import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingSum
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! # Continuity of smooth families with a common compact support

The support is fixed only after rescaling the physical cutoff.  No decay or
symbol hypothesis on the smooth coefficient is needed for this local result.
-/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- Spatial derivatives of a jointly smooth family vary jointly continuously. -/
theorem continuous_spatial_iteratedFDeriv (F : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    Continuous (fun p : ℝ × E => iteratedFDeriv ℝ n (fun x => F (p.1, x)) p.2) := by
  let J : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E
  have he (t : ℝ) (x : E) :
      iteratedFDeriv ℝ n (fun y => F (t, y)) x =
        (iteratedFDeriv ℝ n F (t, x)).compContinuousLinearMap (fun _ => J) := by
    have h := J.iteratedFDeriv_comp_right
      (hF.comp (contDiff_const.add contDiff_id) :
        ContDiff ℝ ∞ (fun z : ℝ × E => F ((t, 0) + z))) x (by simp : (n : ℕ∞ω) ≤ ∞)
    simpa only [J, Function.comp_def, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add,
      iteratedFDeriv_comp_add_left] using h
  simp_rw [he]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin n => J)).continuous.comp (hF.continuous_iteratedFDeriv (by simp))

/-- Jointly continuous spatial jets and a fixed compact support give Schwartz continuity. -/
theorem continuous_schwartz_of_common_compact_support
    {P : Type*} [UniformSpace P] [WeaklyLocallyCompactSpace P]
    (f : P → 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K)
    (hs : ∀ t, tsupport (f t : E → ℂ) ⊆ K)
    (hj : ∀ n : ℕ, Continuous
      (fun p : P × E => iteratedFDeriv ℝ n (f p.1) p.2)) : Continuous f := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let B : ℝ := max R 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  rw [continuous_iff_continuousAt]
  intro t
  apply ((schwartz_withSeminorms ℝ E ℂ).tendsto_nhds f (f t)).mpr
  rintro ⟨i, n⟩ ε hε
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu : TendstoUniformly
      (fun s : P => fun x : K => iteratedFDeriv ℝ n (f s) x)
      (fun x : K => iteratedFDeriv ℝ n (f t) x) (𝓝 t) :=
    Continuous.tendstoUniformly _
      ((hj n).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) t
  have hd := (Metric.tendstoUniformly_iff.mp hu)
    (ε / (2 * B ^ i)) (by positivity)
  filter_upwards [hd] with s hst
  have hb : SchwartzMap.seminorm ℝ i n (f s - f t) ≤ ε / 2 := by
    apply SchwartzMap.seminorm_le_bound ℝ i n _ (by positivity)
    intro x
    by_cases hx : x ∈ K
    · have hdx : ‖iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x‖ <
          ε / (2 * B ^ i) := by
        simpa only [dist_eq_norm, norm_sub_rev] using hst ⟨x, hx⟩
      have hxB : ‖x‖ ≤ B := (hR x hx).trans (le_max_left _ _)
      have hdif : iteratedFDeriv ℝ n (f s - f t) x =
          iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x :=
        iteratedFDeriv_sub_apply ((f s).smooth'.contDiffAt.of_le (by simp))
          ((f t).smooth'.contDiffAt.of_le (by simp))
      rw [hdif]
      calc
        _ ≤ B ^ i * ‖iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hxB i) (norm_nonneg _)
        _ ≤ B ^ i * (ε / (2 * B ^ i)) :=
          mul_le_mul_of_nonneg_left hdx.le (by positivity)
        _ = ε / 2 := by field_simp
    · have hzero (u : P) : iteratedFDeriv ℝ n (f u) x = 0 := by
        by_contra hn
        exact hx (hs u (support_iteratedFDeriv_subset n hn))
      have hdif : iteratedFDeriv ℝ n (f s - f t) x =
          iteratedFDeriv ℝ n (f s) x - iteratedFDeriv ℝ n (f t) x :=
        iteratedFDeriv_sub_apply ((f s).smooth'.contDiffAt.of_le (by simp))
          ((f t).smooth'.contDiffAt.of_le (by simp))
      rw [hdif, hzero s, hzero t, sub_self, norm_zero, mul_zero]
      positivity
  exact hb.trans_lt (by linarith)

/-- Multiplication of a jointly smooth family by a fixed compact cutoff. -/
noncomputable def compactSmoothFamily (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (F : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) : 𝓢(E, ℂ) :=
  (hκ.mul_right (f' := fun x => F (t, x))).toSchwartzMap
    (κ.smooth'.mul (hF.comp (contDiff_const.prodMk contDiff_id)))

@[simp] theorem compactSmoothFamily_apply (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (F : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : E) :
    compactSmoothFamily κ hκ F hF t x = κ x * F (t, x) := rfl

theorem continuous_compactSmoothFamily (κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (F : ℝ × E → ℂ)
    (hF : ContDiff ℝ ∞ F) : Continuous (compactSmoothFamily κ hκ F hF) := by
  apply continuous_schwartz_of_common_compact_support _ (tsupport (κ : E → ℂ)) hκ
  · intro t
    exact tsupport_mul_subset_left
  · intro n
    exact continuous_spatial_iteratedFDeriv (fun p => κ p.2 * F p)
      ((κ.smooth'.comp contDiff_snd).mul hF) n

end DefocusingNLS

end OAI
