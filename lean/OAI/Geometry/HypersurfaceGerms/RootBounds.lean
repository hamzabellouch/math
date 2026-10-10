import Mathlib

namespace OAI

/-! Compact quartic estimates and confinement of prepared roots. -/

namespace AmbientMultiplicity.InnerQuartic
noncomputable section
open Filter Topology

variable {G : Type*} [UniformSpace G]

 
def rescaledQuartic (A : G → Fin 4 → ℂ) (s : ℝ) (p : G) (w : ℂ) : ℂ :=
  w^4 + ∑ j : Fin 4, (s : ℂ)^(4-(j : ℕ)) * A p j * w^(j : ℕ)

omit [UniformSpace G] in
lemma rescaledQuartic_zero (A : G → Fin 4 → ℂ) (p : G) (w : ℂ) :
    rescaledQuartic A 0 p w = w^4 := by
  rw [rescaledQuartic]
  have h : (∑ j : Fin 4, (0 : ℂ)^(4-(j : ℕ)) * A p j * w^(j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero_pow (by omega : 4-(j : ℕ) ≠ 0), zero_mul, zero_mul]
  simp only [Complex.ofReal_zero, h, add_zero]

lemma continuous_rescaledQuartic (A : G → Fin 4 → ℂ) (hA : Continuous A) :
    Continuous (fun q : ℝ × (G × ℂ) => rescaledQuartic A q.1 q.2.1 q.2.2) := by
  unfold rescaledQuartic
  fun_prop

 

lemma eventually_quartic_norm_le [CompactSpace G] (A : G → Fin 4 → ℂ)
    (hA : Continuous A) (radius : ℝ) (hradius : 0 < radius) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ p : G, ∀ w : ℂ, ‖w‖ ≤ radius →
      ‖rescaledQuartic A s p w‖ ≤ 2*radius^4 := by
  let K := G × ↑(Metric.closedBall (0 : ℂ) radius)
  let f : ℝ → K → ℂ := fun s p => rescaledQuartic A s p.1 p.2.val
  have hk : Continuous (fun q : ℝ × K => (q.1, (q.2.1, q.2.2.val))) :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_snd.snd.subtype_val)
  have hcomp := (continuous_rescaledQuartic A hA).comp hk
  have hc : Continuous (Function.uncurry f) := hcomp
  have hu := Continuous.tendstoUniformly f hc 0
  have hε : 0 < radius^4 := pow_pos hradius 4
  have he := (Metric.tendstoUniformly_iff.mp hu) (radius^4) hε
  filter_upwards [he] with s hs p w hw
  have hw' : w ∈ Metric.closedBall (0 : ℂ) radius := by simpa [dist_eq_norm] using hw
  have hh := hs (p, ⟨w, hw'⟩)
  dsimp [f] at hh
  rw [rescaledQuartic_zero] at hh
  have hp : ‖w^4‖ ≤ radius^4 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 4
  calc
    ‖rescaledQuartic A s p w‖ ≤ ‖rescaledQuartic A s p w - w^4‖ + ‖w^4‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ radius^4 + radius^4 := by
      exact add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hh.le) hp
    _ = 2*radius^4 := by ring

lemma sqrt_quartic_bound {radius M r : ℝ} (hradius : 0 ≤ radius) (hM : 3 < M)
    (hr : 0 ≤ r) (hb : r ≤ 2*radius^4) :
    Real.sqrt r ≤ M*radius^2 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by linarith) (pow_nonneg hradius 2), ?_⟩
  have hh : 2*radius^4 ≤ (M*radius^2)^2 := by
    nlinarith [sq_nonneg radius, sq_nonneg (M-2)]
  exact hb.trans hh

end
end AmbientMultiplicity.InnerQuartic

 

namespace AmbientMultiplicity.RootConfinement
open Filter Topology

lemma quartic_root_bound (A : Fin 4 → ℂ) {r : ℝ} (hr : 0 < r)
    (hA : ∀ j : Fin 4, ‖A j‖ ≤ r^(4-(j:ℕ))/8) {w : ℂ}
    (hw : w^4 + ∑ j : Fin 4, A j*w^(j:ℕ) = 0) : ‖w‖ < r := by
  by_contra! hwr
  have hp : 0 < ‖w‖ := hr.trans_le hwr
  have hn : ‖w‖^4 ≤ ∑ j : Fin 4, ‖A j*w^(j:ℕ)‖ := by
    have he : w^4 = -(∑ j : Fin 4, A j*w^(j:ℕ)) := eq_neg_of_add_eq_zero_left hw
    calc
      ‖w‖^4 = ‖w^4‖ := by rw [norm_pow]
      _ = ‖∑ j : Fin 4, A j*w^(j:ℕ)‖ := by rw [he, norm_neg]
      _ ≤ _ := norm_sum_le _ _
  have hb : ∀ j : Fin 4, ‖A j*w^(j:ℕ)‖ ≤ ‖w‖^4/8 := by
    intro j
    rw [norm_mul, norm_pow]
    calc
      ‖A j‖*‖w‖^(j:ℕ) ≤ (r^(4-(j:ℕ))/8)*‖w‖^(j:ℕ) :=
        mul_le_mul_of_nonneg_right (hA j) (by positivity)
      _ ≤ (‖w‖^(4-(j:ℕ))/8)*‖w‖^(j:ℕ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr.le hwr _) (by norm_num)
      _ = ‖w‖^4/8 := by
        rw [div_mul_eq_mul_div, ← pow_add, Nat.sub_add_cancel (by omega : (j:ℕ) ≤ 4)]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have h4 : 0 < ‖w‖^4 := by positivity
  linarith

lemma eventually_all_roots_small {B : Type*} [TopologicalSpace B]
    {p₀ : B} (A : B → Fin 4 → ℂ) (hA : ContinuousAt A p₀)
    (hzero : A p₀ = 0) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ p in 𝓝 p₀, ∀ w : ℂ,
      w^4 + ∑ j : Fin 4, A p j*w^(j:ℕ) = 0 → ‖w‖ < r := by
  have hj : ∀ j : Fin 4, ∀ᶠ p in 𝓝 p₀, ‖A p j‖ ≤ r^(4-(j:ℕ))/8 := by
    intro j
    have hc := (continuous_apply j).continuousAt.comp hA
    have hz : A p₀ j = 0 := by rw [hzero]; rfl
    have hε : 0 < r^(4-(j:ℕ))/8 := by positivity
    have hh := hc.norm.eventually (gt_mem_nhds (show ‖A p₀ j‖ < r^(4-(j:ℕ))/8 by simpa [hz] using hε))
    filter_upwards [hh] with p hp
    exact hp.le
  have hall : ∀ᶠ p in 𝓝 p₀, ∀ j : Fin 4, ‖A p j‖ ≤ r^(4-(j:ℕ))/8 :=
    Filter.eventually_all.mpr hj
  filter_upwards [hall] with p hp w hw
  exact quartic_root_bound _ hr hp hw

end AmbientMultiplicity.RootConfinement

end OAI
