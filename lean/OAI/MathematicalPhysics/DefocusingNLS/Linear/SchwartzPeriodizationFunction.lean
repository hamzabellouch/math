import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDerivatives
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace OAI

/-! # Actual continuous periodization in twelve dimensions

Schwartz decay gives local normal convergence of lattice translates.  The
resulting function descends to the genuine product torus.
-/

open Set Filter Topology TopologicalSpace
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def frequencyCoordinatesEquiv : frequencyLattice ≃ₗ[ℤ] (Fin 12 → ℤ) :=
  ((EuclideanSpace.basisFun (Fin 12) ℝ).toBasis.restrictScalars ℤ).repr.trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 12))

theorem frequencyCoordinatesEquiv_apply (n : frequencyLattice) :
    frequencyCoordinatesEquiv n = frequencyCoordinates n := rfl

private theorem schwartz_periodization_decay (K : 𝓢(E, ℂ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M := by
  let M := 2 ^ (14 : ℕ) *
    (Finset.Iic (14, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) K
  refine ⟨max M 1, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (14, 0)) (k := 14) (n := 0) (by decide) (by decide) K x
  have h' : (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using h
  exact h'.trans (le_max_left _ _)

private theorem schwartz_periodization_translate_bound (K : 𝓢(E, ℂ)) (M R : ℝ)
    (hM : ∀ x : E, (1 + ‖x‖) ^ 14 * ‖K x‖ ≤ M) (hR : 0 ≤ R)
    (x : E) (hx : ‖x‖ ≤ R) (n : frequencyLattice) :
    ‖K (x + n)‖ ≤ ((1 + R) ^ 14 * M) * ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹ := by
  have hn : ‖n‖ ≤ ‖x + (n : E)‖ + ‖x‖ := by
    have h := norm_sub_le (x + (n : E)) x
    simpa only [add_sub_cancel_left, Submodule.norm_coe] using h
  have hlin : 1 + ‖n‖ ≤ (1 + R) * (1 + ‖x + (n : E)‖) := by
    nlinarith [norm_nonneg (x + (n : E))]
  have hsquare : 1 + ‖n‖ ^ 2 ≤ (1 + ‖n‖) ^ 2 := by
    nlinarith [norm_nonneg n]
  have hp : (1 + ‖n‖ ^ 2) ^ (7 : ℕ) ≤
      (1 + R) ^ (14 : ℕ) * (1 + ‖x + (n : E)‖) ^ (14 : ℕ) := by
    calc
      _ ≤ ((1 + ‖n‖) ^ 2) ^ (7 : ℕ) := by gcongr
      _ = (1 + ‖n‖) ^ (14 : ℕ) := by ring
      _ ≤ ((1 + R) * (1 + ‖x + (n : E)‖)) ^ (14 : ℕ) := by gcongr
      _ = _ := by rw [mul_pow]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖n‖ ^ 2) ^ (7 : ℕ))).mpr
  calc
    _ = (1 + ‖n‖ ^ 2) ^ (7 : ℕ) * ‖K (x + n)‖ := mul_comm _ _
    _ ≤ ((1 + R) ^ (14 : ℕ) * (1 + ‖x + (n : E)‖) ^ (14 : ℕ)) *
        ‖K (x + n)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = (1 + R) ^ (14 : ℕ) * ((1 + ‖x + (n : E)‖) ^ (14 : ℕ) *
        ‖K (x + n)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM _) (by positivity)

noncomputable def schwartzLatticeTranslate (K : 𝓢(E, ℂ)) (n : frequencyLattice) : C(E, ℂ) :=
  K.toContinuousMap.comp (ContinuousMap.addRight (n : E))

theorem summable_schwartzLatticeTranslate_restrict (K : 𝓢(E, ℂ)) (S : Compacts E) :
    Summable (fun n : frequencyLattice => ‖(schwartzLatticeTranslate K n).restrict S‖) := by
  obtain ⟨M, hM, hdecay⟩ := schwartz_periodization_decay K
  obtain ⟨r, hr⟩ := S.isCompact.isBounded.subset_closedBall (0 : E)
  let R := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs : Summable (fun n : frequencyLattice => ((1 + ‖n‖ ^ 2) ^ (7 : ℕ))⁻¹) := by
    have h := summable_sobolev_variances 0 7 (by norm_num)
    convert h using 1
    ext n
    norm_num [Real.rpow_neg]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left ((1 + R) ^ (14 : ℕ) * M))
  intro n
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply schwartz_periodization_translate_bound K M R hdecay hR x.1
  have hx := hr x.2
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact hx.trans (le_max_left _ _)

theorem summable_schwartzLatticeTranslate (K : 𝓢(E, ℂ)) :
    Summable (schwartzLatticeTranslate K) :=
  ContinuousMap.summable_of_locally_summable_norm (summable_schwartzLatticeTranslate_restrict K)

theorem summable_norm_schwartz_lattice (K : 𝓢(E, ℂ)) (x : E) :
    Summable (fun n : frequencyLattice => ‖K (x + n)‖) := by
  let S : Compacts E := ⟨{x}, isCompact_singleton⟩
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (summable_schwartzLatticeTranslate_restrict K S)
  intro n
  exact ((schwartzLatticeTranslate K n).restrict S).norm_coe_le_norm ⟨x, rfl⟩

noncomputable def schwartzPeriodization (K : 𝓢(E, ℂ)) : C(E, ℂ) :=
  ∑' n, schwartzLatticeTranslate K n

theorem schwartzPeriodization_apply (K : 𝓢(E, ℂ)) (x : E) :
    schwartzPeriodization K x = ∑' n : frequencyLattice, K (x + n) := by
  exact (ContinuousMap.tsum_apply (summable_schwartzLatticeTranslate K) x).symm

theorem schwartzPeriodization_add_lattice (K : 𝓢(E, ℂ)) (x : E) (n : frequencyLattice) :
    schwartzPeriodization K (x + n) = schwartzPeriodization K x := by
  simp only [schwartzPeriodization_apply]
  calc
    _ = ∑' m : frequencyLattice, K (x + ((m + n : frequencyLattice) : E)) := by
      apply tsum_congr
      intro m
      congr 1
      simp only [Submodule.coe_add]
      abel
    _ = _ := (Equiv.addRight n).tsum_eq (fun m : frequencyLattice => K (x + m))

noncomputable def unitTorusProjection (x : E) : UnitAddTorus (Fin 12) :=
  fun j => (x j : UnitAddCircle)

theorem unitTorusProjection_isOpenQuotientMap : IsOpenQuotientMap unitTorusProjection := by
  exact (IsOpenQuotientMap.piMap fun _ : Fin 12 =>
    (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)))).comp
    (PiLp.homeomorph 2 (fun _ : Fin 12 => ℝ)).isOpenQuotientMap

theorem schwartzPeriodization_eq_of_projection_eq (K : 𝓢(E, ℂ)) {x y : E}
    (h : unitTorusProjection x = unitTorusProjection y) :
    schwartzPeriodization K x = schwartzPeriodization K y := by
  have hj (j : Fin 12) : ((x j - y j : ℝ) : UnitAddCircle) = 0 := by
    have hc := congrFun h j
    change (x j : UnitAddCircle) = (y j : UnitAddCircle) at hc
    rw [AddCircle.coe_sub, hc, sub_self]
  have hz (j : Fin 12) : ∃ n : ℤ, (n : ℝ) = x j - y j := by
    simpa only [zsmul_eq_mul, mul_one] using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hj j))
  choose z hz using hz
  let n := frequencyCoordinatesEquiv.symm z
  have hn (j : Fin 12) : ((n : frequencyLattice) : E) j = (z j : ℝ) := by
    rw [← frequencyCoordinates_coe]
    change (frequencyCoordinatesEquiv n j : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
  have hxy : x = y + (n : E) := by
    ext j
    change x j = y j + (n : E) j
    rw [hn, hz]
    ring
  rw [hxy, schwartzPeriodization_add_lattice]

noncomputable def schwartzPeriodizedTorus (K : 𝓢(E, ℂ)) : C(UnitAddTorus (Fin 12), ℂ) where
  toFun x := schwartzPeriodization K
    (Function.surjInv unitTorusProjection_isOpenQuotientMap.surjective x)
  continuous_toFun := by
    apply unitTorusProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
    have he : (fun x : E => schwartzPeriodization K
        (Function.surjInv unitTorusProjection_isOpenQuotientMap.surjective
          (unitTorusProjection x))) = schwartzPeriodization K := by
      funext x
      apply schwartzPeriodization_eq_of_projection_eq
      exact Function.rightInverse_surjInv unitTorusProjection_isOpenQuotientMap.surjective _
    simpa only [Function.comp_def, he] using (schwartzPeriodization K).continuous

theorem schwartzPeriodizedTorus_projection (K : 𝓢(E, ℂ)) (x : E) :
    schwartzPeriodizedTorus K (unitTorusProjection x) = schwartzPeriodization K x := by
  apply schwartzPeriodization_eq_of_projection_eq
  exact Function.rightInverse_surjInv unitTorusProjection_isOpenQuotientMap.surjective _

end DefocusingNLS

end OAI
