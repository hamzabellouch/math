import OAI.Analysis.CircleDomains.Sobolev.BoundedSobolevChain
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! The bounded scalar chain rule on an open planar set. Compact tests
are enclosed in a cutoff plateau, so no boundary regularity is needed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem bounded_sobolev_chain_rule_on_symmetric
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x ∈ U, u x ∈ Icc (-B) B) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) U := by
  intro φ hφ hs hsub
  obtain ⟨η, V, hη, hsη, hηunit, hηsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs hU hsub
  have hVU : V ⊆ U := by
    intro x hx
    apply hηsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let v : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hv⟩ := exists_global_compact_cutoff_witness hU hw.memW1p hη hsη hηsub
  have hvunit : ∀ x, v x ∈ Icc (-B) B := by
    intro x
    apply abs_le.mp
    by_cases hx : x ∈ U
    · have hux : |u x| ≤ B := abs_le.mpr (hu x hx)
      change |η x * u x| ≤ B
      rw [abs_mul, abs_of_nonneg (hηunit x).1]
      exact (mul_le_mul (hηunit x).2 hux (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηsub h))
      change |η x * u x| ≤ B
      simpa only [hz, zero_mul, abs_zero] using hB
  have heq : EqOn v u V := fun x hx => by dsimp [v]; rw [hone x hx, one_mul]
  have hg := weakGrad_eq_on_cutoff_plateau hV hVU hw hv hone i
  have hg' : ∀ᵐ x ∂volume, x ∈ V → hv.weakGrad x i = hw.weakGrad x i := by
    change ∀ᵐ x ∂volume.restrict V, hv.weakGrad x i = hw.weakGrad x i at hg
    exact (ae_restrict_iff' hV.measurableSet).mp hg
  have hc := bounded_sobolev_chain_rule_Icc hv hsη.mul_right hvunit hF i φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hc
  have hderiv (x : EuclideanPlane) (hx : x ∉ V) :
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    have hn : x ∉ tsupport (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) :=
      fun h => hx (hKV ((tsupport_fderiv_apply_subset ℝ _) h))
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) hn
  have hφzero (x : EuclideanPlane) (hx : x ∉ V) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hKV h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hderiv x (fun h => hx (hVU h)), mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero])]
  calc
    _ = ∫ x, (F ∘ v) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [comp_apply]
        by_cases hx : x ∈ V
        · rw [heq hx]
        · rw [hderiv x hx, mul_zero, mul_zero]
    _ = -(∫ x, (deriv F (v x) * hv.weakGrad x i) * φ x) := hc
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg'] with x hx
      by_cases hxV : x ∈ V
      · rw [heq hxV, hx hxV]
      · rw [hφzero x hxV, mul_zero, mul_zero]

 theorem bounded_sobolev_chain_rule_on
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u U)
    (hu : ∀ x ∈ U, u x ∈ Icc 0 1) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) U :=
  bounded_sobolev_chain_rule_on_symmetric hU hw (by norm_num : (0 : ℝ) ≤ 1)
    (fun x hx => ⟨by linarith [(hu x hx).1], (hu x hx).2⟩) hF i

end CircleDomainRigidity

end

end OAI
