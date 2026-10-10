import OAI.Analysis.CircleDomains.Topology.CompactPairChainRule
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! The joint chain rule on the actual open source domain. All temporary
global extensions are cut off strictly inside that domain, so no
extension across the removed set is assumed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_pair_weak_chain {U : Set EuclideanPlane} (hU : IsOpen U)
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
        fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
      (fun x => Φ (planePair (u x) (v x))) U := by
  intro φ hφ hs hsub
  obtain ⟨η, Z, hη, hsη, _, hηU, hZ, hKZ, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs hU hsub
  have hZU : Z ⊆ U := by
    intro x hx
    exact hηU (subset_tsupport η (by change η x ≠ 0; rw [hone x hx]; exact one_ne_zero))
  let a := fun x => η x*u x
  let b := fun x => η x*v x
  obtain ⟨Wa⟩ := exists_global_compact_cutoff_witness hU Wu.memW1p hη hsη hηU
  obtain ⟨Wb⟩ := exists_global_compact_cutoff_witness hU Wv.memW1p hη hsη hηU
  have ha : EqOn a u Z := fun x hx => by dsimp [a]; rw [hone x hx, one_mul]
  have hb : EqOn b v Z := fun x hx => by dsimp [b]; rw [hone x hx, one_mul]
  have hGa := (ae_restrict_iff' hZ.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hZ hZU Wu Wa hone i)
  have hGb := (ae_restrict_iff' hZ.measurableSet).mp (weakGrad_eq_on_cutoff_plateau hZ hZU Wv Wb hone i)
  have hdz (x : EuclideanPlane) (hx : x ∉ Z) : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun ht => hx (hKZ (tsupport_fderiv_apply_subset ℝ _ ht)))
  have hφz (x : EuclideanPlane) (hx : x ∉ Z) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hKZ ht))
  have hchain := compact_pair_weak_chain (hη.continuous.mul hu) (hη.continuous.mul hv)
    hsη.mul_right hsη.mul_right Wa Wb hΦ hB hC hΦb hΦd i φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hchain
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hdz x (fun hz => hx (hZU hz)), mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hφz x (fun hz => hx (hZU hz)), mul_zero])]
  calc
    _ = ∫ x, Φ (planePair (a x) (b x))*fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Z
        · simp only [a, b, hone x hx, one_mul]
        · simp only [hdz x hx, mul_zero]
    _ = _ := hchain
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hGa, hGb] with x hax hbx
      by_cases hx : x ∈ Z
      · simp only [Pi.mul_apply, hone x hx, one_mul, hax hx, hbx hx]
      · simp only [hφz x hx, mul_zero]

end CircleDomainRigidity

end

end OAI
