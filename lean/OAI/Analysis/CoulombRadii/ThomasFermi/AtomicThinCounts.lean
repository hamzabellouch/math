import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ThinEnsemble
import OAI.Analysis.CoulombRadii.Localization.ShellChoice

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def atomicPatchCountFactor : ℝ := (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)^2*64
lemma atomicPatchCountFactor_nonneg : 0≤atomicPatchCountFactor := by unfold atomicPatchCountFactor; positivity

lemma atomicPatch_secondMoment {n : ℕ} (ψ : H1Vector n)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    localCountSecondMoment ψ (Metric.closedBall y (80*atomicCellScale y))≤
      atomicPatchCountFactor*P*(screenMass δ (atomicCellScale y))^2 := by
  let A := fun z : {z : Space // z∈atomicPatchMesh} =>
    Metric.closedBall (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val))
  have hcover : Metric.closedBall y (80*atomicCellScale y) ⊆ ⋃ z, A z := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := atomicMesh_cover hy x (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,by simpa only [A,Metric.mem_closedBall,dist_eq_norm] using hzx⟩
  have HE (z : {z : Space // z∈atomicPatchMesh}) : localCountSecondMoment ψ (A z)≤
      64*P*(screenMass δ (atomicCellScale y))^2 := by
    have hz : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy
      (by nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
    have hu := atomicMeshCenter_comparable y z.val z.property
    have Hm := screenMass_comparable hδ (atomicCellScale_pos hy) (show (1:ℝ)≤2 by norm_num) hu.1 (by linarith [hu.2])
    norm_num at Hm
    apply (hc _ hz).trans
    have HS := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos δ _).le Hm 2) hP
    nlinarith
  calc
    _≤(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*∑ z, localCountSecondMoment ψ (A z) :=
      localCountSecondMoment_cover ψ A (fun _ => measurableSet_closedBall) hcover
    _≤(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*∑ _ : {z : Space // z∈atomicPatchMesh},
        64*P*(screenMass δ (atomicCellScale y))^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => HE z)) (Nat.cast_nonneg _)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,atomicPatchCountFactor]; ring

lemma exists_atomic_deletedShell {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ : ℝ} (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
      localCountSecondMoment ψ (deletedShell y t b)≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*screenCountParameter ψ δ*
          (screenMass δ (atomicCellScale y))^2 := by
  obtain ⟨t,ht,H⟩ := exists_deletedShell_small ψ y (atomicCellScale_pos hy) hb hsmall
  refine ⟨t,ht,H.trans ?_⟩
  have HP := atomicPatch_secondMoment ψ hδ (le_trans zero_le_one (screenCountParameter_ge_one ψ δ))
    (fun _ hz => screenCountParameter_controls ψ hm δ hz) hy
  have HM := localCountSecondMoment_mono ψ (A:=Metric.closedBall y (7*atomicCellScale y)) measurableSet_closedBall
    (Metric.closedBall_subset_closedBall (show 7*atomicCellScale y≤80*atomicCellScale y by nlinarith [atomicCellScale_nonneg y]))
  have Hmul := mul_le_mul_of_nonneg_left (HM.trans HP)
    (show 0≤18*b/atomicCellScale y from div_nonneg (by positivity) (atomicCellScale_nonneg y))
  convert Hmul using 1
  ring

def thinReserveFactor : ℝ := max 1 (3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)
lemma thinReserveFactor_ge_one : 1≤ thinReserveFactor := le_max_left _ _
lemma thinReserveFactor_nonneg : 0≤ thinReserveFactor := le_trans zero_le_one thinReserveFactor_ge_one

lemma thinIMS_budget {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 1≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2)
    {y : Space} (hy : y≠0) {t b : ℝ} (hb : 0<b) (hwidth : t+b≤80*atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt P*screenMass δ (atomicCellScale y)) :
    thinIMS ψ y t b≤ thinReserveFactor*P*screenEnergy δ (atomicCellScale y) := by
  have hP0 : 0≤P := le_trans zero_le_one hP
  have ha := atomicCellScale_pos hy
  have hm0 := screenMass_pos δ (atomicCellScale y)
  have H := (expectedPopulation_mono ψ measurableSet_closedBall measurableSet_closedBall
    (Metric.closedBall_subset_closedBall hwidth)).trans (atomicPatch_population ψ hm hδ hP0 hc hy)
  have Hims := mul_le_mul_of_nonneg_left H (show 0≤3*(thinCutCoefficient/b)^2 by positivity)
  have HC : 3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8≤ thinReserveFactor := le_max_right _ _
  have HU : 3*(thinCutCoefficient/b)^2*((Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y))≤
      thinReserveFactor*(Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by
    calc
      _=(3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)*
          (Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by rw [div_pow]; ring
      _≤_ := mul_le_mul_of_nonneg_right HC (by positivity)
  have Hscale : Real.sqrt P*screenMass δ (atomicCellScale y)/b^2≤P*screenEnergy δ (atomicCellScale y) := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    rw [screenEnergy,←mul_div_assoc,div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    have Hc := mul_le_mul_of_nonneg_right hcond (mul_nonneg (Real.sqrt_nonneg P) hm0.le)
    have Hr : (Real.sqrt P*screenMass δ (atomicCellScale y))^2=P*(screenMass δ (atomicCellScale y))^2 := by
      rw [mul_pow,Real.sq_sqrt hP0]
    nlinarith [mul_le_mul_of_nonneg_left Hr.le (sq_nonneg b),
      mul_le_mul_of_nonneg_left Hr.ge (sq_nonneg b)]
  exact Hims.trans (HU.trans (by nlinarith [mul_le_mul_of_nonneg_left Hscale thinReserveFactor_nonneg]))

end Coulomb
end

end
end

end OAI
