import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CountMoments
import OAI.Analysis.CoulombRadii.Packets.AtomicMesh
import OAI.Analysis.CoulombRadii.Screening.ScreenUnits

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCount_cover {n : ℕ} {C : Type*} [Fintype C] {B : Set Space} (A : C → Set Space)
    (hc : B ⊆ ⋃ c, A c) (x : Configuration n) : localCount B x ≤ ∑ c, localCount (A c) x := by
  unfold localCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈B
  · obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hc hx)
    rw [indicator_of_mem hx]
    calc
      1=(A c).indicator (fun _ => (1:ℝ)) (position x i) := by rw [indicator_of_mem hc]
      _ ≤ _ := Finset.single_le_sum (fun d _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ c)
  · rw [indicator_of_notMem hx]
    exact Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

lemma expectedPopulation_cover {n : ℕ} (ψ : H1Vector n) {C : Type*} [Fintype C]
    {B : Set Space} (hB : MeasurableSet B) (A : C → Set Space) (hA : ∀ c, MeasurableSet (A c))
    (hc : B ⊆ ⋃ c, A c) : expectedPopulation ψ B ≤ ∑ c, expectedPopulation ψ (A c) := by
  rw [expectedPopulation_eq ψ hB]
  simp_rw [expectedPopulation_eq ψ (hA _)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_finsetSum _ (fun c _ => by simpa using localCount_weight_integrable ψ (hA c) s 1)]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (localCount_nonneg _ _) (sq_nonneg _))
  · exact integrable_finsetSum _ (fun c _ => by simpa using localCount_weight_integrable ψ (hA c) s 1)
  · exact Eventually.of_forall (fun x => by
      dsimp only
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (localCount_cover A hc x) (sq_nonneg _))

def screenCountRatio {n : ℕ} (ψ : H1Vector n) (δ : ℝ) (y : Space) : ℝ :=
  if y=0 then 0 else localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y))/(screenMass δ (atomicCellScale y))^2

def screenCountParameter {n : ℕ} (ψ : H1Vector n) (δ : ℝ) : ℝ :=
  max 1 (sSup (Set.range (screenCountRatio ψ δ)))

lemma screenCountRatio_nonneg {n : ℕ} (ψ : H1Vector n) (δ : ℝ) (y : Space) :
    0 ≤ screenCountRatio ψ δ y := by
  unfold screenCountRatio
  split_ifs
  · exact le_rfl
  · exact div_nonneg (localCountSecondMoment_nonneg _ _) (sq_nonneg _)

lemma screenCountRatio_le {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ) (y : Space) :
    screenCountRatio ψ δ y ≤ (n:ℝ)^2 := by
  unfold screenCountRatio
  split_ifs
  · positivity
  · rw [div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))]
    have H := localCountSecondMoment_le ψ (Metric.closedBall y (atomicCellScale y))
    rw [hm,mul_one] at H
    exact H.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith [screenMass_ge_one δ (atomicCellScale y)]))

lemma screenCountParameter_ge_one {n : ℕ} (ψ : H1Vector n) (δ : ℝ) :
    1 ≤ screenCountParameter ψ δ := le_max_left _ _

lemma screenCountParameter_le {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ) :
    screenCountParameter ψ δ ≤ max 1 ((n:ℝ)^2) := by
  unfold screenCountParameter
  apply max_le (le_max_left _ _)
  exact (csSup_le (Set.range_nonempty _) (fun _ ⟨y,hy⟩ => hy ▸ screenCountRatio_le ψ hm δ y)).trans (le_max_right _ _)

lemma screenCountParameter_controls {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) (δ : ℝ)
    {y : Space} (hy : y≠0) :
    localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y)) ≤
      screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 := by
  have hb : BddAbove (Set.range (screenCountRatio ψ δ)) :=
    ⟨(n:ℝ)^2,fun _ ⟨z,hz⟩ => hz ▸ screenCountRatio_le ψ hm δ z⟩
  have H := (le_csSup hb (Set.mem_range_self y)).trans (le_max_right 1 (sSup (Set.range (screenCountRatio ψ δ))))
  change screenCountRatio ψ δ y ≤ screenCountParameter ψ δ at H
  simpa only [screenCountRatio,ite_eq_right hy,div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))] using H

lemma screenCountParameter_le_of {n : ℕ} (ψ : H1Vector n) (δ : ℝ) {P : ℝ} (hP : 1 ≤ P)
    (hc : ∀ y : Space, y≠0 → localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y)) ≤
      P*(screenMass δ (atomicCellScale y))^2) : screenCountParameter ψ δ ≤ P := by
  apply max_le hP
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y,rfl⟩
  unfold screenCountRatio
  split_ifs with hy
  · linarith
  · exact (div_le_iff₀ (sq_pos_of_pos (screenMass_pos δ _))).mpr (hc y hy)

lemma atomicPatch_population {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) {y : Space} (hy : y≠0) :
    expectedPopulation ψ (Metric.closedBall y (80*atomicCellScale y)) ≤
      (Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8*Real.sqrt P*screenMass δ (atomicCellScale y) := by
  let A := fun z : {z : Space // z∈atomicPatchMesh} =>
    Metric.closedBall (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val))
  have hcover : Metric.closedBall y (80*atomicCellScale y) ⊆ ⋃ z, A z := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := atomicMesh_cover hy x (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,by simpa only [A,Metric.mem_closedBall,dist_eq_norm] using hzx⟩
  have HB := expectedPopulation_cover ψ measurableSet_closedBall A (fun _ => measurableSet_closedBall) hcover
  have HE (z : {z : Space // z∈atomicPatchMesh}) : expectedPopulation ψ (A z) ≤
      8*Real.sqrt P*screenMass δ (atomicCellScale y) := by
    have hz : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy
      (by nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
    have hs := expectedPopulation_sq_le ψ (A:=A z) measurableSet_closedBall hm
    have HC := hc (atomicMeshCenter y z.val) hz
    have hu := atomicMeshCenter_comparable y z.val z.property
    have Hm := screenMass_comparable hδ (atomicCellScale_pos hy) (show (1:ℝ) ≤ 2 by norm_num) hu.1 (by linarith [hu.2])
    norm_num at Hm
    have hsq : (expectedPopulation ψ (A z))^2 ≤ (Real.sqrt P*screenMass δ (atomicCellScale (atomicMeshCenter y z.val)))^2 := by
      rw [mul_pow,Real.sq_sqrt hP]
      exact hs.trans HC
    have hp : expectedPopulation ψ (A z) ≤ Real.sqrt P*screenMass δ (atomicCellScale (atomicMeshCenter y z.val)) :=
      (sq_le_sq₀ (show 0 ≤ expectedPopulation ψ (A z) from Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))))) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)).mp hsq
    exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left Hm (Real.sqrt_nonneg P)])
  calc
    _ ≤ ∑ z, expectedPopulation ψ (A z) := HB
    _ ≤ ∑ _z : {z : Space // z∈atomicPatchMesh}, 8*Real.sqrt P*screenMass δ (atomicCellScale y) :=
      Finset.sum_le_sum (fun z _ => HE z)
    _ = _ := by simp; ring

end Coulomb
end

end
end

end OAI
