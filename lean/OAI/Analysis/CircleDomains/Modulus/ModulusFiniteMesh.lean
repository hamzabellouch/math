import OAI.Analysis.CircleDomains.Modulus.ModulusFiniteBallCut
import OAI.Analysis.CircleDomains.Topology.FiniteMeshCompactIntersection

namespace OAI

/-! Recursive finite ball cuts preserve the strict modulus threshold while
constructing a closed finite-mesh presentation with compact intersection. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_modulus_finite_mesh
    {X Z : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ] (K : X → FiniteMeasure Z)
    {A : Set X} (hA : IsClosed A) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ (fun x => K x.val)) :
    ∃ (C : ℕ → Set X) (F : ℕ → Finset X), C 0 = A ∧ (∀ n, IsClosed (C n)) ∧
      Antitone C ∧
      (∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1))) ∧
      ∀ n, c < measureFamilyModulus (C n) Z σ (fun x => K x.val) := by
  classical
  let Q := {C : Set X // IsClosed C ∧ c < measureFamilyModulus C Z σ (fun x => K x.val)}
  let cut (n : ℕ) (C : Q) : ℕ := Classical.choose
    (exists_modulus_finite_closedBall_cut σ K C.property.2 (r := 1/((n:ℝ)+1)) (by positivity))
  let U (n k : ℕ) : Set X :=
    ⋃ j ∈ (↑(Finset.range (k+1)) : Set ℕ), closedBall (denseSeq X j) (1/((n:ℝ)+1))
  have hU (n k : ℕ) : IsClosed (U n k) :=
    (Finset.range (k+1)).finite_toSet.isClosed_biUnion (fun j _ => isClosed_closedBall)
  let step (n : ℕ) (C : Q) : Q := ⟨C.val ∩ U n (cut n C),C.property.1.inter (hU n _),
    Classical.choose_spec
      (exists_modulus_finite_closedBall_cut σ K C.property.2 (r := 1/((n:ℝ)+1)) (by positivity))⟩
  let p : ℕ → Q := Nat.rec ⟨A,hA,hc⟩ step
  let C (n : ℕ) : Set X := (p n).val
  let F (n : ℕ) : Finset X := (Finset.range (cut n (p n)+1)).image (denseSeq X)
  have hs (n : ℕ) : C (n+1) = C n ∩ U n (cut n (p n)) := rfl
  refine ⟨C,F,rfl,fun n => (p n).property.1,?_,?_,fun n => (p n).property.2⟩
  · exact antitone_nat_of_succ_le (fun n => hs n ▸ inter_subset_left)
  · intro n x hx
    rw [hs n] at hx
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx.2
    apply mem_iUnion₂.mpr
    refine ⟨denseSeq X j,?_,hxj⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)

end CircleDomainRigidity

end

end OAI
