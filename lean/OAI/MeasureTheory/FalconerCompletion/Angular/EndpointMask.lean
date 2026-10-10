import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.DescriptorGoodNeg

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace ContDiff Topology
variable {d : ℕ}

noncomputable def actualEndpointMask (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x w : EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact ∑ P ∈ dyadicPaths (descriptorAnchor b),
    if x ∈ treeCell P then actualDescriptorMask ρ m N sig C J i P b w else 0

lemma actualEndpointMask_of_mem (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {P : CellPath d} (hP : P ∈ dyadicPaths (descriptorAnchor b))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ treeCell P) :
    actualEndpointMask ρ m N sig C J i b x=actualDescriptorMask ρ m N sig C J i P b := by
  classical
  funext w
  unfold actualEndpointMask
  rw [Finset.sum_eq_single P]
  · simp only [hx,ite_true]
  · intro Q hQ hQP
    have hnot : x ∉ treeCell Q := fun hxQ =>
      Set.disjoint_left.mp (treeCell_disjoint
        (((mem_dyadicPaths _ _).mp hQ).trans ((mem_dyadicPaths _ _).mp hP).symm) hQP) hxQ hx
    simp only [hnot,ite_false]
  · exact fun h => (h hP).elim

lemma actualEndpointMask_of_absent (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : ∀ P ∈ dyadicPaths (descriptorAnchor b), x ∉ treeCell P) :
    actualEndpointMask ρ m N sig C J i b x=0 := by
  classical
  funext w
  exact Finset.sum_eq_zero (fun P hP => ite_eq_right (hx P hP))

lemma actualEndpointMask_smooth (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ ∞ (actualEndpointMask ρ m N sig C J i b x) := by
  classical
  by_cases hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P
  · obtain ⟨P,hP,hx⟩ := hx
    rw [actualEndpointMask_of_mem ρ m N sig C J i b hP hx]
    exact actualDescriptorMask_smooth _ _ _ _ _ _ _ _ _
  · rw [actualEndpointMask_of_absent ρ m N sig C J i b (by simpa only [not_exists,not_and] using hx)]
    exact contDiff_const

lemma actualEndpointMask_measurable (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      actualEndpointMask ρ m N sig C J i b z.1 z.2) := by
  classical
  unfold actualEndpointMask
  apply Finset.measurable_sum
  intro P hP
  exact Measurable.ite ((measurableSet_treeCell P).preimage measurable_fst)
    ((actualDescriptorMask_smooth ρ m N sig C J i P b).continuous.measurable.comp measurable_snd)
    measurable_const

lemma actualEndpointMask_bounds (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (x : EuclideanSpace ℝ (Fin d)) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖≤1) :
    0≤actualEndpointMask ρ m N sig C J i b x w ∧ actualEndpointMask ρ m N sig C J i b x w ≤ 1 := by
  classical
  by_cases hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P
  · obtain ⟨P,hP,hx⟩ := hx
    rw [actualEndpointMask_of_mem ρ m N sig C J i b hP hx]
    exact actualDescriptorMask_bounds _ _ _ _ _ _ _ _ _ hw
  · rw [actualEndpointMask_of_absent ρ m N sig C J i b (by simpa only [not_exists,not_and] using hx)]
    simp

lemma actualEndpointMask_one (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {x w : EuclideanSpace ℝ (Fin d)}
    (hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P)
    (hg : (x,w) ∈ endpointGood ρ m N sig C J i b) :
    actualEndpointMask ρ m N sig C J i b x w=1 := by
  obtain ⟨P,hP,hx⟩ := hx
  rw [actualEndpointMask_of_mem ρ m N sig C J i b hP hx]
  exact actualDescriptorMask_one ρ m N sig C J i P b (hg P hP hx)

lemma uniform_actualEndpointMask_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ) (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ (k : ℕ) (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualEndpointMask ρ m N sig C J i b x)) →
      (x,w) ∈ endpointGood ρ m N sig C J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_actualDescriptorMask_support (d := d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf m C i b hb k x w hw hs P hP hx
  rw [actualEndpointMask_of_mem ρ m N sig C J i b hP hx] at hs
  exact h₀ N hN ρ hf m C i b hb P ((mem_dyadicPaths _ _).mp hP) k w hw hs

lemma actualEndpointMask_derivatives (d B : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d)))
      (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (k : ℕ), k ≤ B → ∀ x w,
      ‖iteratedFDeriv ℝ k (actualEndpointMask ρ m N sig C J i b x) w‖ ≤
        C₀*(sourceMaskScaleND (descriptorLength b) ((2:ℝ)^N) sig)^k := by
  classical
  obtain ⟨C₀,hC,h₀⟩ := actualDescriptorMask_derivatives d B
  refine ⟨C₀,hC,?_⟩
  intro ρ m N sig C J i b k hk x w
  by_cases hx : ∃ P ∈ dyadicPaths (descriptorAnchor b), x ∈ treeCell P
  · obtain ⟨P,hP,hx⟩ := hx
    rw [actualEndpointMask_of_mem ρ m N sig C J i b hP hx]
    exact h₀ ρ m N sig C J i P b k hk w
  · rw [actualEndpointMask_of_absent ρ m N sig C J i b (by simpa only [not_exists,not_and] using hx)]
    change ‖iteratedFDeriv ℝ k (fun _ : EuclideanSpace ℝ (Fin d) => (0:ℝ)) w‖ ≤ _
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg hC (pow_nonneg (sourceMaskScaleND_pos _ _ _).le k)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
