import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing
import OAI.MeasureTheory.FalconerCompletion.Fourier.LawRoot

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped Classical ENNReal
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

lemma assemblyDescriptorList_card (A : ℕ → ℝ) {N q c : ℕ} (hq : 0<q) :
    (assemblyDescriptorList A N q c).card ≤ (N+1)^3+1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (policyDescriptorList_card A hq) 1)

lemma assemblyPairMask_one (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ) {z : V×V}
    (hz : z∈treeCell [] ×ˢ treeCell [])
    (h₁ : ∀ b∈assemblyDescriptorList e₁.profile e₁.N e₁.q c,
      (z.1,radialVector z.1 z.2)∈endpointGood e₁.ρ e₁.mass e₁.N e₁.sig e₁.C e₁.J 0 b)
    (h₂ : ∀ b∈assemblyDescriptorList e₂.profile e₂.N e₂.q c,
      (z.2,radialVector z.1 z.2)∈endpointGood e₂.ρ e₂.mass e₂.N e₂.sig e₂.C e₂.J 0 b) :
    assemblyPairMask e₁ e₂ c z=1 := by
  have hp (e : RecursiveEnvironmentND n) (x : V) (hx : x∈treeCell [])
      (hg : ∀ b∈assemblyDescriptorList e.profile e.N e.q c,
        (x,radialVector z.1 z.2)∈endpointGood e.ρ e.mass e.N e.sig e.C e.J 0 b) :
      (∏ b∈assemblyDescriptorList e.profile e.N e.q c,
        actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b x (radialVector z.1 z.2))=1 := by
    apply Finset.prod_eq_one
    intro b hb
    apply actualEndpointMask_one e.ρ e.mass e.N e.sig e.C e.J 0 b ?_ (hg b hb)
    rw [←treeCell_cover_root (descriptorAnchor b)] at hx
    obtain ⟨P,hP,hxP⟩ := mem_iUnion₂.mp hx
    exact ⟨P,hP,hxP⟩
  rw [assemblyPairMask,hp e₁ z.1 hz.1 h₁,hp e₂ z.2 hz.2 h₂,one_mul]

section Families
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {μ ν : Measure (EuclideanSpace ℝ (Fin (n+1)))} {N B : ℕ} {chi sig : ℝ}
variable (F : AssemblyClassFamily ι μ N B chi sig) (G : AssemblyClassFamily κ ν N B chi sig)
variable (kap Ctest beta : ℝ)
omit [Fintype ι] [Fintype κ] in
lemma assemblyPairEntry_le (hbeta : 0<beta) (i : ι) (j : κ) :
    assemblyPairEntry F G kap Ctest beta i j ≤ N := by
  apply (GraphLiteralSupport.CurrentFalconer.entryDepthND_spec _ _ ?_).1
  simp only [Fin.isValue,ite_true,RecursiveEnvironmentND.profile,AssemblyClassFamily.env]
  simp only [show (1:Fin 2)≠0 by decide,ite_false]
  simp only [adjustedProfile,Nat.cast_zero,mul_zero,zero_div,sub_zero]
  rw [(F.profile i).zero,(G.profile j).zero]
  simpa using hbeta.le
lemma assemblyTheta_at {z : V×V} {i : ι} {j : κ} (hx : z.1∈F.domain i) (hy : z.2∈G.domain j) :
    assemblyTheta F G kap Ctest beta z = assemblyPairMask (F.env kap Ctest i) (G.env kap Ctest j)
      (assemblyPairEntry F G kap Ctest beta i j) z := by
  unfold assemblyTheta
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · exact indicator_of_mem (show z∈F.domain i ×ˢ G.domain j from ⟨hx,hy⟩) _
    · intro k _ hk
      apply indicator_of_notMem
      intro hz
      exact Set.disjoint_left.mp (G.disjoint hk) hz.2 hy
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    apply indicator_of_notMem
    intro hz
    exact Set.disjoint_left.mp (F.disjoint hk) hz.1 hx
  · simp
lemma assemblyTheta_zero {z : V×V} (h : z.1∉⋃ i,F.domain i ∨ z.2∉⋃ j,G.domain j) :
    assemblyTheta F G kap Ctest beta z=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply indicator_of_notMem
  rintro ⟨hx,hy⟩
  rcases h with h|h
  · exact h (mem_iUnion.mpr ⟨i,hx⟩)
  · exact h (mem_iUnion.mpr ⟨j,hy⟩)
lemma assemblyTheta_bounds (z : V×V) :
    0≤assemblyTheta F G kap Ctest beta z ∧ assemblyTheta F G kap Ctest beta z≤1 := by
  by_cases hx : z.1∈⋃ i,F.domain i
  · by_cases hy : z.2∈⋃ j,G.domain j
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hy
      rw [assemblyTheta_at F G kap Ctest beta hi hj]
      exact assemblyPairMask_bounds _ _ _ _
    · rw [assemblyTheta_zero F G kap Ctest beta (Or.inr hy)]; norm_num
  · rw [assemblyTheta_zero F G kap Ctest beta (Or.inl hx)]; norm_num
lemma assemblyTheta_measurable : Measurable (assemblyTheta F G kap Ctest beta) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (assemblyPairMask_measurable _ _ _).indicator ((F.measurable i).prod (G.measurable j))
end Families
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
