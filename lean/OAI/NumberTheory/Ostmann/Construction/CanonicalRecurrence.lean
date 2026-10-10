import OAI.NumberTheory.Ostmann.Construction.CanonicalFrame
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

def guardedCanonicalCoefficient (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (parent a : State) : ℂ :=
  ∑ c : HistoryChoices sources seed V l,(choicesMass sources seed V l c:ℂ)*
    History.guardedWeight parent V outside base φ G (decodeHistory sources seed V l a c)

theorem independent_node_sum {α β : Type*} [Fintype α] [Fintype β]
    (μ : α → ℝ) (ν : β → ℝ) (P : Prop) (K : ℂ) (f : α → ℂ) (g : β → ℂ) :
    (∑ x,∑ y,(μ x:ℂ)*(ν y:ℂ)*(if P then K*f x*conj (g y) else 0)) =
      if P then K*(∑ x,(μ x:ℂ)*f x)*conj (∑ y,(ν y:ℂ)*g y) else 0 := by
  by_cases hP : P
  · simp only [hP,ite_true,map_sum,map_mul,Complex.conj_ofReal]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  · simp only [hP,ite_false,mul_zero,Finset.sum_const_zero]

theorem canonicalCoefficient_node (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (a : State) :
    canonicalCoefficient sources seed V outside base φ G (l+1) a =
      ∑ v : AllowedFrequency V l, ∑ w : AllowedFrequency V l,
      ∑ u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)),
        let f := canonicalFrame sources seed V l a v w u
        ((assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass u:ℂ)*
          (if f.Valid V outside l then f.scalar φ G*
            guardedCanonicalCoefficient sources seed V outside base φ G l a f.plusState*
            conj (guardedCanonicalCoefficient sources seed V outside base φ G l a f.minusState)
           else 0) := by
  unfold canonicalCoefficient
  change (∑ c : AllowedFrequency V l × AllowedFrequency V l ×
      SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)) ×
      HistoryChoices sources seed V l × HistoryChoices sources seed V l,
    (choicesMass sources seed V (l+1) c:ℂ)*
      History.supportedWeight V outside base φ G (decodeHistory sources seed V (l+1) a c)) = _
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro u hu
  simp only [decodeHistory_node,History.supportedWeight_node,decodeHistory_root,
    choicesMass,Complex.ofReal_mul]
  let f := canonicalFrame sources seed V l a v w u
  simp_rw [mul_assoc,← Finset.mul_sum]
  congr 1
  have h := independent_node_sum (choicesMass sources seed V l) (choicesMass sources seed V l)
      (f.Valid V outside l) (f.scalar φ G)
      (fun x => History.guardedWeight a V outside base φ G (decodeHistory sources seed V l f.plusState x))
      (fun y => History.guardedWeight a V outside base φ G (decodeHistory sources seed V l f.minusState y))
  by_cases hp : f.Valid V outside l
  all_goals
    simp only [NodeFrame.Valid,f,canonicalFrame] at hp
    simp only [guardedCanonicalCoefficient,NodeFrame.Valid,NodeFrame.scalar,f,canonicalFrame,
      hp,ite_false,mul_zero,Finset.sum_const_zero,mul_assoc,← Finset.mul_sum] at h ⊢ <;>
      exact h

end Ostmann.Construction

end

end OAI
