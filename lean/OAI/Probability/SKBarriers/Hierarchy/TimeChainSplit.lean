import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarTimeChain

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def chainDuration (l : List (ℝ × ℝ≥0)) : ℝ≥0 := (l.map Prod.snd).sum

@[simp] theorem chainDuration_nil : chainDuration []=0 := rfl
@[simp] theorem chainDuration_cons (m : ℝ) (t : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    chainDuration ((m,t)::l)=t+chainDuration l := rfl

def TimeChainModels (α : ℝ → ℝ) : ℝ → List (ℝ × ℝ≥0) → Prop
  | _,[] => True
  | s,(m,t)::l => (∀ z ∈ Ico s (s+t), α z=m) ∧ TimeChainModels α (s+t) l

theorem scalarTimeChain_split_at (β : ℝ) (α : ℝ → ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) (s : ℝ) (hmodel : TimeChainModels α s l)
    (t₁ t₂ : ℝ≥0) (ht : chainDuration l=t₁+t₂) :
    ∃ l₁ l₂ : List (ℝ × ℝ≥0), chainDuration l₁=t₁ ∧ chainDuration l₂=t₂ ∧
      (∀ p ∈ l₁, p.1 ∈ Icc (0:ℝ) 1) ∧ (∀ p ∈ l₂, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels α s l₁ ∧ TimeChainModels α (s+t₁) l₂ ∧
      ∀ f : ℝ → ℝ, BoundedDerivs f →
        scalarTimeChain β l₁ (scalarTimeChain β l₂ f)=scalarTimeChain β l f := by
  induction l generalizing s t₁ t₂ with
  | nil =>
    have h0 : t₁=0 ∧ t₂=0 := (add_eq_zero.mp ht.symm)
    obtain ⟨rfl,rfl⟩ := h0
    exact ⟨[],[],rfl,rfl,by simp,by simp,trivial,trivial,fun _ _ => rfl⟩
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    have hp := hm (m,d) (List.mem_cons_self)
    have hm' (p) (hp : p∈l) := hm p (List.mem_cons_of_mem _ hp)
    rcases hmodel with ⟨hcell,htail⟩
    dsimp only [chainDuration_cons] at ht
    by_cases hcut : t₁≤d
    · refine ⟨[(m,t₁)],(m,d-t₁)::l,by simp,?_,?_,?_,?_,?_,?_⟩
      · simp only [chainDuration_cons]
        have hsum : t₁+(d-t₁)=d := add_tsub_cancel_of_le hcut
        exact add_left_cancel (show t₁+((d-t₁)+chainDuration l)=t₁+t₂ by
          rw [← add_assoc,hsum,ht])
      · intro p hmem
        simp only [List.mem_singleton] at hmem
        subst p
        exact hp
      · intro p hmem
        rcases List.mem_cons.mp hmem with rfl|hmem
        · exact hp
        · exact hm' p hmem
      · constructor
        · intro z hz
          have hc : (t₁:ℝ)≤d := hcut
          exact hcell z ⟨hz.1,by linarith [hz.2]⟩
        · trivial
      · constructor
        · intro z hz
          apply hcell z
          constructor
          · exact (le_add_of_nonneg_right t₁.coe_nonneg).trans hz.1
          · rw [NNReal.coe_sub hcut] at hz
            linarith [hz.2]
        · have hstart : s+(t₁:ℝ)+((d-t₁:ℝ≥0):ℝ)=s+d := by
            rw [NNReal.coe_sub hcut]
            ring
          rw [hstart]
          exact htail
      · intro f hf
        simp only [scalarTimeChain]
        rw [scalarTimeStep_semigroup (scalarTimeChain_regular hf β l),add_tsub_cancel_of_le hcut]
    · have hdc : d≤t₁ := (le_of_not_ge hcut)
      have hsum : d+(t₁-d)=t₁ := add_tsub_cancel_of_le hdc
      have htaildur : chainDuration l=(t₁-d)+t₂ := by
        apply add_left_cancel (a:=d)
        rw [← add_assoc,hsum,ht]
      obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,ht₁,ht₂,he⟩ := ih hm' (s+d) htail (t₁-d) t₂ htaildur
      refine ⟨(m,d)::l₁,l₂,?_,h₂,?_,hm₂,?_,?_,?_⟩
      · simp only [chainDuration_cons,h₁,hsum]
      · intro p hmem
        rcases List.mem_cons.mp hmem with rfl|hmem
        · exact hp
        · exact hm₁ p hmem
      · exact ⟨hcell,ht₁⟩
      · have hstart : s+(d:ℝ)+((t₁-d:ℝ≥0):ℝ)=s+t₁ := by
          rw [NNReal.coe_sub hdc]
          ring
        rw [hstart] at ht₂
        exact ht₂
      · intro f hf
        simp only [scalarTimeChain,he f hf]

end SK.Analytic

end
end

end OAI
