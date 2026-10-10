import OAI.NumberTheory.Ostmann.Construction.CanonicalHistory

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem assignedSlots_injective (sources : SourceFamily) (T : List SourceSlot) :
    Function.Injective (assignedSlots sources T) := by
  intro x y h
  have hf := List.ofFn_injective h
  funext i
  apply Subtype.ext
  exact congrArg SmallSlot.value (congrFun hf i)

namespace History

def nodeCompensation {l : ℕ} : History (l+1) → List SmallSlot
  | .node _ _ u _ _ _ _ => u

def nodeLeft {l : ℕ} : History (l+1) → History l
  | .node _ _ _ _ _ left _ => left

def nodeRight {l : ℕ} : History (l+1) → History l
  | .node _ _ _ _ _ _ right => right

end History

theorem decodeHistory_injective (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) :
    Function.Injective (decodeHistory sources seed V l a) := by
  induction l generalizing a with
  | zero =>
    intro x y h
    change @Eq Unit x y
    exact @Subsingleton.elim Unit inferInstance x y
  | succ l ih =>
    rintro ⟨v,w,u,cl,cr⟩ ⟨v',w',u',dl,dr⟩ heq
    have hv : v=v' := by
      apply Subtype.ext
      have h := congrArg (fun H => (History.nodeLeft H).root.frequency) heq
      simpa only [decodeHistory, History.nodeLeft, decodeHistory_root] using h
    have hw : w=w' := by
      apply Subtype.ext
      have h := congrArg (fun H => (History.nodeRight H).root.frequency) heq
      simpa only [decodeHistory, History.nodeRight, decodeHistory_root] using h
    have hu : u=u' := by
      apply assignedSlots_injective
      have h := congrArg History.nodeCompensation heq
      simpa only [decodeHistory, History.nodeCompensation] using h
    subst v'
    subst w'
    subst u'
    have hcl : cl=dl := by
      apply ih
      have h := congrArg History.nodeLeft heq
      simpa only [decodeHistory, History.nodeLeft] using h
    have hcr : cr=dr := by
      apply ih
      have h := congrArg History.nodeRight heq
      simpa only [decodeHistory, History.nodeRight] using h
    subst dl
    subst dr
    rfl

def canonicalHistoryPool (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) : Finset (History l) := by
  classical
  exact Finset.univ.image (decodeHistory sources seed V l a)

theorem canonicalCoefficient_eq_coefficient (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (a : State) :
    canonicalCoefficient sources seed V outside base φ G l a =
      coefficient (canonicalHistoryPool sources seed V l a) (sourceMass sources)
        V outside base φ G a := by
  classical
  unfold coefficient canonicalHistoryPool
  rw [Finset.sum_image]
  · simp only [decodeHistory_root, ite_true, decodeHistory_internalMass, canonicalCoefficient]
  · intro c hc d hd heq
    exact decodeHistory_injective sources seed V l a heq

end Ostmann.Construction

end

end OAI
