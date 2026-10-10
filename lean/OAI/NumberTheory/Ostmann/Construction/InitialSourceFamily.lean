import OAI.NumberTheory.Ostmann.Construction.PrimeSources

namespace OAI

noncomputable section
namespace Ostmann.Construction

def initialSourceValue {α : Type*} (b k : ℕ) (bulk : α)
    (top : Fin 3 → α) (comp : Fin k → Fin 2 → α) (origin : ℕ) : α :=
  if origin<2*b then bulk else
  if origin<2*b+6 then top ⟨(origin-2*b)%3,Nat.mod_lt _ (by decide)⟩ else
  if hj : (origin-(2*b+6))/4<k then
    comp ⟨(origin-(2*b+6))/4,hj⟩ ⟨(origin-(2*b+6))%2,Nat.mod_lt _ (by decide)⟩
  else bulk

def initialSourceFamily (b k : ℕ) (bulk : PrimeSource)
    (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource) : SourceFamily :=
  initialSourceValue b k bulk top comp

theorem initialSourceValue_bulk {α : Type*} (b k : ℕ) (bulk : α)
    (top : Fin 3 → α) (comp : Fin k → Fin 2 → α) {i : ℕ} (hi : i<2*b) :
    initialSourceValue b k bulk top comp i=bulk := by
  simp only [initialSourceValue,hi,ite_true]

theorem initialSourceValue_top {α : Type*} (b k : ℕ) (bulk : α)
    (top : Fin 3 → α) (comp : Fin k → Fin 2 → α) (h : Bool) (i : Fin 3) :
    initialSourceValue b k bulk top comp (2*b+(if h then 3 else 0)+i)=top i := by
  cases h <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
    unfold initialSourceValue <;> split_ifs <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    dsimp only
    omega

theorem initialSourceValue_comp {α : Type*} (b k : ℕ) (bulk : α)
    (top : Fin 3 → α) (comp : Fin k → Fin 2 → α) (h : Bool) (j : Fin k) (i : Fin 2) :
    initialSourceValue b k bulk top comp (2*b+6+4*j+(if h then 2 else 0)+i)=comp j i := by
  cases h <;> simp only [Bool.false_eq_true,↓reduceIte] <;>
    unfold initialSourceValue <;> split_ifs <;> try omega
  all_goals
    congr 1 <;> apply Fin.ext <;> dsimp only <;> omega

end Ostmann.Construction

end

end OAI
