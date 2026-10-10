import OAI.Combinatorics.ContingencyTables.Transport.IntegerEquivLaw
import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Independent Boolean words combined with cached integer laws -/

namespace ContingencyTables.IntegerLaw
open FirstSuccess FairBits ResidualMixture
open scoped BigOperators Classical
noncomputable section

def boolean (n : ℕ) : IntegerLaw (Fin n → Bool) (2^n) where
  count _ := 1
  total := by simp

lemma toRational_boolean (n : ℕ) :
    (boolean n).toRational (by positivity)=uniformLaw (α := Fin n → Bool) := by
  apply RationalLaw.ext
  funext x
  simp [toRational,boolean,uniformLaw,uniformMass]

variable {B C : Type*} [Fintype B] [Fintype C] [DecidableEq C]

/-- A short proposal word and an independently drawn cached completion
reserve their full combined word length. -/
def booleanFinish {s f : ℕ} (p : IntegerLaw B (2^f))
    (finish : (Fin s → Bool) → B → C) : IntegerLaw C (2^(s+f)) :=
  (((boolean s).product p).push (fun z => finish z.1 z.2)).rebase (pow_add 2 s f).symm

lemma toRational_booleanFinish {s f : ℕ} (p : IntegerLaw B (2^f))
    (draw : (Fin f → Bool) → B) (finish : (Fin s → Bool) → B → C)
    (hp : p.toRational (by positivity)=mapLaw (uniformLaw (α := Fin f → Bool)) draw) :
    (booleanFinish p finish).toRational (by positivity)=
      mapLaw (uniformLaw (α := Fin (s+f) → Bool))
        (fun bits => finish (splitWordEquiv s f bits).1 (draw (splitWordEquiv s f bits).2)) := by
  classical
  unfold booleanFinish
  rw [toRational_rebase,toRational_push,toRational_product,toRational_boolean,hp]
  have he := mapLaw_product (uniformLaw (α := Fin s → Bool))
    (uniformLaw (α := Fin f → Bool)) id draw
  rw [mapLaw_id] at he
  rw [←he,mapLaw_comp]
  have hs := map_equiv (splitWordEquiv s f)
    (uniformLaw (α := Fin (s+f) → Bool))
    (fun z => finish z.1 (draw z.2))
  rw [uniform_equiv,←uniform_product] at hs
  exact hs
  all_goals positivity

end
end ContingencyTables.IntegerLaw

end OAI
