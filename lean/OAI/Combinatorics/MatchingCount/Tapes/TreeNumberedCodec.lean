import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeSum
import OAI.Combinatorics.MatchingCount.Machines.TreeClosureReindex

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A : Type} [Fintype A] [LinearOrder A]
def index (a : A) : ℕ := ((UnitRefresh.orderedEnum A).symm a).val
instance (priority := 100) codec : Codec A := ⟨fun a=>encode (index a)⟩
lemma index_injective : Function.Injective (index (A:=A)) := by
  intro a b h
  exact (UnitRefresh.orderedEnum A).symm.injective (Fin.ext h)
lemma index_le (a b : A) : index a ≤ index b ↔ a ≤ b := by
  change (UnitRefresh.orderedEnum A).symm a ≤ (UnitRefresh.orderedEnum A).symm b ↔ _
  rw [←not_lt,←not_lt,←UnitRefresh.orderedEnum_lt]
  simp

def equal : Realizer (fun x : A×A=>decide (x.1=x.2)) :=
  natEqual.recode (fun x : A×A=>(index x.1,index x.2)) _ (fun _=>rfl) (fun x=>by
    simp only [(index_injective (A:=A)).eq_iff])
def lessEqual : Realizer (fun x : A×A=>decide (x.1≤x.2)) :=
  leNat.recode (fun x : A×A=>(index x.1,index x.2)) _ (fun _=>rfl) (fun x=>by
    simp only [index_le])
lemma polynomial_equal : PolynomialTime (equal (A:=A)) :=
  polynomial_recode _ _ _ _ polynomial_natEqual
lemma polynomial_lessEqual : PolynomialTime (lessEqual (A:=A)) :=
  polynomial_recode _ _ _ _ polynomial_leNat
@[simp] lemma equal_program : (equal (A:=A)).program=natEqual.program := rfl
@[simp] lemma lessEqual_program : (lessEqual (A:=A)).program=leNat.program := rfl

lemma index_orderedEnum (i : Fin (Fintype.card A)) :
    index (UnitRefresh.orderedEnum A i)=i.val := by simp [index]
end MatchingFPRAS.TreeTyped.Numbered

end OAI
