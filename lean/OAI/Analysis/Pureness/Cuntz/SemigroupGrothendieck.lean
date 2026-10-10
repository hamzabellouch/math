import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import OAI.Analysis.Pureness.Cuntz.SemigroupComparisonArithmetic
import Mathlib.Tactic.Abel

namespace OAI
noncomputable section
namespace CuntzPureness.OrderedSemigroup
variable {S : Type*} [AddCommMonoid S]
open Algebra

theorem grothendieck_eq_iff (a b : S) :
    GrothendieckAddGroup.of a = GrothendieckAddGroup.of b ↔ ∃ c : S, a+c=b+c := by
  change AddLocalization.mk a 0 = AddLocalization.mk b 0 ↔ _
  simp only [AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists,
    AddSubmonoid.coe_zero, zero_add, Subtype.exists, AddSubmonoid.mem_top]
  simp [add_comm]

theorem grothendieck_difference_eq_iff (a b c d : S) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a =
      GrothendieckAddGroup.of d - GrothendieckAddGroup.of c ↔
        ∃ e : S, b+c+e=d+a+e := by
  rw [sub_eq_sub_iff_add_eq_add, ← map_add, ← map_add, grothendieck_eq_iff]

theorem grothendieck_exists_difference (g : GrothendieckAddGroup S) :
    ∃ a b : S, g = GrothendieckAddGroup.of b - GrothendieckAddGroup.of a := by
  induction g using AddLocalization.ind with
  | H p =>
    refine ⟨p.2,p.1,?_⟩
    change AddLocalization.mk p.1 p.2 = (AddLocalization.mk p.1 0 : GrothendieckAddGroup S) - (AddLocalization.mk p.2 0 : GrothendieckAddGroup S)
    rw [GrothendieckAddGroup.mk_sub_mk]
    simp

variable [PartialOrder S] [IsOrderedAddMonoid S]

def grothendieckCone : AddSubmonoid (GrothendieckAddGroup S) where
  carrier := {g | ∃ a b : S, a ≤ b ∧ g = GrothendieckAddGroup.of b - GrothendieckAddGroup.of a}
  zero_mem' := ⟨0,0,le_rfl,by simp⟩
  add_mem' := by
    rintro g h ⟨a,b,hab,rfl⟩ ⟨c,d,hcd,rfl⟩
    exact ⟨a+c,b+d,add_le_add hab hcd,by simp only [map_add]; abel⟩

theorem grothendieck_mem_cone_iff (a b : S) :
    GrothendieckAddGroup.of b - GrothendieckAddGroup.of a ∈ grothendieckCone ↔
      ∃ c : S, a+c ≤ b+c := by
  constructor
  · rintro ⟨c,d,hcd,heq⟩
    obtain ⟨e,he⟩ := (grothendieck_difference_eq_iff a b c d).mp heq
    refine ⟨c+e,?_⟩
    calc
      a+(c+e) ≤ a+(d+e) := add_le_add le_rfl (add_le_add hcd le_rfl)
      _ = b+(c+e) := by rw [← add_assoc, add_comm a d, ← he, add_assoc]
  · rintro ⟨c,hc⟩
    refine ⟨a+c,b+c,hc,?_⟩
    simp only [map_add]
    abel

lemma grothendieck_of_nonneg (hzero : ∀ a : S, 0 ≤ a) (a : S) :
    GrothendieckAddGroup.of a ∈ grothendieckCone :=
  ⟨0,a,hzero a,by simp⟩

theorem grothendieck_orderUnit (hzero : ∀ a : S, 0 ≤ a)
    (u : S) (hunit : ∀ a : S, ∃ n : ℕ, a ≤ n • u)
    (g : GrothendieckAddGroup S) :
    ∃ n : ℕ, n • GrothendieckAddGroup.of u + g ∈ grothendieckCone := by
  obtain ⟨a,b,rfl⟩ := grothendieck_exists_difference g
  obtain ⟨n,hn⟩ := hunit a
  refine ⟨n,a,n • u+b,hn.trans (le_add_of_nonneg_right (hzero b)),?_⟩
  simp only [map_add,map_nsmul]
  abel
end CuntzPureness.OrderedSemigroup

end

end OAI
