import Mathlib
import OAI.Combinatorics.KMedian.Machines.RawCSP
import OAI.Combinatorics.KMedian.Machines.RotationBounds

namespace OAI

section Inline_PCPCSPTableBounds
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic Finset
open scoped BigOperators Classical

variable {A : Type} [Fintype A] [DecidableEq A]
noncomputable def relationBound : ℕ := RotationTable.codeBound (D := Finset (A × A))
noncomputable def sizeBound (N : ℕ) : ℕ :=
  2*(N*(2*(enc ()).length+1))+1+N*(2*(2*(N+1)+1+(2*(N+1)+1+relationBound (A := A)))+1)
omit [DecidableEq A] in
lemma size_bound {s : CSPTable A} (h : s.WellFormed) (N : ℕ)
    (hN : s.1.length+s.2.length≤N) : (enc s).length≤ sizeBound (A := A) N := by
  have h1 : (enc s.1).length ≤ N*(2*(enc ()).length+1) := by
    apply (EncodedList.length_bound enc s.1 _ (by intros; exact Nat.le_refl _)).trans
    exact Nat.mul_le_mul_right _ (by omega)
  have he (r : CSPRow A) (hr : r∈s.2) :
      (enc r).length≤2*(N+1)+1+(2*(N+1)+1+relationBound (A := A)) := by
    have hh := h.2 r hr
    have hl : r.1.bits.length≤N+1 :=
      (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have hr : r.2.1.bits.length≤N+1 :=
      (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have ha := RotationTable.code_le r.2.2
    change (encodePair Nat.bits (encodePair Nat.bits enc) r).length≤_
    rw [encodePair_length,encodePair_length]
    change _≤_ at ha
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) _)
      (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hr) _) ha)
  have h2 := EncodedList.length_bound enc s.2 _ he
  have h2' := h2.trans (Nat.mul_le_mul_right _ (show s.2.length≤N by omega))
  change (encodePair enc enc s).length≤_
  rw [encodePair_length]
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _) h2'
omit [DecidableEq A] in
lemma count_le_encoding (s : CSPTable A) : s.1.length+s.2.length≤(enc s).length := by
  have h1 := EncodedList.length_le enc s.1
  have h2 := EncodedList.length_le enc s.2
  change s.1.length ≤ (enc s.1).length at h1
  change s.2.length ≤ (enc s.2).length at h2
  change _≤(encodePair enc enc s).length
  rw [encodePair_length]
  omega
noncomputable def check (s : CSPTable A) : Bool :=
  decide (0<s.2.length) && ((s.2.filter fun r => !(decide (r.1<s.1.length) && decide (r.2.1<s.1.length))).isEmpty)
omit [Fintype A] [DecidableEq A] in
lemma check_iff (s : CSPTable A) : check s=true ↔ s.WellFormed := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,List.filter_eq_nil_iff,
    Bool.not_eq_true,CSPTable.WellFormed]
  aesop
omit [DecidableEq A] in
lemma poly_check : Poly (check (A := A)) := by
  unfold check
  have hf : Poly (fun s : CSPTable A => s.2.filter fun r => !(decide (r.1<s.1.length) && decide (r.2.1<s.1.length))) := by
    apply Poly.list_filter
    · fun_prop
    · exact Poly.snd
  fun_prop
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPCSPTableBounds

end OAI
