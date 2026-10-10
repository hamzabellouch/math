import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalBatchEnumeration

namespace OAI


                                        
section
namespace MetricKMedian.RationalBatchData.ActionCodes
open Finset FixedBatch
variable {n : ℕ} (Full : Actions (Fin n) (Fin n)) (H : Finset (Fin n))
abbrev pairOrder : LinearOrder (Fin n × Fin n) :=
  LinearOrder.lift' (fun p : Fin n × Fin n => toLex p) (fun _ _ h => h)
abbrev actionOrder : LinearOrder (HeavyAction Full H) := by
  letI : LinearOrder (Fin n × Fin n) := pairOrder (n:=n)
  exact LinearOrder.lift' (fun e : HeavyAction Full H => toLex e) (fun _ _ h => h)

def code : HeavyAction Full H → ℕ
 | .inl h => h.val.val
 | .inr p => n+p.val.1.val*n+p.val.2.val

 theorem code_strictMono : @StrictMono _ _ (actionOrder Full H).toPreorder _ (code Full H) := by
  let : LinearOrder (Fin n × Fin n) := pairOrder (n:=n)
  let : LinearOrder (HeavyAction Full H) := actionOrder Full H
  intro e f hef
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hh := Sum.lex_inl_inl.mp hef
      exact hh
    | inr f =>
      simp only [code]
      have he := e.val.isLt
      omega
  | inr e =>
    cases f with
    | inl f =>
      cases hef
    | inr f =>
      have hh := Sum.lex_inr_inr.mp hef
      change Prod.Lex (fun a b : Fin n => a<b) (fun a b : Fin n => a<b) e.val f.val at hh
      have hef := Prod.lex_def.mp hh
      simp only [code]
      rcases hef with h | ⟨h,h'⟩
      · have h1 : e.val.1.val+1≤f.val.1.val := h
        have h2 := e.val.2.isLt
        nlinarith
      · have h1 : e.val.1.val=f.val.1.val := congrArg Fin.val h
        have h2 : e.val.2.val<f.val.2.val := h'
        rw [h1]
        omega

 theorem code_lt (e : HeavyAction Full H) : code Full H e<n+n*n := by
  cases e with
  | inl e => simp only [code]; have he := e.val.isLt; omega
  | inr e =>
    simp only [code]
    have he := e.val.1.isLt
    have hf := e.val.2.isLt
    nlinarith

 def valid (c : ℕ) : Prop :=
  if hc : c<n then (⟨c,hc⟩ : Fin n)∉H
  else ∃ h i : Fin n, h∈H ∧ i∈Full.erase h ∧ c=n+h.val*n+i.val

 theorem valid_iff (c : ℕ) : valid Full H c ↔ ∃ e, code Full H e=c := by
  unfold valid
  split_ifs with hc
  · constructor
    · intro h; exact ⟨.inl ⟨⟨c,hc⟩,h⟩,rfl⟩
    · rintro ⟨e,he⟩
      cases e with
      | inl e => simpa only [code,Fin.ext_iff] using he ▸ e.property
      | inr e => simp only [code] at he; omega
  · constructor
    · rintro ⟨h,i,hh,hi,rfl⟩; exact ⟨.inr ⟨(h,i),hh,hi⟩,rfl⟩
    · rintro ⟨e,he⟩
      cases e with
      | inl e => exact (hc (he ▸ e.val.isLt)).elim
      | inr e => exact ⟨e.val.1,e.val.2,e.property.1,e.property.2,he.symm⟩

 theorem enumeration_strictMono : StrictMono (fun i => code Full H (enumeration Full H i)) := by
  let : LinearOrder (Fin n × Fin n) := pairOrder (n:=n)
  let : LinearOrder (HeavyAction Full H) := actionOrder Full H
  intro i j hij
  apply code_strictMono Full H
  exact @OrderIso.strictMono _ _ _ (actionOrder Full H).toPreorder
    (@Fintype.orderIsoFinOfCardEq (HeavyAction Full H) (actionOrder Full H) _ _ rfl) i j hij

end MetricKMedian.RationalBatchData.ActionCodes
end

end OAI
