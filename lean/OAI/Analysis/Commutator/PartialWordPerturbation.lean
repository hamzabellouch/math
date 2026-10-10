import Mathlib
import OAI.Analysis.Commutator.CornerCenteredEstimates
import OAI.Analysis.Commutator.PartialUnitaryWords

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

def MomentBound (v : PartialUnitary A) (N : ℕ) (B : ℝ) : Prop :=
  (∀ i,‖τ (v.power (k i))‖ ≤ B) ∧
    ∀ l : List (Letter J K), l≠[] → l.length ≤ N → Valid l → ‖τ (word x k v l)‖ ≤ B

include hτ in
lemma open_scalar_bound {v : PartialUnitary A} {N : ℕ} {B η : ℝ}
    (hbound : MomentBound τ x k v N B) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (s : List (Letter J K)) (j : J) (hlen : s.length+1 ≤ N)
    (hs : ∀ i∈s,NonzeroSlot i.2) :
    ‖cornerScalar τ (1-v.support) (word x k v s*x j)‖ ≤ 2*B/η := by
  apply cornerScalar_complement_bound τ v.projection _ hη hrest
  · have hh := hbound.2 (s++[(j,none)]) (by simp)
      (by simpa only [List.length_append,List.length_singleton] using hlen)
      (valid_of_internal s _ hs)
    simpa only [word_open_last] using hh
  · have hh := hbound.2 (s++[(j,some none)]) (by simp)
      (by simpa only [List.length_append,List.length_singleton] using hlen)
      (valid_of_internal s _ hs)
    rw [word_support_last,hτ] at hh
    exact hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_left (w : PartialUnitary A) (s : Slot K) :
    w.support*slotIncrement k w s=slotIncrement k w s := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.isIdempotentElem.eq
    | some i => exact w.support_power _

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_right (w : PartialUnitary A) (s : Slot K) :
    slotIncrement k w s*w.support=slotIncrement k w s := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.isIdempotentElem.eq
    | some i => exact w.power_support _

omit [PartialOrder A] [StarOrderedRing A] in
lemma slotIncrement_norm (w : PartialUnitary A) (s : Slot K) :
    ‖slotIncrement k w s‖ ≤ 1 := by
  cases s with
  | none => simp [slotIncrement]
  | some s =>
    cases s with
    | none => exact w.projection.norm_le _
    | some i => exact w.power_norm _

include hτ in
theorem word_perturbation_bound (hx : ∀ j,‖x j‖ ≤ 1)
    (v w : PartialUnitary A) (horth : v.support*w.support=0)
    (hqp : w.support ≤ 1-v.support) {N : ℕ} {B δ η : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hη : 0<η) (hrest : η ≤ (τ (1-v.support)).re)
    (hbound : MomentBound τ x k v N B)
    (hsmall : ∀ (s : List (Letter J K)) (j : J), s.length ≤ N →
      TracialL2.norm τ (w.support*cornerCenter τ (1-v.support) (word x k v s*x j)*w.support)^2 ≤
        δ^2*(τ w.support).re)
    (hphase : ∀ (s t : List (Letter J K)) (j : J) (i : K),
      s.length ≤ N → t.length ≤ N →
      ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re)
    (l : List (Letter J K)) (hlen : l.length ≤ N) (hv : Valid l) :
    ‖τ (word x k (v.add w horth) l)-τ (word x k v l)‖ ≤
      ((l.length:ℝ)+(l.length:ℝ)^2)*(δ+2*B/η)*(τ w.support).re := by
  have hqt : 0 ≤ (τ w.support).re := (τ.map_nonneg w.projection.nonneg).1
  have hc : 0 ≤ δ+2*B/η := by positivity
  have hS : 0 ≤ (δ+2*B/η)*(τ w.support).re := mul_nonneg hc hqt
  have hlen1 : ∀ s i t,l=s++i::t → s.length+1 ≤ N ∧ t.length ≤ N := by
    intro s i t he
    have hh : s.length+1+t.length ≤ N := by
      simpa only [he,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hlen
    omega
  have hsingle : ∀ s i t,l=s++i::t →
      ‖τ (wordProduct (letter x k v) s*newLetter x k w i*wordProduct (letter x k v) t)‖ ≤
        (δ+2*B/η)*(τ w.support).re := by
    intro s i t he
    rcases i with ⟨j,i⟩
    cases i with
    | none => simp [newLetter,slotIncrement,hS]
    | some i =>
      cases i with
      | none =>
        have ht : t=[] := tail_nil_of_not_nonzero hv he (by simp [NonzeroSlot])
        subst t
        have hs := internal_prefix hv he
        have hsc := open_scalar_bound τ hτ x k hbound hη hrest s j (hlen1 s _ [] he).1 hs
        have hh := trace_single_support_bound τ hτ v.projection.one_sub w.projection hqp
          (word x k v s*x j) hδ (hsmall s j (by have hh := (hlen1 s _ [] he).1; omega))
        have hcq := mul_le_mul_of_nonneg_right (add_le_add (le_refl δ) hsc) hqt
        calc
          _=‖τ (w.support*(word x k v s*x j))‖ := by
            simp only [wordProduct_nil,mul_one,newLetter,slotIncrement,←mul_assoc]
            rw [hτ]
            simp only [word,mul_assoc]
          _ ≤ (δ+‖cornerScalar τ (1-v.support) (word x k v s*x j)‖)*(τ w.support).re := hh
          _ ≤ _ := hcq
      | some i =>
        have hp := hphase s t j i (by have hh := (hlen1 s _ t he).1; omega)
          (hlen1 s _ t he).2
        have heq : τ (wordProduct (letter x k v) s*newLetter x k w (j,some (some i))*
            wordProduct (letter x k v) t)=
            τ (w.power (k i)*(word x k v t*word x k v s*x j)) := by
          change τ (word x k v s*(x j*w.power (k i))*word x k v t)=_
          calc
            _=τ ((word x k v s*x j)*(w.power (k i)*word x k v t)) := by congr 1; noncomm_ring
            _=τ ((w.power (k i)*word x k v t)*(word x k v s*x j)) := hτ _ _
            _=_ := by congr 1; noncomm_ring
        rw [heq]
        exact hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hqt)
  have hdouble : ∀ s i t j r,l=s++i::(t++j::r) →
      ‖τ (wordProduct (letter x k v) s*newLetter x k w i*
        wordProduct (letter x k v) t*newLetter x k w j*
        wordProduct (fun b => letter x k v b+newLetter x k w b) r)‖ ≤
          (δ+2*B/η)*(τ w.support).re := by
    intro s i t j r he
    have htlen : t.length+1 ≤ N := by
      have hh := hlen
      rw [he,List.length_append,List.length_cons,List.length_append,List.length_cons] at hh
      omega
    have hts := internal_middle hv he
    have hsc := open_scalar_bound τ hτ x k hbound hη hrest t j.1 htlen hts
    have han : ‖word x k v s*x i.1‖ ≤ 1 :=
      (_root_.norm_mul_le _ _).trans ((mul_le_mul (word_norm x k hx v s) (hx _)
        (_root_.norm_nonneg _) (by norm_num)).trans_eq (one_mul (1:ℝ)))
    have hh := trace_centered_compression_bound τ hτ v.projection.one_sub w.projection hqp
      (slotIncrement_right k w i.2) (slotIncrement_left k w j.2)
      han (word_norm x k hx (v.add w horth) r)
      (slotIncrement_norm k w i.2) (slotIncrement_norm k w j.2)
      hδ (hsmall t j.1 (by omega))
    have heq : wordProduct (letter x k v) s*newLetter x k w i*
        wordProduct (letter x k v) t*newLetter x k w j*
        wordProduct (fun b => letter x k v b+newLetter x k w b) r=
        (word x k v s*x i.1)*slotIncrement k w i.2*(word x k v t*x j.1)*
          slotIncrement k w j.2*word x k (v.add w horth) r := by
      rw [word_add]
      simp only [newLetter,word,mul_assoc]
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl δ) hsc) hqt)
  rw [word_add]
  exact (trace_word_second_order_bound τ.toLinearMap (letter x k v) (newLetter x k w)
    l hS hS hsingle hdouble).trans_eq (by ring)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
