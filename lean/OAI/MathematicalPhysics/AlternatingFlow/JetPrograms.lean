import OAI.MathematicalPhysics.AlternatingFlow.CertifiedBounds
import OAI.MathematicalPhysics.AlternatingFlow.TypedPrograms
import OAI.MathematicalPhysics.AlternatingFlow.JetNames

namespace OAI

section JetProgramsDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*}

def jetApprox (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (a : A) : List (Fin 4) → RationalPoint → ℕ → ℚ
  | [], q, k => b ((a,q),k)
  | i::w, q, k =>
    let n := k+1+B (a,w.length+2)
    let m := k+2+n
    (jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n

attribute [local irreducible] jetApprox

lemma jetApprox_computable [Primcodable A] (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : Computable b) (hB : Computable B) :
    Computable (fun z : A × List (Fin 4) × RationalPoint × ℕ => jetApprox b B z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let Q := A × List (Fin 4) × RationalPoint × ℕ
  let n (z : Q) := z.2.2.2+1+B (z.1,z.2.1.tail.length+2)
  let m (z : Q) := z.2.2.2+2+n z
  let left (z : Q) : Q := (z.1,z.2.1.tail,shift (z.2.1.head?.getD 0) (tolerance (n z)) z.2.2.1,m z)
  let right (z : Q) : Q := (z.1,z.2.1.tail,z.2.2.1,m z)
  have ha : Computable (fun z : Q => z.1) := Computable.fst
  have hw : Computable (fun z : Q => z.2.1) := Computable.fst.comp Computable.snd
  have hq : Computable (fun z : Q => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hk : Computable (fun z : Q => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ht : Computable (fun z : Q => z.2.1.tail) := Primrec.list_tail.to_comp.comp hw
  have hn : Computable n := Primrec.nat_add.to_comp.comp (Computable.succ.comp hk)
    (hB.comp (ha.pair (Primrec.nat_add.to_comp.comp (Computable.list_length.comp ht) (Computable.const 2))))
  have hm : Computable m := Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp hk (Computable.const 2)) hn
  have he : Computable (fun z : Q => tolerance (n z)) := tolerance_primrec.to_comp.comp hn
  have hl : Computable left := ha.pair (ht.pair ((shift_computable.comp
    ((Computable.option_getD (Primrec.list_head?.to_comp.comp hw) (Computable.const 0)).pair
      (he.pair hq))).pair hm))
  have hr : Computable right := ha.pair (ht.pair (hq.pair hm))
  have hbase : Computable (fun z : Q => b ((z.1,z.2.2.1),z.2.2.2)) :=
    hb.comp ((ha.pair hq).pair hk)
  have hop : Computable (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) :=
    Arithmetic.rat_div.to_comp.comp (Arithmetic.rat_sub.to_comp.comp
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
      (he.comp Computable.fst)
  obtain ⟨c,hc⟩ := binary_recursive_program (fun z : Q => z.2.1 = [])
    (Primrec.eq.decide.to_comp.comp hw (Computable.const []))
    (fun z => b ((z.1,z.2.2.1),z.2.2.2)) hbase left right hl hr
    (fun z : Q × ℚ × ℚ => (z.2.1-z.2.2)/tolerance (n z.1)) hop
  apply computable_of_execute c
  rintro ⟨a,w,q,k⟩
  induction w generalizing q k with
  | nil => simp [hc, jetApprox]
  | cons i w ih =>
    rw [hc]
    simp only [List.cons_ne_nil, ite_false]
    apply Part.mem_bind_iff.mpr
    refine ⟨_, ih (shift i (tolerance (n (a,i::w,q,k))) q) (m (a,i::w,q,k)), ?_⟩
    apply (Part.mem_map_iff _).mpr
    refine ⟨_, ih q (m (a,i::w,q,k)), ?_⟩
    rw [jetApprox]
    rfl

lemma jetApprox_error (f : A → ℝ × Space → ℝ) (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (b : (A × RationalPoint) × ℕ → ℚ) (B : A × ℕ → ℕ)
    (hb : ∀ a q k, |f a (rationalPoint q) - (b ((a,q),k) : ℝ)| ≤ tolerance k)
    (hB : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    ∀ a w q k, |wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q k : ℝ)| ≤ tolerance k := by
  intro a w
  induction w with
  | nil => simpa only [wordJet, jetApprox] using hb a
  | cons i w ih =>
    intro q k
    let C := B (a,w.length+2)
    let n := k+1+C
    let m := k+2+n
    have hd := difference_error (wordJet_smooth (sf a) w) (Nat.cast_nonneg C)
      (fun z => (wordJet_bound (sf a) w 2 z).trans (by rw [Nat.add_comm 2 w.length]; exact hB a (w.length+2) z))
      (rationalPoint q) (direction i) (direction_norm i) (tolerance_pos n)
    have he : |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q)) /
        (tolerance n : ℝ) -
        ((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m) / tolerance n : ℚ)| ≤
          2 * (tolerance m : ℝ) / tolerance n := by
      push_cast
      rw [← sub_div, abs_div, abs_of_pos (tolerance_pos n)]
      apply div_le_div_of_nonneg_right _ (tolerance_pos n).le
      calc
        _ = |(wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - (jetApprox b B a w (shift i (tolerance n) q) m : ℝ)) -
          (wordJet (f a) w (rationalPoint q) - (jetApprox b B a w q m : ℝ))| := by congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (by linarith [ih (shift i (tolerance n) q) m, ih q m])
    have hp : 2 * (tolerance m : ℝ) / tolerance n = tolerance (k+1) := by
      dsimp [m]
      rw [tolerance_add, mul_div_assoc, mul_div_cancel_right₀ _ (tolerance_pos n).ne']
      simp [tolerance, pow_add]; ring
    have hh := abs_sub_le (fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i))
      ((wordJet (f a) w (rationalPoint (shift i (tolerance n) q)) - wordJet (f a) w (rationalPoint q))/(tolerance n : ℝ))
      (((jetApprox b B a w (shift i (tolerance n) q) m - jetApprox b B a w q m)/tolerance n : ℚ) : ℝ)
    rw [shift_cast] at he hh
    have hsum := hh.trans (add_le_add hd he)
    rw [hp] at hsum
    have hp' := difference_precision C k
    have ht : (tolerance (k+1) : ℝ)+(tolerance (k+1) : ℝ) = tolerance k := by simp [tolerance, pow_succ]; ring
    change |fderiv ℝ (wordJet (f a) w) (rationalPoint q) (direction i) - _| ≤ _
    unfold jetApprox
    exact hsum.trans (by linarith)

lemma named_wordJet [Primcodable A] {f : A → ℝ × Space → ℝ}
    (sf : ∀ a, ContDiff ℝ ∞ (f a))
    (hf : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2)))
    (B : A × ℕ → ℕ) (hB : Computable B)
    (hbound : ∀ a r z, ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,r)) :
    Named (fun z : (A × List (Fin 4)) × RationalPoint => wordJet (f z.1.1) z.1.2 (rationalPoint z.2)) := by
  obtain ⟨b,hb,h⟩ := hf
  refine ⟨fun z => jetApprox b B z.1.1.1 z.1.1.2 z.1.2 z.2, ?_, ?_⟩
  · have hp : Computable (fun z : (((A × List (Fin 4)) × RationalPoint) × ℕ) =>
        (z.1.1.1,z.1.1.2,z.1.2,z.2)) :=
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))
    have hg := jetApprox_computable (A := A) b B hb hB
    have hcomp := Computable.comp hg hp
    exact hcomp
  · rintro ⟨⟨a,w⟩,q⟩ k
    exact jetApprox_error f sf b B (fun a q k => h (a,q) k) hbound a w q k

end AlternatingNS.Effective

end JetProgramsDevelopment

end OAI
