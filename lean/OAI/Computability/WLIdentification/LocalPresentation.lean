import OAI.Computability.WLIdentification.PresentationArithmetic

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions NumericFinite
variable {C B : Word → Type} [∀ w, DecidableEq (C w)]

structure Locals (CP : Presented C) (BP : Presented B) where
  coordinates : ∀ w, B w → Finset (C w)
  size : ∀ w b, (coordinates w b).card ≤ 5
  member : Test (BP.prod CP) (fun w p => decide (p.2 ∈ coordinates w p.1))

namespace Locals
variable {CP : Presented C} {BP : Presented B} (D : Locals CP BP)

abbrev Value (w : Word) (b : B w) := (c : D.coordinates w b) → Bit

def good (w : Word) (b c : ℕ) : Bool := CP.good w c && D.member.eval w (Nat.pair b c)

theorem good_iff (w : Word) (b : B w) (i : ℕ) :
    D.good w (BP.code w b) i=true ↔ ∃ x : D.coordinates w b, CP.code w x.val=i := by
  simp only [good, Bool.and_eq_true]
  constructor
  · rintro ⟨hc,hm⟩
    obtain ⟨c,rfl⟩ := (CP.good_iff w i).mp hc
    have h := D.member.correct w (b,c)
    change D.member.eval w (Nat.pair (BP.code w b) (CP.code w c))=decide (c∈D.coordinates w b) at h
    exact ⟨⟨c,of_decide_eq_true (h ▸ hm)⟩,rfl⟩
  · rintro ⟨c,rfl⟩
    refine ⟨CP.good_code w c.val,?_⟩
    have h := D.member.correct w (b,c.val)
    change D.member.eval w (Nat.pair (BP.code w b) (CP.code w c.val))=_ at h
    rw [h,decide_eq_true_eq]
    exact c.property

noncomputable def localP (w : Word) (b : B w) : Presented (fun _ => D.coordinates w b) :=
  Presented.ofCode _ (NaturalCode.subtype (CP.code w) _) (CP.bound w)
    (D.good w (BP.code w b)) (fun c => CP.code_lt w c.val) (D.good_iff w b)

def count (w : Word) (b : ℕ) : ℕ := NumericFinite.count (CP.bound w) (D.good w b)

theorem count_eq (w : Word) (b : B w) : D.count w (BP.code w b)=(D.coordinates w b).card := by
  change (D.localP w b).card [] = _
  rw [Presented.card_eq, Fintype.card_coe]

def rank (w : Word) (b c : ℕ) : ℕ := NumericFinite.count c (D.good w b)

noncomputable def valueEquiv (w : Word) (b : B w) :
    D.Value w b ≃ Fin (2^(D.count w (BP.code w b))) :=
  (Equiv.arrowCongr ((D.localP w b).rankEquiv []) (ZMod.finEquiv 2).toEquiv.symm).trans finFunctionFinEquiv

noncomputable def valueCode (w : Word) (b : B w) : D.Value w b ↪ ℕ :=
  (D.valueEquiv w b).toEmbedding.trans (NaturalCode.fin _)

def valueGood (w : Word) (b v : ℕ) : Bool := decide (v < min (2^(D.count w b)) 32)

theorem valueGood_iff (w : Word) (b : B w) (i : ℕ) :
    D.valueGood w (BP.code w b) i=true ↔ ∃ v, D.valueCode w b v=i := by
  have h : 2^(D.count w (BP.code w b)) ≤ 32 := by
    rw [D.count_eq]
    exact Nat.pow_le_pow_right (by decide) (D.size w b)
  simp only [valueGood, min_eq_left h, decide_eq_true_eq]
  exact ⟨fun hi => ⟨(D.valueEquiv w b).symm ⟨i,hi⟩, congrArg Fin.val ((D.valueEquiv w b).apply_symm_apply _)⟩,
    fun ⟨v,hv⟩ => hv ▸ (D.valueEquiv w b v).isLt⟩

theorem good_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : BoolPoly (fun S => D.good (w S) (b S) (c S)) :=
  BoolPoly.and (CP.good_poly_of hw hc) (D.member.eval_poly hw (NatPoly.pair hb hc))

theorem count_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => D.count (w S) (b S)) := by
  apply (NatPoly.filterCount (CP.bound_poly_of hw)
    (D.good_poly (hw.rename Fin.castSucc) (hb.rename Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  simp only [Fin.snoc_comp_castSucc, Fin.snoc_last, unary, List.length_replicate]
  rfl

theorem rank_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : NatPoly (fun S => D.rank (w S) (b S) (c S)) := by
  apply (NatPoly.filterCount hc
    (D.good_poly (hw.rename Fin.castSucc) (hb.rename Fin.castSucc) (NatPoly.var (Fin.last n)))).congr
  intro S
  simp only [Fin.snoc_comp_castSucc, Fin.snoc_last, unary, List.length_replicate]
  rfl

noncomputable def values : Presented (fun w => Σ b : B w, D.Value w b) :=
  BP.sigma (D.Value) D.valueCode (fun _ => 32) D.valueGood
    (by intro w b v; have := (D.valueEquiv w b v).isLt
        have h := D.size w b
        rw [← D.count_eq w b] at h
        exact this.trans_le (Nat.pow_le_pow_right (by decide) h))
    D.valueGood_iff (NatPoly.const _)
    (NatPoly.lt (NatPoly.var 2) (NatPoly.cappedPow (NatPoly.const 2)
      (D.count_poly (Poly.var 0) (NatPoly.var 1)) (NatPoly.const 32)))

def read (w : Word) (b v c : ℕ) : ℕ := NumericKernel.digit 2 v (D.rank w b c)

theorem read_value (w : Word) (b : B w) (v : D.Value w b) (c : D.coordinates w b) :
    D.read w (BP.code w b) (D.valueCode w b v) (CP.code w c.val)=(v c).val := by
  have h := (D.valueEquiv w b).symm_apply_apply v
  have h' := congrArg (fun f => (f c).val) h
  exact h'

theorem read_poly {n} {w : (Fin n → Word) → Word} {b v c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hc : NatPoly c) :
    NatPoly (fun S => D.read (w S) (b S) (v S) (c S)) :=
  NatPoly.digit (NatPoly.const 2) hv (D.rank_poly hw hb hc)

end Locals
end FinitePresentation

end WLIdentification

end OAI
