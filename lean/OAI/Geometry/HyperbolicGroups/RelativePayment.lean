import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkPayment
import OAI.Geometry.HyperbolicGroups.RelativeRadialBoundary
import OAI.Geometry.HyperbolicGroups.RelativeExceptional

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

lemma top_exceptional_incoming {x : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e)))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true)
    (hl : dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x))) = false) :
    P.index (P.pairing.face⁻¹ x) = .inl (.inl (a,exceptionalMacro.symm)) := by
  obtain ⟨k,hk⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx
    (sameCycle_inv.mp (SameCycle.rfl.apply_right))
  have hei : (target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)) =
      rev n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x))) := by
    rw [vertex_inverse]
    exact P.paired _
  have hax : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)))) = true :=
    (walk_apex_previous n w d ell hell word c hc f P x).trans ha
  rw [hei,hk] at hl hax
  have hlab : macroStep n w a k.symm.adj = rev n w (macroStep n w a k.adj) :=
    macroStep_reverse n w a k.adj
  have he : k.symm = exceptionalMacro := macro_exceptional_port n w a k.symm
    (by rw [hlab]; exact hax)
    (by rw [hlab]; exact hl)
  have hh : k = exceptionalMacro.symm := congrArg SimpleGraph.Dart.symm he
  rw [hk,hh]

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllPaymentIndex := Σ b : Fan n w,
  (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).PaymentIndex

abbrev paymentCorner (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) := p.2.val.1.2.val
abbrev paymentBool (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) := p.2.val.2

def paymentRawDart (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) : P.Dart :=
  if paymentBool n w d ell hell word c hc f P select hs hm hred hrad p then
    P.pairing.face (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p)
  else P.pairing.face⁻¹ (P.pairing.face⁻¹ (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p))

include hb in
lemma payment_raw_index (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    ∃ a, P.index (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad p) =
      .inl (.inl (a,if paymentBool n w d ell hell word c hc f P select hs hm hred hrad p then looseMacro else looseMacro.symm)) := by
  obtain ⟨F,hF⟩ := p.2.property.1
  obtain ⟨e,he⟩ := mark_top_index n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  let a := selectedOccurrence n w d ell hell word c hc f P select p.1 F
  refine ⟨a,?_⟩
  have ha := instance_apex n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2
  have hl := p.2.property.2
  cases ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p
  · have hl' : dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ p.2.val.1.2.val))) = false := by
      simpa only [indexedFanData,ho,Bool.false_eq_true,↓reduceIte,P.linkNext_val] using hl
    have hx := top_exceptional_incoming n w d ell hell word c hc f P he ha hl'
    simpa only [paymentRawDart,ho,Bool.false_eq_true,↓reduceIte] using
      exceptional_previous n w d ell hell word c hc f P hs hb hx
  · have hl' : dartPart n w (macroStep n w a e.adj) = false := by
      simpa only [indexedFanData,ho,↓reduceIte,he,target,exteriorWalkTarget,WalkCellTarget.withExterior,Sum.elim_inl,walkTarget,walkLabel] using hl
    have hh : e = exceptionalMacro := macro_exceptional_port n w a e
      (by simpa only [he,target,exteriorWalkTarget,WalkCellTarget.withExterior,Sum.elim_inl,walkTarget,walkLabel] using ha) hl'
    have hx : P.index p.2.val.1.2.val = .inl (.inl (a,exceptionalMacro)) := by rw [he,hh]
    simpa only [paymentRawDart,ho,↓reduceIte] using
      exceptional_next n w d ell hell word c hc f P hs hb hx

lemma payment_selected (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    select (P.faceClass (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad p)) = true := by
  obtain ⟨F,hF⟩ := p.2.property.1
  have hf := mark_top_face n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  have hx : select (P.faceClass p.2.val.1.2.val) = true := by rw [← hf]; exact F.property.1
  unfold paymentRawDart
  split_ifs <;> simpa only [P.faceClass_apply,P.faceClass_previous] using hx

lemma payment_param_injective : Function.Injective (fun p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad =>
    (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p,paymentBool n w d ell hell word c hc f P select hs hm hred hrad p)) := by
  rintro ⟨b,⟨⟨⟨z,x⟩,o⟩,hp⟩⟩ ⟨a,⟨⟨⟨y,k⟩,q⟩,hq⟩⟩ hh
  obtain ⟨hx,ho⟩ := Prod.mk.inj hh
  have hv := apexCorner_injective n w d ell hell word c hc f P select (a₁ := ⟨b,z,x⟩) (a₂ := ⟨a,y,k⟩) hx
  have hb : b = a := congrArg Sigma.fst hv
  subst a
  have hz : z = y := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj_iff.mp hv).2)
  subst y
  have hk : x = k := Subtype.ext hx
  subst k
  change o = q at ho
  subst q
  rfl

include hb in
lemma paymentRawDart_injective : Function.Injective
    (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q he
  apply payment_param_injective n w d ell hell word c hc f P select hs hm hred hrad
  have ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p =
      paymentBool n w d ell hell word c hc f P select hs hm hred hrad q := by
    obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨b,hb⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    have hh := congrArg P.index he
    rw [ha,hb] at hh
    have hh' := congrArg (fun t : Top n w × MacroGraph.graph.Dart => t.2.fst) (Sum.inl.inj (Sum.inl.inj hh))
    cases hp : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p <;>
      cases hq : paymentBool n w d ell hell word c hc f P select hs hm hred hrad q <;>
      simp only [hp,hq,Bool.false_eq_true,↓reduceIte] at hh' ⊢
    all_goals cases hh'
  refine Prod.ext ?_ ho
  unfold paymentRawDart at he
  rw [ho] at he
  split_ifs at he
  · exact P.pairing.face.injective he
  · exact (P.pairing.face⁻¹).injective ((P.pairing.face⁻¹).injective he)

lemma allPaymentIndex_card :
    Fintype.card (AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natPaymentIndex_card
    (fun b => indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
