import OAI.Combinatorics.Ryser.LineCover.Definitions

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [instFieldF : Field F] [instFintypeF : Fintype F] [instDecidableEqF : DecidableEq F]

abbrev CoverSample (L : Finset (AffineLine F)) (t : ℕ) :=
  (Fin t ⊕ Fin t) ↪ ↥L

def liftSample (L : Finset (AffineLine F)) {t : ℕ} (u : CoverSample L t) :
    LineTuple F t :=
  u.trans ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem liftSample_apply (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) :
    liftSample L u i = (u i).val := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF; rfl

theorem liftSample_mem (L : Finset (AffineLine F)) {t : ℕ}
    (u : CoverSample L t) (i : Fin t ⊕ Fin t) : liftSample L u i ∈ L := let _ := instFieldF; let _ := instFintypeF; let _ := instDecidableEqF;
  (u i).property

def CrossHit (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t)
    (p : Fin t × Fin t) : Prop :=
  ∃ x ∈ X, Incidence x (a (Sum.inl p.1)) ∧ Incidence x (a (Sum.inr p.2))

def crossHitCount (X : Finset (Point F)) {t : ℕ} (a : LineTuple F t) : ℕ :=
  (Finset.univ.filter (CrossHit X a)).card

end RyserCoveringCounterexample.LineCover

end

end OAI
