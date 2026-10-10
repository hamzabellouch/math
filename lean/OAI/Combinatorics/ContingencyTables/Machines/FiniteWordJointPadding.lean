import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartPadding

namespace OAI

/-! # Padding preserves the joint law with every unused suffix bit -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped BigOperators Classical
noncomputable section

theorem SameLaw.append_joint {Z : Type*} {n q : ℕ}
    {f : (Fin n → Bool) → Z} {g : (Fin q → Bool) → Z}
    (h : SameLaw f g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
        (f (splitWordEquiv n t bits).1,(splitWordEquiv n t bits).2))
      (fun bits : Fin (q+t) → Bool =>
        (g (splitWordEquiv q t bits).1,(splitWordEquiv q t bits).2)) := by
  have hp := h.prod (show SameLaw (fun bits : Fin t → Bool => bits) (fun bits : Fin t → Bool => bits)
    from fun _ => rfl)
  intro phi
  have hl := uniformAverage_equiv (splitWordEquiv n t)
    (fun p : (Fin n → Bool)×(Fin t → Bool) => phi (f p.1,p.2))
  have hr := uniformAverage_equiv (splitWordEquiv q t)
    (fun p : (Fin q → Bool)×(Fin t → Bool) => phi (g p.1,p.2))
  exact hl.trans ((hp phi).trans hr.symm)

theorem restart_append_joint_sameLaw
    (base : List CompanionRestartProgram.Stage×List ℕ) (n q : ℕ)
    (hn : (∑ i : Fin base.1.length,CompanionRestartProgram.widthAt base i.val)=n)
    (g : (Fin q → Bool) → List ℕ)
    (h : SameLaw (fun bits : Fin n → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
        (CompanionRestartProgram.output (base,List.ofFn bits),(splitWordEquiv n t bits).2))
      (fun bits : Fin (q+t) → Bool =>
        (g (splitWordEquiv q t bits).1,(splitWordEquiv q t bits).2)) := by
  have hp := h.append_joint t
  have he (bits : Fin (n+t) → Bool) :
      CompanionRestartProgram.output (base,List.ofFn bits)=
        CompanionRestartProgram.output (base,List.ofFn (splitWordEquiv n t bits).1) := by
    have hs := (CompanionRestartProgram.output_take_sum base (List.ofFn bits)).symm
    rw [hn,DensePrograms.ofFn_split_take] at hs
    exact hs
  intro phi
  simp_rw [he]
  exact hp phi

/-- Flattening the first two independent blocks preserves their joint
law with the untouched third block. -/
theorem nested_word_joint {Z : Type*} (a b t : ℕ)
    (f : (Fin a → Bool) → (Fin b → Bool) → Z) :
    SameLaw (fun bits : Fin (a+(b+t)) → Bool =>
      (f (splitWordEquiv a (b+t) bits).1
        (splitWordEquiv b t (splitWordEquiv a (b+t) bits).2).1,
        (splitWordEquiv b t (splitWordEquiv a (b+t) bits).2).2))
      (fun bits : (Fin (a+b) → Bool)×(Fin t → Bool) =>
        (f (splitWordEquiv a b bits.1).1 (splitWordEquiv a b bits.1).2,bits.2)) := by
  intro phi
  have houter := uniformAverage_equiv (splitWordEquiv a (b+t))
    (fun p : (Fin a → Bool)×(Fin (b+t) → Bool) =>
      phi (f p.1 (splitWordEquiv b t p.2).1,(splitWordEquiv b t p.2).2))
  have hinner (u : Fin a → Bool) := uniformAverage_equiv (splitWordEquiv b t)
    (fun p : (Fin b → Bool)×(Fin t → Bool) => phi (f u p.1,p.2))
  have hfirst := uniformAverage_equiv (splitWordEquiv a b)
    (fun p : (Fin a → Bool)×(Fin b → Bool) =>
      uniformAverage (fun tail : Fin t → Bool => phi (f p.1 p.2,tail)))
  rw [uniformAverage_prod] at hfirst
  rw [uniformAverage_prod]
  refine houter.trans ?_
  rw [uniformAverage_prod]
  calc
    _ = uniformAverage (fun u : Fin a → Bool =>
        uniformAverage (fun v : Fin b → Bool =>
          uniformAverage (fun tail : Fin t → Bool => phi (f u v,tail)))) := by
      apply congrArg uniformAverage
      funext u
      exact (hinner u).trans (uniformAverage_prod _)
    _ = _ := hfirst.symm

end
end ContingencyTables.FiniteObservableTransport

end OAI
