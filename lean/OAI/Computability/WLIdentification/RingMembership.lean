import OAI.Computability.WLIdentification.RingCodes

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

theorem hCoord_iff (_F : RingRealizer TP LP r rp R) (w : Word) (h : (R w).HName) (k : Σ h : (R w).HName, Fin ((R w).dimension h.1)) :
    Sum.inl k∈(R w).hCoords h ↔ k.1=h := by
  simp only [RingLayout.hCoords, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,hj⟩
    exact (congrArg Sigma.fst (Sum.inl.inj hj)).symm
  · intro eh
    rcases k with ⟨k,j⟩
    dsimp only at eh
    subst k
    exact ⟨j,rfl⟩

theorem vCoord_iff (_F : RingRealizer TP LP r rp R) (w : Word) (h : (R w).HName) (v : (R w).VName) :
    Sum.inr v∈(R w).hCoords h ↔ False := by
  simp [RingLayout.hCoords]

def memberEval (w : Word) (b c : ℕ) : Bool :=
  if b%2=0 then if c%2=0 then decide ((Nat.unpair (c/2)).1=b/2) else false
  else if c%2=0 then decide ((Nat.unpair (c/2)).1=F.leftCode w (b/2)) || decide ((Nat.unpair (c/2)).1=F.rightCode w (b/2))
  else decide (c/2=F.topCode (b/2)) || decide (c/2=F.bottomCode w (b/2))

theorem member_ee (w : Word) (b c : ℕ) : F.memberEval w (2*b) (2*c)=decide ((Nat.unpair c).1=b) := by
  simp [memberEval]
theorem member_eo (w : Word) (b c : ℕ) : F.memberEval w (2*b) (2*c+1)=false := by
  simp [memberEval]
theorem member_oe (w : Word) (b c : ℕ) : F.memberEval w (2*b+1) (2*c)=
    (decide ((Nat.unpair c).1=F.leftCode w b) || decide ((Nat.unpair c).1=F.rightCode w b)) := by
  simp [memberEval,AffineRealizer.odd_half]
theorem member_oo (w : Word) (b c : ℕ) : F.memberEval w (2*b+1) (2*c+1)=
    (decide (c=F.topCode b) || decide (c=F.bottomCode w b)) := by
  simp [memberEval,AffineRealizer.odd_half]

theorem memberEval_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : BoolPoly (fun S => F.memberEval (w S) (b S) (c S)) := by
  have hb2 := NatPoly.div hb (NatPoly.const 2)
  have hc2 := NatPoly.div hc (NatPoly.const 2)
  have hb0 := NatPoly.eqtest (NatPoly.mod hb (NatPoly.const 2)) (NatPoly.const 0)
  have hc0 := NatPoly.eqtest (NatPoly.mod hc (NatPoly.const 2)) (NatPoly.const 0)
  unfold memberEval
  apply BoolPoly.iteProp hb0
  · exact BoolPoly.iteProp hc0 (NatPoly.eqtest (NatPoly.unpair_fst hc2) hb2) (BoolPoly.const false)
  · apply BoolPoly.iteProp hc0
    · exact BoolPoly.or (NatPoly.eqtest (NatPoly.unpair_fst hc2) (F.leftCode_poly hw hb2))
        (NatPoly.eqtest (NatPoly.unpair_fst hc2) (F.rightCode_poly hw hb2))
    · apply BoolPoly.or
      · exact NatPoly.eqtest hc2 (NatPoly.pair (NatPoly.unpair_fst hb2)
          (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb2))
          (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb2)))))
      · exact NatPoly.eqtest hc2 (NatPoly.pair (NatPoly.unpair_fst hb2)
          (NatPoly.pair (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb2)))
          (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb2)))))

noncomputable def member : Test (F.bP.prod F.cP) (fun w x => decide (x.2∈(R w).coordinates x.1)) where
  eval w i := F.memberEval w (Nat.unpair i).1 (Nat.unpair i).2
  correct w x := by
    rcases x with ⟨b,c⟩
    change F.memberEval w (Nat.unpair (Nat.pair (F.bP.code w b) (F.cP.code w c))).1 (Nat.unpair (Nat.pair (F.bP.code w b) (F.cP.code w c))).2=_
    rw [Nat.unpair_pair]
    cases b with
    | inl h => cases c with
      | inl k =>
        rw [F.bP_inl,F.cP_inl,F.member_ee,Nat.unpair_pair]
        apply Bool.eq_iff_iff.mpr
        simp only [RingLayout.coordinates]
        simp only [decide_eq_true_eq]
        constructor
        · intro he
          exact decide_eq_true ((F.hCoord_iff w h k).mpr ((F.hP.code w).injective he))
        · intro he
          exact congrArg (F.hP.code w) ((F.hCoord_iff w h k).mp (of_decide_eq_true he))
      | inr v =>
        rw [F.bP_inl,F.cP_inr,F.member_eo]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.false_eq_true,decide_eq_true_eq,RingLayout.coordinates,F.vCoord_iff]
    | inr b => cases c with
      | inl k =>
        rw [F.bP_inr,F.cP_inl,F.member_oe,Nat.unpair_pair,F.leftCode_eq,F.rightCode_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true,decide_eq_true_eq,(F.hP.code w).injective.eq_iff,
          RingLayout.coordinates,Finset.mem_union,F.hCoord_iff,Finset.mem_insert,Finset.mem_singleton,Sum.inl_ne_inr,or_false]
      | inr v =>
        rw [F.bP_inr,F.cP_inr,F.member_oo,F.topCode_eq,F.bottomCode_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true,decide_eq_true_eq,(F.vP.code w).injective.eq_iff,
          RingLayout.coordinates,Finset.mem_union,F.vCoord_iff,Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,false_or]
  poly := F.memberEval_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.unpair_snd (NatPoly.var 1))

noncomputable def localData : Locals F.cP F.bP :=
  ⟨fun w => (R w).coordinates, fun w b => (R w).coordinates_card b, F.member⟩

end FinitePresentation.RingRealizer
end WLIdentification

end OAI
