import OAI.Computability.TypeSystem.Substitution

namespace OAI

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Value
variable {Ω C hno}
@[simp] theorem asPlus_plus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) false)
    (p : Plus (hw := hw) Ω C hno) : asPlus hT ⟨.plus p,hT⟩ = p :=
  RawValue.plus.inj (asPlus_spec hT ⟨.plus p,hT⟩).symm
@[simp] theorem asMinus_minus {T : Expr S} (hT : FreeLayer P C (Ω.profile T) true)
    (p : Minus (hw := hw) Ω C hno) : asMinus hT ⟨.minus p,hT⟩ = p :=
  RawValue.minus.inj (asMinus_spec hT ⟨.minus p,hT⟩).symm
end Value

theorem plain_beta (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (act : LambdaAction (hw := hw) Ω C hno T) (a : FrameKey Ω C T)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p) :
    plainApply Ω C hno T hT (plainLambda Ω C hno T hT act) a p hp = act a p hp := by
  simp only [plainApply,plainLambda,Value.asPlain_plain,Equiv.apply_symm_apply]
  simp only [ActualPlainKey.payload_parameters]
  exact Value.plain_asPlain (ActualPlain.Key.target hw (a.plainKey hT)) (act a p hp)

theorem exitValue_tag (T : ActiveType Ω C) (hT : PlainLayer P C (Ω.profile T.type))
    (v : Value (hw := hw) Ω C hno T.type) :
    exitValue Ω C hno T (some (tagPlain Ω C hno T hT v)) = v := by
  simp only [exitValue,tagPlain_spec,project_valid]

theorem lambdaExit_parameter {X : Type u}
    (decode : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X →
      Option (RawValue (hw := hw) Ω C hno))
    (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (q : FreeObservations.Payload (PlainValue (hw := hw) Ω C hno) X) (hq : decode q = p)
    (ht : PlainLayer P C (Ω.profile (a.target hw).type)) :
    lambdaExit Ω C hno decode T act (a.argument,q) =
      some (tagPlain Ω C hno (a.target hw) ht (act a p hp)) := by
  have hg : Gate Ω C hno T a.argument (decode q) true :=
    ⟨a,rfl,hq.symm ▸ hp,⟨fun _ => rfl,fun _ => ht⟩⟩
  simp only [lambdaExit,dite_eq_left hg]
  subst p
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (decode q))
        (htk : PlainLayer P C (Ω.profile (k.target hw).type)),
      some (tagPlain Ω C hno (k.target hw) htk (act k (decode q) hpk)) =
        some (tagPlain Ω C hno (a.target hw) ht (act a (decode q) hp)) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.plain

theorem plusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : PlusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : plusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act q = Value.asPlus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (plusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [plusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (plusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.profile (k.target hw).type)),
      Value.asPlus (k.free_target hT htk) (act k (plusPayload Ω C hno v) hpk) =
        Value.asPlus (a.free_target hT ht) (act a (plusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem plusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act (a.argument,a.plusParameter hT p hp) =
      Value.asPlus (a.free_target hT ht) (act a p hp) :=
  plusContinue_gate Ω C hno T hT act a _ rfl p hp (a.plusPayload_parameter hT p hp) ht

theorem minusContinue_gate (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (q : MinusFrame (hw := hw) Ω C hno) (hqa : q.1 = a.argument)
    (p : Option (RawValue (hw := hw) Ω C hno)) (hp : PayloadFits Ω C hno a.domain p)
    (hq : minusPayload Ω C hno q.2 = p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act q = Value.asMinus (a.free_target hT ht) (act a p hp) := by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg : Gate Ω C hno T a.argument (minusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [minusContinue,dite_eq_left hg]
  have H : ∀ (k : FrameKey Ω C T), k = a →
      ∀ (hpk : PayloadFits Ω C hno k.domain (minusPayload Ω C hno v))
        (htk : ¬ PlainLayer P C (Ω.profile (k.target hw).type)),
      Value.asMinus (k.free_target hT htk) (act k (minusPayload Ω C hno v) hpk) =
        Value.asMinus (a.free_target hT ht) (act a (minusPayload Ω C hno v) hp) := by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain

 theorem minusContinue_parameter (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p)
    (ht : ¬ PlainLayer P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act (a.argument,a.minusParameter hT p hp) =
      Value.asMinus (a.free_target hT ht) (act a p hp) :=
  minusContinue_gate Ω C hno T hT act a _ rfl p hp (a.minusPayload_parameter hT p hp) ht

theorem plusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) false) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : PlusFrame (hw := hw) Ω C hno) :
    (plusLambda Ω C hno T hT act).slice a = plusContinue Ω C hno T hT act a := by
  rfl

theorem minusLambda_slice (T : ActiveType Ω C)
    (hT : FreeLayer P C (Ω.profile T.type) true) (act : LambdaAction (hw := hw) Ω C hno T)
    (a : MinusFrame (hw := hw) Ω C hno) :
    (minusLambdaBehavior Ω C hno T hT act).slice a =
      FreeObservations.behavior _ _ _ _ (minusContinue Ω C hno T hT act a) := by
  rfl

/-- The raw lambda equation. The sole representability premise is supplied
below from the proved uniform finite-bound lemma for an actual body tree. -/
theorem lambda_beta (T : ActiveType Ω C) (act : LambdaAction (hw := hw) Ω C hno T)
    (hr : ∀ hT : FreeLayer P C (Ω.profile T.type) true,
      ∃ x, FreeObservations.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act)
    (a : FrameKey Ω C T) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno T (lambdaValue Ω C hno T act) a p hp = act a p hp := by
  by_cases hT : PlainLayer P C (Ω.profile T.type)
  · simp only [applyValue,lambdaValue,dite_eq_left hT]
    exact plain_beta Ω C hno T hT act a p hp
  · by_cases hF : FreeLayer P C (Ω.profile T.type) false
    · by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_left hA,Value.asPlus_plus,plusLambda]
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.plusPayload_parameter hF p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_left hF,dite_eq_right hA,Value.asPlus_plus]
        apply Subtype.ext
        change RawValue.plus ((plusLambda Ω C hno T hF act).slice
          (a.argument,a.plusParameter hF p hp)) = _
        rw [plusLambda_slice,plusContinue_parameter Ω C hno T hF act a p hp hA]
        exact (Value.asPlus_spec (a.free_target hF hA) (act a p hp)).symm
    · have hM : FreeLayer P C (Ω.profile T.type) true := by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      have hb := packMinus_spec Ω C hno (minusLambdaBehavior Ω C hno T hM act) (hr hM)
      by_cases hA : PlainLayer P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_left hA,Value.asMinus_minus]
        rw [hb]
        change exitValue Ω C hno (a.target hw)
          (lambdaExit Ω C hno (minusPayload Ω C hno) T act (a.argument,a.minusParameter hM p hp)) = _
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.minusPayload_parameter hM p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dite_eq_right hT,dite_eq_right hF,dite_eq_right hA,Value.asMinus_minus]
        apply Subtype.ext
        change RawValue.minus (FreeObservations.minusSlice
          (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hM act))
          (a.argument,a.minusParameter hM p hp)) = _
        rw [Value.asMinus_spec (a.free_target hM hA) (act a p hp)]
        apply congrArg RawValue.minus
        apply FreeObservations.behavior_injective (topBase Ω) none
        rw [FreeObservations.behavior_minusSlice,hb,minusLambda_slice,
          minusContinue_parameter Ω C hno T hM act a p hp hA]

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {T : Expr S}
theorem abstraction_beta {D m E : Expr S} {s : S} (h : HasType P Γ (.lam D m) T)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hc : Converts T (.pi D E))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E) {B : Nat → Nat}
    (hub : Uniform Ω C hno eb B) (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpp : PayloadFits Ω C hno a.domain p) :
    applyValue Ω C hno (e.activeType h ha) ((abstraction h hp hc eb e).val ha) a p hpp =
      abstractionAction h hp hc eb e ha a p hpp := by
  apply lambda_beta
  intro hT
  obtain ⟨k,hk⟩ := e.exists_bound
  obtain ⟨v,_,hv⟩ := minusLambda_representable Ω C hno hT (by have := hub.growth k; omega)
    (abstractionAction_bounded h hp hc eb hub k e hk ha)
    (fun a p p' hp' hp'' hbp hbp' hpp =>
      abstractionAction_level h hp hc eb hub k e e hk hk (e.level_refl _) ha ha a a rfl
        p p' hp' hp'' hbp hbp' hpp)
  exact ⟨v,hv⟩

theorem application_frame {f n A B : Expr S} (h : HasType P Γ (.app f n) T)
    (hf : HasType P Γ f (.pi A B)) (hn : HasType P Γ n A) (hc : Converts T (B.instantiate n))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi A B))
    (en : Evaluator (hw := hw) Ω C hno Γ n A)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images).normalForm))
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ∃ (k : FrameKey Ω C (e.activeType hf hF))
      (hp : PayloadFits Ω C hno k.domain (en e).parameter),
      k.argument = (n.subst e.images).normalForm ∧ k.domain = (A.subst e.images).normalForm ∧
      ((application h hf hn hc ef en e).val ha).val =
        (applyValue Ω C hno _ ((ef e).val hF) k (en e).parameter hp).val := by
  unfold application baseResult applicationValue
  simp only [dite_eq_left hF]
  exact ⟨_,(en e).parameter_fits,rfl,rfl,rfl⟩

theorem abstractionAction_raw {D m E : Expr S} {s : S}
    (h : HasType P Γ (.lam D m) T) (hp : HasType P Γ (.pi D E) (.sort s))
    (hc : Converts T (.pi D E)) (b : TypingTree P (D :: Γ) m E)
    (hC : IsComponent (PrimaryEdge P) C)
    (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (k : FrameKey Ω C (e.activeType h ha))
    (p : Option (RawValue (hw := hw) Ω C hno)) (hpp : PayloadFits Ω C hno k.domain p)
    (n : Expr S) (hn : Ω.HasType n (D.subst e.images))
    (hp' : PayloadFits Ω C hno (D.subst e.images).normalForm p)
    (hkn : Converts k.argument n)
    (ha' : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n e.images)).normalForm)) :
    (abstractionAction h hp hc (preEvaluate Ω C hno b) e ha k p hpp).val =
      ((preEvaluate Ω C hno b (e.cons hn p hp')).val ha').val := by
  unfold abstractionAction
  apply val_congr
  apply (preEvaluate_compatible Ω C hno hC b _ _ ?_).1
  constructor
  · intro i hi
    cases i with
    | zero => exact hkn
    | succ i => exact .refl _
  · intro i hi
    cases i <;> rfl
end PreResult

 theorem application_abstraction_beta {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasType P Γ (.app (.lam D m) n) T)
    (hf : HasType P Γ (.lam D m) (.pi A B))
    (d : TypingTree P Γ D (.sort a)) (b : TypingTree P (D :: Γ) m E)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hcF : Converts (.pi A B) (.pi D E))
    (nt : TypingTree P Γ n A) (hc : Converts T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) (e : Environment (hw := hw) Ω C hno Γ)
    (hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images).normalForm))
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)) :
    ∃ (hnD : Ω.HasType (n.subst e.images) (D.subst e.images))
      (hpp : PayloadFits Ω C hno (D.subst e.images).normalForm (preEvaluate Ω C hno nt e).parameter)
      (hb : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm)),
      (Ω.profile (D.subst e.images) ∈ ObservationLayers P C → ActiveLayer P C (Ω.profile (D.subst e.images))) ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno b (e.cons hnD (preEvaluate Ω C hno nt e).parameter hpp)).val hb).val := by
  obtain ⟨k,hpk,hkn,hkD,hval⟩ := PreResult.application_frame ht hf nt.typing hc
    (preEvaluate Ω C hno (.abstraction hf d b hp hcF)) (preEvaluate Ω C hno nt) e hF ha
  have hnD : HasType P Γ n D := .conversion nt.typing d.typing hcF.product_compatibility.1
  have hAD := e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
  have hpp : PayloadFits Ω C hno (D.subst e.images).normalForm (preEvaluate Ω C hno nt e).parameter :=
    hAD ▸ (preEvaluate Ω C hno nt e).parameter_fits
  have hbT : Converts T (E.instantiate n) := .trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  have heT := e.type_convert_eq ht (b.typing.instantiate hnD) hbT
  have heT' : (T.subst e.images).normalForm =
      (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm := by
    simpa only [Expr.instantiate,Expr.subst_compSub,Expr.comp_single] using heT
  have hb : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).normalForm) := heT' ▸ ha
  refine ⟨ContextTower.HasType.subst hnD e.typed,hpp,hb,?_,?_⟩
  · intro hH
    have heD : Ω.profile k.domain = Ω.profile (D.subst e.images) := by rw [hkD,hAD,Ω.profile_normalForm]
    rw [← heD]
    exact k.domain_active hw (heD.symm ▸ hH)
  · obtain ⟨F,hB⟩ := preEvaluate_uniform Ω C hno hC b
    refine hval.trans ?_
    rw [show ((preEvaluate Ω C hno (.abstraction hf d b hp hcF) e).val hF) =
      (PreResult.abstraction hf hp hcF (preEvaluate Ω C hno b) e).val hF from rfl,
      PreResult.abstraction_beta hf hp hcF _ hB e hF k _ hpk]
    apply PreResult.abstractionAction_raw hf hp hcF b hC e hF k _ hpk
      (n.subst e.images) (ContextTower.HasType.subst hnD e.typed) hpp _ hb
    rw [hkn]
    exact .symm _ _ (Expr.normalForm_spec ((ContextTower.HasType.subst nt.typing e.typed).weaklyNormalizing hw)).1.converts

/-- Exact tree transport at a fixed root expectation. Only good observations
are equated; raw environments and values are otherwise unrestricted. -/
structure GoodTransport {Γ : List (Expr S)} {M N T : Expr S}
    (t : TypingTree P Γ M T) (t' : TypingTree P Γ N T) : Prop where
  val : ∀ (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
    ValGood Ω C t e.images → ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno t e).val ha).val = ((preEvaluate Ω C hno t' e).val ha).val
  read : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C t e.images →
    ReadGood Ω C t' e.images ∧ (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val

 theorem baseRead_transport {Γ : List (Expr S)} {M N T : Expr S}
    (ht : HasType P Γ M T) (t' : TypingTree P Γ N T)
    (e : Environment (hw := hw) Ω C hno Γ)
    (hMN : (M.subst e.images).normalForm = (N.subst e.images).normalForm)
    (hne : Neutral M → Neutral N)
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm) (G : Prop)
    (hr : baseGood Ω C M T e.images G)
    (hv : ∀ ha, G → ValGood Ω C t' e.images ∧ (v ha).val = ((preEvaluate Ω C hno t' e).val ha).val) :
    ReadGood Ω C t' e.images ∧ (PreResult.baseRead ht v).val = (preEvaluate Ω C hno t' e).read.val := by
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (N.subst e.images).normalForm ∈ C := hMN ▸ hm
    obtain ⟨s,hs,hsC,hval,hn⟩ := hr (by simpa only [Ω.profile_normalForm] using hm)
    subst T
    by_cases ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)
    · have hvg := hv ha (hval (by simpa only [Ω.profile_normalForm] using ha))
      refine ⟨(readGood_active_iff Ω C t' (by simpa only [Ω.profile_normalForm] using hm') hsC
        (by simpa only [Ω.profile_normalForm] using ha)).mpr hvg.1,?_⟩
      refine Eq.trans (PreResult.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEvaluate_read_base Ω C hno t' e hm' hsC ha).symm)
      rw [hvg.2]
      exact congrArg (fun X : ActualType Ω =>
        ((RawValue.base Ω C hno ((preEvaluate Ω C hno t' e).val ha).val) X).val) (Subtype.ext hMN)
    · have hn' := hne (hn (by simpa only [Ω.profile_normalForm] using ha))
      refine ⟨neutral_readGood Ω C t' hn' e.images hsC (by simpa only [Expr.subst,Ω.profile_sort,Ω.profile_normalForm] using ha),?_⟩
      have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hsC⟩
      rw [preEvaluate_neutral_read_inactive Ω C hno t' e hn' ha]
      simp only [PreResult.baseRead,dite_eq_left hm,dite_eq_left hex,dite_eq_right ha]
      exact congrArg (Candidates.Top Ω) hMN
  · have hm' : Ω.profile (N.subst e.images).normalForm ∉ C := hMN ▸ hm
    refine ⟨readGood_outside Ω C t' e.images (by simpa only [Ω.profile_normalForm] using hm'),?_⟩
    rw [preEvaluate_read_outside Ω C hno t' e hm']
    simp only [PreResult.baseRead,dite_eq_right hm]
    exact congrArg (Candidates.Top Ω) hMN

 theorem root_transport {Γ : List (Expr S)} {D m E A B n T : Expr S} {a s : S}
    (ht : HasType P Γ (.app (.lam D m) n) T)
    (hf : HasType P Γ (.lam D m) (.pi A B))
    (d : TypingTree P Γ D (.sort a)) (b : TypingTree P (D :: Γ) m E)
    (hp : HasType P Γ (.pi D E) (.sort s)) (hcF : Converts (.pi A B) (.pi D E))
    (nt : TypingTree P Γ n A) (hc : Converts T (B.instantiate n))
    (hC : IsComponent (PrimaryEdge P) C) :
    ∃ t' : TypingTree P Γ (m.instantiate n) T,
      GoodTransport (hw := hw) Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) t' := by
  have hnD : HasType P Γ n D := .conversion nt.typing d.typing hcF.product_compatibility.1
  let ntD := nt.retarget hnD (.symm _ _ hcF.product_compatibility.1)
  let ts := TypingTree.StoredSubstitution.single ntD
  let bt := b.subst ht.valid (Expr.single n) ts
  have ht' := ht.subject_reduction (.head D m n)
  have hc' : Converts T (E.instantiate n) := .trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  let t' := bt.retarget ht' hc'
  refine ⟨t',?_⟩
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.application ht (.abstraction hf d b hp hcF) nt hc) e.images →
      ValGood Ω C t' e.images ∧
      ((preEvaluate Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEvaluate Ω C hno t' e).val ha).val := by
    intro e ha hg
    have hF : ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) := by
      by_contra hh
      change (if ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
      rw [ite_eq_right hh] at hg
      cases hg with | app hf => cases hf
    change (if ActiveLayer P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
    rw [ite_eq_left hF] at hg
    obtain ⟨hraw,hpp,hbody,hguard,hbeta⟩ := application_abstraction_beta Ω C hno ht hf d b hp hcF nt hc hC e
      (by simpa only [Ω.profile_normalForm] using hF) ha
    let er := e.cons (ContextTower.HasType.subst hnD e.typed) (preEvaluate Ω C hno ntD e).parameter
      (preEvaluate Ω C hno ntD e).parameter_fits
    have herimages : er.images = Expr.consSub (n.subst e.images) e.images := by
      funext i; cases i <;> rfl
    have hpEq : (preEvaluate Ω C hno nt e).parameter = (preEvaluate Ω C hno ntD e).parameter :=
      preEvaluate_retarget_parameter Ω C hno nt hnD (.symm _ _ hcF.product_compatibility.1) e
    have heren : (e.cons hraw (preEvaluate Ω C hno nt e).parameter hpp).Compatible er := by
      constructor
      · intro i hi; exact .refl _
      · intro i hi; cases i with
        | zero => exact hpEq
        | succ i => rfl
    have hgoodB : ValGood Ω C b er.images := hg.1 (n.subst e.images) hraw
      (by simpa only [Ω.profile_normalForm] using hbody)
    have heT := e.type_convert_eq ht bt.typing hc'
    have haBt : ActiveLayer P C (Ω.profile ((E.instantiate n).subst e.images).normalForm) := heT ▸ ha
    have hsGuard : SubstitutionGuard Ω C (D :: Γ) (Expr.single n) er.images := single_guard Ω C e.images hguard
    have hgoodN : GoodReplacement Ω C ts e.images := single_goodReplacement Ω C ntD e.images (by
      intro hD
      apply (valGood_retarget Ω C nt hnD (.symm _ _ hcF.product_compatibility.1) e.images).mpr
      apply hg.2
      have heD := e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
      rw [← Ω.profile_normalForm,heD,Ω.profile_normalForm]
      exact hD)
    have hgoodBt : ValGood Ω C bt e.images := (goodness_subst Ω C hw b ht.valid (Expr.single n) ts e.images e.typed
      (by simpa only [Expr.comp_single,←herimages] using hsGuard) hgoodN).1
      (by simpa only [Expr.comp_single,Ω.profile_normalForm] using hbody)
      (by simpa only [Expr.comp_single,←herimages] using hgoodB)
    refine ⟨(valGood_retarget Ω C bt ht' hc' e.images).mpr hgoodBt,?_⟩
    refine hbeta.trans (Eq.trans ?_ (preEvaluate_retarget_val Ω C hno bt ht' hc' e haBt ha))
    refine Eq.trans (PreResult.val_congr _ _ (preEvaluate_compatible Ω C hno hC b _ _ heren).1 hbody hbody) ?_
    exact (preEvaluate_subst Ω C hno b ht.valid (Expr.single n) ts er e (single_assigned Ω C hno ntD e) hsGuard).1
      hbody haBt hgoodB
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht t' e
    (e.expression_convert_eq ht ht' (.rel _ _ (.head D m n)))
    (fun h => by cases h with | app hf => cases hf) _ _ hr
  exact hval e

namespace Environment
variable {Ω C hno} {Γ : List (Expr S)}
@[simp] theorem cons_images (e : Environment (hw := hw) Ω C hno Γ) {D n : Expr S}
    (hn : Ω.HasType n (D.subst e.images)) p hp :
    (e.cons hn p hp).images = Expr.consSub n e.images := by
  funext i; cases i <;> rfl
end Environment

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N T : Expr S}
 theorem refl (t : TypingTree P Γ M T) : GoodTransport (hw := hw) Ω C hno t t :=
  ⟨fun _ _ h => ⟨h,rfl⟩,fun _ h => ⟨h,rfl⟩⟩
 theorem parameter_eq {t : TypingTree P Γ M T} {t' : TypingTree P Γ N T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (e : Environment (hw := hw) Ω C hno Γ)
    (hg : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) → ValGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' e).parameter := by
  apply PreResult.parameter_congr _ _ rfl
  intro ha ha'
  exact (h.val e ha (hg ha)).2
end GoodTransport

 theorem application_transport {Γ : List (Expr S)} {f n f' n' D E T : Expr S}
    (ht : HasType P Γ (.app f n) T) (ht' : HasType P Γ (.app f' n') T)
    (ft : TypingTree P Γ f (.pi D E)) (ft' : TypingTree P Γ f' (.pi D E))
    (nt : TypingTree P Γ n D) (nt' : TypingTree P Γ n' D)
    (hc : Converts T (E.instantiate n)) (hc' : Converts T (E.instantiate n'))
    (hf : GoodTransport (hw := hw) Ω C hno ft ft') (hn : GoodTransport (hw := hw) Ω C hno nt nt')
    (hff : Converts f f') (hnn : Converts n n') (hne : Neutral f → Neutral f') :
    GoodTransport (hw := hw) Ω C hno (.application ht ft nt hc) (.application ht' ft' nt' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.application ht ft nt hc) e.images →
      ValGood Ω C (.application ht' ft' nt' hc') e.images ∧
      ((preEvaluate Ω C hno (.application ht ft nt hc) e).val ha).val =
      ((preEvaluate Ω C hno (.application ht' ft' nt' hc') e).val ha).val := by
    intro e ha hg
    change (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) at hg
    change (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) ∧ _
    by_cases hF : ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images))
    · rw [ite_eq_left hF] at hg ⊢
      have hFa : ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images).normalForm) := by
        simpa only [Ω.profile_normalForm] using hF
      refine ⟨⟨(hf.val e hFa hg.1).1,fun haD => (hn.val e
        (by simpa only [Ω.profile_normalForm] using haD) (hg.2 haD)).1⟩,?_⟩
      apply PreResult.application_val_congr ht ht' ft.typing ft'.typing nt.typing nt'.typing hc hc'
        _ _ _ _ e e rfl rfl (e.expression_convert_eq nt.typing nt'.typing hnn)
      · exact fun _ _ => (hf.val e hFa hg.1).2
      · exact hn.parameter_eq e (fun haD => hg.2 (by simpa only [Ω.profile_normalForm] using haD))
    · rw [ite_eq_right hF] at hg ⊢
      refine ⟨?_,?_⟩
      · cases hg with | app hg => exact .app (hne hg)
      · have hFa : ¬ ActiveLayer P C (Ω.profile ((Expr.pi D E).subst e.images).normalForm) := by
          simpa only [Ω.profile_normalForm] using hF
        simp only [preEvaluate,PreResult.application,PreResult.baseResult,PreResult.applicationValue,dite_eq_right hFa]
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.application ht' ft' nt' hc') e
    (e.expression_convert_eq ht ht' (.app hff hnn))
    (fun hh => by cases hh with | app hh => exact .app (hne hh)) _ _ hr
  exact hval e

 theorem abstraction_transport {Γ : List (Expr S)} {D m E D' m' E' T : Expr S} {a a' s s' : S}
    (ht : HasType P Γ (.lam D m) T) (ht' : HasType P Γ (.lam D' m') T)
    (d : TypingTree P Γ D (.sort a)) (d' : TypingTree P Γ D' (.sort a'))
    (b : TypingTree P (D :: Γ) m E) (b' : TypingTree P (D' :: Γ) m' E')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Γ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T (.pi D' E'))
    (hD : Converts D D') (hm : Converts m m') (hE : Converts E E')
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e.images))
      p hpp hpp' ha ha', ValGood Ω C b (e.cons hn p hpp).images →
        ValGood Ω C b' (e.cons hn' p hpp').images ∧
        ((preEvaluate Ω C hno b (e.cons hn p hpp)).val ha).val =
        ((preEvaluate Ω C hno b' (e.cons hn' p hpp')).val ha').val) :
    GoodTransport (hw := hw) Ω C hno (.abstraction ht d b hp hc) (.abstraction ht' d' b' hp' hc') := by
  have hval : ∀ (e : Environment (hw := hw) Ω C hno Γ)
      (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)),
      ValGood Ω C (.abstraction ht d b hp hc) e.images →
      ValGood Ω C (.abstraction ht' d' b' hp' hc') e.images ∧
      ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
      ((preEvaluate Ω C hno (.abstraction ht' d' b' hp' hc') e).val ha).val := by
    intro e ha hg
    have hnold {n : Expr S} (hn : Ω.HasType n (D'.subst e.images)) : Ω.HasType n (D.subst e.images) :=
      .conversion hn (ContextTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n : Expr S) (hn : Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).normalForm = (E'.subst (Expr.consSub n e.images)).normalForm :=
      Expr.normalForm_converts ((ContextTower.HasType.subst b.typing (e.typed.cons (hnold hn))).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst b'.typing (e.typed.cons hn)).type_weaklyNormalizing hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨?_,?_⟩
    · intro n hn ha'
      have haold : ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n e.images)).normalForm) := by
        rw [hEeq n hn,Ω.profile_normalForm]; exact ha'
      obtain ⟨pa,hpD⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hDD := e.expression_convert_eq d.typing d'.typing hD
      have hpD' : PayloadFits Ω C hno (D'.subst e.images).normalForm pa := hDD ▸ hpD
      exact (hb e n (hnold hn) hn pa hpD hpD' haold
        (by simpa only [Ω.profile_normalForm,Environment.cons_images] using ha') (hg n (hnold hn)
          (by simpa only [Ω.profile_normalForm] using haold))).1
    · apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e rfl
      intro n n' hn hn' he p hpp hpp' haB haB'
      subst n'
      exact (hb e n hn hn' p hpp hpp' haB haB' (hg n hn
        (by simpa only [Ω.profile_normalForm,Environment.cons_images] using haB))).2
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.abstraction ht' d' b' hp' hc') e
    (e.expression_convert_eq ht ht' (.lam hD hm)) (fun hn => by cases hn) _ _ hr
  exact hval e

 theorem product_transport {Γ : List (Expr S)} {D E D' E' T : Expr S} {a q c : S}
    (ht : HasType P Γ (.pi D E) T) (ht' : HasType P Γ (.pi D' E') T)
    (d : TypingTree P Γ D (.sort a)) (d' : TypingTree P Γ D' (.sort a))
    (b : TypingTree P (D :: Γ) E (.sort q)) (b' : TypingTree P (D' :: Γ) E' (.sort q))
    (hr : P.rule a q c) (hc : Converts T (.sort c))
    (hD : Converts D D') (hE : Converts E E')
    (hd : ∀ (e : Environment (hw := hw) Ω C hno Γ), ReadGood Ω C d e.images →
      ReadGood Ω C d' e.images ∧ (preEvaluate Ω C hno d e).read.val = (preEvaluate Ω C hno d' e).read.val)
    (hb : ∀ (e : Environment (hw := hw) Ω C hno Γ) n
      (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e.images))
      p hpp hpp', ReadGood Ω C b (e.cons hn p hpp).images →
        ReadGood Ω C b' (e.cons hn' p hpp').images ∧
        (preEvaluate Ω C hno b (e.cons hn p hpp)).read.val =
        (preEvaluate Ω C hno b' (e.cons hn' p hpp')).read.val) :
    GoodTransport (hw := hw) Ω C hno (.product ht d b hr hc) (.product ht' d' b' hr hc) := by
  have hdata (e : Environment (hw := hw) Ω C hno Γ) :
      (D.subst e.images).normalForm = (D'.subst e.images).normalForm ∧
      (E.subst (Expr.liftSub e.images)).normalForm = (E'.subst (Expr.liftSub e.images)).normalForm := by
    have hpi := e.expression_convert_eq ht ht' (.pi hD hE)
    have hwp := (ContextTower.HasType.subst ht e.typed).weaklyNormalizing hw
    have hwp' := (ContextTower.HasType.subst ht' e.typed).weaklyNormalizing hw
    rw [Expr.subst,Expr.subst,Expr.normalForm_pi hwp.pi_domain hwp.pi_body,
      Expr.normalForm_pi hwp'.pi_domain hwp'.pi_body] at hpi
    exact Expr.pi.inj hpi
  have hchildren (e : Environment (hw := hw) Ω C hno Γ)
      (hg : ProductGood Ω C d b e.images) :
      ProductGood Ω C d' b' e.images ∧
      (PreResult.productCandidate d.typing b.typing hr (preEvaluate Ω C hno d) (preEvaluate Ω C hno b) e).val =
      (PreResult.productCandidate d'.typing b'.typing hr (preEvaluate Ω C hno d') (preEvaluate Ω C hno b') e).val := by
    have hnold {n : Expr S} (hn : Ω.HasType n (D'.subst e.images)) : Ω.HasType n (D.subst e.images) :=
      .conversion hn (ContextTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n : Expr S) (hn : Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).normalForm = (E'.subst (Expr.consSub n e.images)).normalForm :=
      Expr.normalForm_converts ((ContextTower.HasType.subst b.typing (e.typed.cons (hnold hn))).weaklyNormalizing hw)
        ((ContextTower.HasType.subst b'.typing (e.typed.cons hn)).weaklyNormalizing hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro hD'
      apply (hd e (hg.1 ?_)).1
      rw [← Ω.profile_normalForm,(hdata e).1,Ω.profile_normalForm]
      exact hD'
    · intro n hn hE'
      have hEold : Ω.profile (E.subst (Expr.consSub n e.images)) ∈ C := by
        rw [← Ω.profile_normalForm,hEeq n hn,Ω.profile_normalForm]; exact hE'
      obtain ⟨p,hp⟩ := PayloadFits.exists_of_actual (hw := hw) (C := C) (hno := hno) (e.actualExpression d.typing)
      have hp' : PayloadFits Ω C hno (D'.subst e.images).normalForm p := (hdata e).1 ▸ hp
      have hh := (hb e n (hnold hn) hn p hp hp' (by
        simpa only [Environment.cons_images] using hg.2 n (hnold hn) hEold)).1
      simpa only [Environment.cons_images] using hh
    · apply PreResult.productCandidate_congr d.typing b.typing hr d'.typing b'.typing hr _ _ _ _ e e
        (hdata e).1 (hdata e).2
      · intro hD
        exact (hd e (hg.1 (by simpa only [Ω.profile_normalForm] using hD))).2
      · intro n hn hn' p hp hp' hE
        exact (hb e n hn hn' p hp hp' (hg.2 n hn
          (by simpa only [Ω.profile_normalForm,Environment.cons_images] using hE))).2
  constructor
  · intro e ha hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hgate
      exact (hchildren e (hg ⟨hgate.1,by
        rw [← Ω.profile_normalForm,hM,Ω.profile_normalForm]; exact hgate.2⟩)).1
    · by_cases hs : ({c} : Set S) ∈ C
      · apply PreResult.product_val_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
          _ _ _ _ e e rfl hM Iff.rfl
        intro hm
        exact (hchildren e (hg ⟨hs,by simpa only [Ω.profile_normalForm] using hm⟩)).2
      · have hgate : ¬ (({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D E).subst e.images).normalForm ∈ C) :=
          fun h => hs h.1
        have hgate' : ¬ (({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D' E').subst e.images).normalForm ∈ C) :=
          fun h => hs h.1
        simp only [preEvaluate,PreResult.product,dite_eq_right hgate,dite_eq_right hgate']
  · intro e hg
    have hM := e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hm
      exact (hchildren e (hg (by rw [← Ω.profile_normalForm,hM,Ω.profile_normalForm]; exact hm))).1
    · apply PreResult.product_read_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
        _ _ _ _ e e hM
      intro hm
      exact (hchildren e (hg (by simpa only [Ω.profile_normalForm] using hm))).2

 theorem reduction_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTree P Γ M T) (hr : Beta M N) :
    ∃ t' : TypingTree P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr generalizing Γ T with
  | head D m n =>
      cases t with
      | application ht ft nt hc =>
          cases ft with
          | abstraction hf d b hp hcF =>
              exact root_transport Ω C hno ht hf d b hp hcF nt hc hC
  | app_left hr ih =>
      cases t with
      | application ht ft nt hc =>
          obtain ⟨ft',hft⟩ := ih ft
          have ht' := ht.subject_reduction (.app_left hr)
          exact ⟨.application ht' ft' nt hc,application_transport Ω C hno ht ht' ft ft' nt nt hc hc
            hft (.refl nt) (.rel _ _ hr) (.refl _) (fun hn => hn.beta hr)⟩
  | app_right hr ih =>
      cases t with
      | @application Γ f n D E T ht ft nt hc =>
          obtain ⟨nt',hnt⟩ := ih nt
          have ht' := ht.subject_reduction (.app_right hr)
          have hc' : Converts T (E.instantiate _) := .trans _ _ _ hc ((show Converts _ _ from .rel _ _ hr).instantiate_right E)
          exact ⟨.application ht' ft nt' hc',application_transport Ω C hno ht ht' ft ft nt nt' hc hc'
            (.refl ft) hnt (.refl _) (.rel _ _ hr) (fun hn => hn)⟩
  | @lam_domain D D' m hr ih =>
      cases t with
      | @abstraction Γ _ _ E a s T ht d b hp hc =>
          obtain ⟨d',_⟩ := ih d
          let hctx := ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b' := b.recontext hctx
          have ht' := ht.subject_reduction (.lam_domain hr)
          have hp' := hp.subject_reduction (.pi_domain hr)
          have hc' : Converts T (.pi D' E) := .trans _ _ _ hc (.rel _ _ (.pi_domain hr))
          refine ⟨.abstraction ht' d' b' hp' hc',abstraction_transport Ω C hno ht ht' d d' b b' hp hp'
            hc hc' (.rel _ _ hr) (.refl _) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (b.recontext hctx) (e.cons hn' p hpp').images).1
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · apply PreResult.val_congr
            exact (preEvaluate_recontext Ω C hno b hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).1
  | lam_body hr ih =>
      cases t with
      | abstraction ht d b hp hc =>
          obtain ⟨b',hb⟩ := ih b
          have ht' := ht.subject_reduction (.lam_body hr)
          refine ⟨.abstraction ht' d b' hp hc,abstraction_transport Ω C hno ht ht' d d b b' hp hp
            hc hc (.refl _) (.rel _ _ hr) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          exact hb.val (e.cons hn p hpp) ha hg
  | @pi_domain D D' E hr ih =>
      cases t with
      | @product Γ _ _ a b c T ht d bt hrule hc =>
          obtain ⟨d',hd⟩ := ih d
          let hctx := ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b' := bt.recontext hctx
          have ht' := ht.subject_reduction (.pi_domain hr)
          refine ⟨.product ht' d' b' hrule hc,product_transport Ω C hno ht ht' d d' bt b' hrule hc
            (.rel _ _ hr) (.refl _) hd.read ?_⟩
          intro e n hn hn' p hpp hpp' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (bt.recontext hctx) (e.cons hn' p hpp').images).2
            rw [goodness_recontext]
            simpa only [Environment.cons_images] using hg
          · exact (preEvaluate_recontext Ω C hno bt hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).2
  | pi_body hr ih =>
      cases t with
      | product ht d bt hrule hc =>
          obtain ⟨b',hb⟩ := ih bt
          have ht' := ht.subject_reduction (.pi_body hr)
          refine ⟨.product ht' d b' hrule hc,product_transport Ω C hno ht ht' d d bt b' hrule hc
            (.refl _) (.rel _ _ hr) (fun e hg => ⟨hg,rfl⟩) ?_⟩
          intro e n hn hn' p hpp hpp' hg
          exact hb.read (e.cons hn p hpp) hg

namespace GoodTransport
variable {Ω C hno} {Γ : List (Expr S)} {M N L T : Expr S}
 theorem trans {t : TypingTree P Γ M T} {t' : TypingTree P Γ N T} {t'' : TypingTree P Γ L T}
    (h : GoodTransport (hw := hw) Ω C hno t t') (h' : GoodTransport (hw := hw) Ω C hno t' t'') :
    GoodTransport (hw := hw) Ω C hno t t'' := by
  constructor
  · intro e ha hg
    have hh := h.val e ha hg
    have hh' := h'.val e ha hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
  · intro e hg
    have hh := h.read e hg
    have hh' := h'.read e hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
end GoodTransport

 theorem reduces_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M N T : Expr S} (t : TypingTree P Γ M T) (hr : Reduces M N) :
    ∃ t' : TypingTree P Γ N T, GoodTransport (hw := hw) Ω C hno t t' := by
  induction hr with
  | refl => exact ⟨t,.refl t⟩
  | tail _ h ih =>
      obtain ⟨t',ht⟩ := ih
      obtain ⟨t'',ht'⟩ := reduction_transport Ω C hno hC t' h
      exact ⟨t'',ht.trans ht'⟩

/-- The good part of any stored tree is transported to a normal stored tree. -/
theorem normalize_transport (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) :
    ∃ t' : TypingTree P Γ M.normalForm T, GoodTransport (hw := hw) Ω C hno t t' :=
  reduces_transport Ω C hno hC t (Expr.normalForm_spec (t.typing.weaklyNormalizing hw)).1

/-- An arbitrary good active value equals every normal-tree value at a
convertible expectation. This does not assume goodness of the target tree. -/
theorem good_normal_value (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M T U : Expr S} (t : TypingTree P Γ M T)
    (t' : TypingTree P Γ M.normalForm U) (hc : Converts T U)
    (e : Environment (hw := hw) Ω C hno Γ)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (U.subst e.images).normalForm))
    (hg : ValGood Ω C t e.images) :
    ((preEvaluate Ω C hno t e).val ha).val = ((preEvaluate Ω C hno t' e).val ha').val := by
  obtain ⟨tn,htn⟩ := normalize_transport Ω C hno hC t
  have he := (htn.val e ha hg).2
  have hn := (Expr.normalForm_spec (t.typing.weaklyNormalizing hw)).2
  exact he.trans (PreResult.val_congr _ _ ((normal_tree_independence Ω C hno tn hn t' e).1 hc) ha ha')

/-- An arbitrary good literal-sort Read equals its normal-syntax interpretation,
even for a different literal expected sort in a nonfunctional specification. -/
theorem good_normal_read (hC : IsComponent (PrimaryEdge P) C)
    {Γ : List (Expr S)} {M : Expr S} {s r : S} (t : TypingTree P Γ M (.sort s))
    (t' : TypingTree P Γ M.normalForm (.sort r))
    (e : Environment (hw := hw) Ω C hno Γ) (hg : ReadGood Ω C t e.images) :
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val := by
  obtain ⟨tn,htn⟩ := normalize_transport Ω C hno hC t
  have hn := (Expr.normalForm_spec (t.typing.weaklyNormalizing hw)).2
  exact (htn.read e hg).2.trans ((normal_tree_independence Ω C hno tn hn t' e).2 s r rfl rfl)
end PureTypeSystem.ObservationValues

end OAI
