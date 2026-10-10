import OAI.Computability.TypeSystem.Bounds

namespace OAI

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

theorem lambdaValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (act : LambdaAction (hw := hw) Ω C hno T) (act' : LambdaAction (hw := hw) Ω C hno U)
    (hr : ∀ (a : FrameKey Ω C T) (a' : FrameKey Ω C U), a.argument = a'.argument →
      ∀ p hp hp', (act a p hp).val = (act' a' p hp').val) :
    (lambdaValue Ω C hno T act).val = (lambdaValue Ω C hno U act').val := by
  have hu := ActiveType.ext hTU
  subst U
  have he : act = act' := by
    funext a p hp
    exact Subtype.ext (hr a a rfl p hp hp)
  rw [he]

theorem applyValue_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (v : Value (hw := hw) Ω C hno T.type) (v' : Value (hw := hw) Ω C hno U.type)
    (hvv : v.val = v'.val) (a : FrameKey Ω C T) (a' : FrameKey Ω C U)
    (hq : a.argument = a'.argument) (p p' : Option (RawValue (hw := hw) Ω C hno)) (hpp : p = p')
    (hp : PayloadFits Ω C hno a.domain p) (hp' : PayloadFits Ω C hno a'.domain p') :
    (applyValue Ω C hno T v a p hp).val = (applyValue Ω C hno U v' a' p' hp').val := by
  have hu := ActiveType.ext hTU
  subst U
  have hv : v = v' := Subtype.ext hvv
  have ha : a = a' := FrameKey.ext hq
  subst v'
  subst a'
  subst p'
  rfl

theorem withBase_congr {T U : ActiveType Ω C} (hTU : T.type = U.type)
    (b b' : Base Ω) (hbb : b = b') :
    (withBase (hw := hw) Ω C hno T b).val = (withBase Ω C hno U b').val := by
  have hu := ActiveType.ext hTU
  subst U
  subst b'
  rfl

theorem distinguished_congr {T U : ActiveType Ω C} (hTU : T.type = U.type) :
    (distinguished (hw := hw) Ω C hno T).val = (distinguished Ω C hno U).val := by
  have hu := ActiveType.ext hTU
  subst U
  rfl

namespace PreResult

section
variable {Ω C hno} {Γ Δ : List (Expr S)} {M M' T T' : Expr S}
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}

theorem parameter_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hT : (T.subst e.images).normalForm = (T'.subst f.images).normalForm)
    (hv : ∀ ha hb, (r.val ha).val = (q.val hb).val) : r.parameter = q.parameter := by
  by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
  · have hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
    rw [r.parameter_eq ha,q.parameter_eq hb,hv ha hb]
  · have hb : ¬ ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
    simp only [parameter,ha,hb,dite_false]

theorem val_congr (r : PreResult Ω C hno M T e) (q : PreResult Ω C hno M' T' f)
    (hr : r.parameter = q.parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm)) :
    (r.val ha).val = (q.val hb).val := by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact Option.some.inj hr

/-- A cross-context form of base projection congruence. The literal-sort
condition is retained: arbitrary retargeting preserves Val, not every unused
Read coordinate. -/
theorem baseRead_congr (h : HasType P Γ M T) (h' : HasType P Δ M' T')
    (hM : (M.subst e.images).normalForm = (M'.subst f.images).normalForm)
    (hT : (T.subst e.images).normalForm = (T'.subst f.images).normalForm)
    (hS : (∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C) ↔
      (∃ s : S, T' = .sort s ∧ ({s} : Set S) ∈ C))
    (v : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (T.subst e.images).normalForm)
    (w : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) →
      Value (hw := hw) Ω C hno (T'.subst f.images).normalForm)
    (hv : ∀ ha hb, (v ha).val = (w hb).val) :
    (baseRead h v).val = (baseRead h' w).val := by
  by_cases hm : Ω.profile (M.subst e.images).normalForm ∈ C
  · have hm' : Ω.profile (M'.subst f.images).normalForm ∈ C := hM ▸ hm
    by_cases hs : ∃ s : S, T = .sort s ∧ ({s} : Set S) ∈ C
    · have hs' := hS.mp hs
      by_cases ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm)
      · have hb : ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true]
        have hX : e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs'.choose_spec.1 ▸ h') := Subtype.ext hM
        rw [hv ha hb]
        exact congrArg (fun X : ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb : ¬ ActiveLayer P C (Ω.profile (T'.subst f.images).normalForm) := hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true,dite_false]
        exact congrArg (Candidates.Top Ω) hM
    · have hs' := mt hS.mpr hs
      simp only [baseRead,hm,hm',hs,hs',dite_true,dite_false]
      exact congrArg (Candidates.Top Ω) hM
  · have hm' : Ω.profile (M'.subst f.images).normalForm ∉ C := hM ▸ hm
    simp only [baseRead,hm,hm',dite_false]
    exact congrArg (Candidates.Top Ω) hM
end

variable {Ω C hno} {Γ Δ : List (Expr S)} {T T' : Expr S}

 theorem abstractionAction_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Δ (.lam D' m') T')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Δ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hb : ∀ n n' (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm))
    (a : FrameKey Ω C (e.activeType h ha)) (a' : FrameKey Ω C (e'.activeType h' ha'))
    (haa : a.argument = a'.argument) (p : Option (RawValue (hw := hw) Ω C hno))
    (hpa : PayloadFits Ω C hno a.domain p) (hpa' : PayloadFits Ω C hno a'.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp' hc' eb' e' ha' a' p hpa').val := by
  dsimp only [abstractionAction,ProductInstance.frameEnvironment,ProductInstance.extend]
  exact hb a.argument a'.argument _ _ haa p _ _ _ _

 theorem abstraction_val_congr {D m E D' m' E' : Expr S} {s s' : S}
    (h : HasType P Γ (.lam D m) T) (h' : HasType P Δ (.lam D' m') T')
    (hp : HasType P Γ (.pi D E) (.sort s)) (hp' : HasType P Δ (.pi D' E') (.sort s'))
    (hc : Converts T (.pi D E)) (hc' : Converts T' (.pi D' E'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) m E)
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) m' E')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hb : ∀ n n' (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((abstraction h hp hc eb e).val ha).val =
      ((abstraction h' hp' hc' eb' e').val ha').val := by
  apply lambdaValue_congr Ω C hno hT
  exact abstractionAction_congr h h' hp hp' hc hc' eb eb' e e' hb ha ha'

 theorem application_val_congr {f n D E f' n' D' E' : Expr S}
    (h : HasType P Γ (.app f n) T) (h' : HasType P Δ (.app f' n') T')
    (hf : HasType P Γ f (.pi D E)) (hf' : HasType P Δ f' (.pi D' E'))
    (hn : HasType P Γ n D) (hn' : HasType P Δ n' D')
    (hc : Converts T (E.instantiate n)) (hc' : Converts T' (E'.instantiate n'))
    (ef : Evaluator (hw := hw) Ω C hno Γ f (.pi D E))
    (ef' : Evaluator (hw := hw) Ω C hno Δ f' (.pi D' E'))
    (en : Evaluator (hw := hw) Ω C hno Γ n D)
    (en' : Evaluator (hw := hw) Ω C hno Δ n' D')
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hF : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hN : (n.subst e.images).normalForm = (n'.subst e'.images).normalForm)
    (hvf : ∀ ha ha', ((ef e).val ha).val = ((ef' e').val ha').val)
    (hvn : (en e).parameter = (en' e').parameter)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((application h hf hn hc ef en e).val ha).val =
      ((application h' hf' hn' hc' ef' en' e').val ha').val := by
  by_cases hA : ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst e.images).normalForm)
  · have hA' : ActiveLayer P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_left hA,dite_eq_left hA']
    apply applyValue_congr Ω C hno hF _ _ (hvf _ _) _ _ hN _ _ hvn
  · have hA' : ¬ ActiveLayer P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm) := hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dite_eq_right hA,dite_eq_right hA']
    exact distinguished_congr Ω C hno hT

 theorem productCandidate_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hD : (D.subst e.images).normalForm = (D'.subst e'.images).normalForm)
    (hE : (E.subst (Expr.liftSub e.images)).normalForm = (E'.subst (Expr.liftSub e'.images)).normalForm)
    (hvd : Ω.profile (D.subst e.images).normalForm ∈ C → (ed e).read.val = (ed' e').read.val)
    (hvb : ∀ n (hn : Ω.HasType n (D.subst e.images)) (hn' : Ω.HasType n (D'.subst e'.images))
        p hp hp', Ω.profile (E.subst (e.cons hn p hp).images).normalForm ∈ C →
        (eb (e.cons hn p hp)).read.val = (eb' (e'.cons hn' p hp')).read.val) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val := by
  dsimp only [productCandidate]
  apply ProductInstance.candidate_eq (t := productData hd hb hr e) (t' := productData hd' hb' hr' e') hD hE
  · exact hvd
  · intro n hn p hp hh
    exact hvb n _ _ p _ _ hh
 theorem product_val_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasType P Γ (.pi D E) T) (h' : HasType P Δ (.pi D' E') T')
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : Converts T (.sort c)) (hc' : Converts T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hT : (T.subst e.images).normalForm = (T'.subst e'.images).normalForm)
    (hM : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hcc : ({c} : Set S) ∈ C ↔ ({c'} : Set S) ∈ C)
    (hpc : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val)
    (ha : ActiveLayer P C (Ω.profile (T.subst e.images).normalForm))
    (ha' : ActiveLayer P C (Ω.profile (T'.subst e'.images).normalForm)) :
    ((product h hd hb hr hc ed eb e).val ha).val =
      ((product h' hd' hb' hr' hc' ed' eb' e').val ha').val := by
  by_cases hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : ({c'} : Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C :=
      ⟨hcc.mp hh.1,hM ▸ hh.2⟩
    simp only [product,dite_eq_left hh,dite_eq_left hh']
    apply withBase_congr Ω C hno hT
    apply Base.update_congr Ω _ (Subtype.ext hM)
    exact hpc hh.2
  · have hh' : ¬ (({c'} : Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C) :=
      fun hcc' => hh ⟨hcc.mpr hcc'.1,hM.symm ▸ hcc'.2⟩
    simp only [product,dite_eq_right hh,dite_eq_right hh']
    exact distinguished_congr Ω C hno hT

 theorem product_read_congr {D E D' E' : Expr S} {a b c a' b' c' : S}
    (h : HasType P Γ (.pi D E) T) (h' : HasType P Δ (.pi D' E') T')
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b)) (hr : P.rule a b c)
    (hd' : HasType P Δ D' (.sort a')) (hb' : HasType P (D' :: Δ) E' (.sort b')) (hr' : P.rule a' b' c')
    (hc : Converts T (.sort c)) (hc' : Converts T' (.sort c'))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (ed' : Evaluator (hw := hw) Ω C hno Δ D' (.sort a'))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (eb' : Evaluator (hw := hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e : Environment (hw := hw) Ω C hno Γ) (e' : Environment (hw := hw) Ω C hno Δ)
    (hM : (Expr.pi D E |>.subst e.images).normalForm = (Expr.pi D' E' |>.subst e'.images).normalForm)
    (hpc : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val) :
    (product h hd hb hr hc ed eb e).read.val = (product h' hd' hb' hr' hc' ed' eb' e').read.val := by
  by_cases hh : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C
  · have hh' : Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∈ C := hM ▸ hh
    simp only [product,ite_eq_left hh,ite_eq_left hh']
    exact hpc hh
  · have hh' : Ω.profile (Expr.pi D' E' |>.subst e'.images).normalForm ∉ C := hM ▸ hh
    simp only [product,ite_eq_right hh,ite_eq_right hh']
    exact congrArg (Candidates.Top Ω) hM
end PreResult
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace Expr
variable {S : Type u} {M : Expr S} {n : Nat}
theorem Scoped.subst_congr (h : Scoped n M) {σ τ : Nat → Expr S}
    (he : ∀ i, i < n → σ i = τ i) : M.subst σ = M.subst τ := by
  induction M generalizing n σ τ with
  | var i => exact he i h
  | sort s => rfl
  | app f a ihf iha => exact congrArg₂ Expr.app (ihf h.1 he) (iha h.2 he)
  | lam D m ihD ihm =>
    apply congrArg₂ Expr.lam (ihD h.1 he)
    apply ihm h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))
  | pi D E ihD ihE =>
    apply congrArg₂ Expr.pi (ihD h.1 he)
    apply ihE h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))

@[simp] theorem rename_eq_sort (M : Expr S) (ρ : Nat → Nat) (s : S) :
    M.rename ρ = .sort s ↔ M = .sort s := by
  cases M <;> simp [rename]
end Expr

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
/-- Matching old raw images and parameters under declaration reindexing.
No equality is imposed on undeclared indices. -/
def Reindexed (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) (ρ : Nat → Nat) : Prop :=
  ∀ i, i < Γ.length → e.images i = f.images (ρ i) ∧ e.parameters i = f.parameters (ρ i)

namespace Reindexed
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable {ρ : Nat → Nat} (he : e.Reindexed f ρ)
include he
 theorem raw_eq {M : Expr S} (hm : M.Scoped Γ.length) :
    M.subst e.images = (M.rename ρ).subst f.images := by
  rw [Expr.subst_rename]
  apply hm.subst_congr
  exact fun n hn => (he n hn).1
 theorem expr_eq {M T : Expr S} (h : HasType P Γ M T) :
    (M.subst e.images).normalForm = (M.rename ρ |>.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq h.scope.1)
 theorem type_eq {M T : Expr S} (h : HasType P Γ M T) :
    (T.subst e.images).normalForm = (T.rename ρ |>.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq h.scope.2)
 theorem cons {A : Expr S} {n m : Expr S}
    (hn : Ω.HasType n (A.subst e.images)) (hm : Ω.HasType m (A.rename ρ |>.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hp' : PayloadFits Ω C hno (A.rename ρ |>.subst f.images).normalForm p) :
    (e.cons hn p hp).Reindexed (f.cons hm p hp') (Expr.liftRen ρ) := by
  intro i hi
  cases i with
  | zero => exact ⟨hnm,rfl⟩
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
end Reindexed
end Environment

 theorem preEvaluate_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.Reindexed f ρ) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.rename hΔ ρ hρ) f).read.val := by
  induction t generalizing Δ ρ with
  | var ht hd hc =>
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).parameter := by
        exact (PreResult.lookup_parameter ht hd hc e).trans
          ((hef _ ht.scope.1).2.trans (PreResult.lookup_parameter
            (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).symm)
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ))
        (hef.expr_eq ht) (hef.type_eq ht)
      · simp only [Expr.rename_eq_sort]
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.type_eq ht)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.type_eq ht)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq ht)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.abstraction ht d b hp hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) hp
          (hp.rename hΔ ρ (hρ.typed hΔ)) hc (hc.rename ρ) _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
          (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg hΔ ρ hρ e f hef
      have hn := ihn hΔ ρ hρ e f hef
      have he := hef.type_eq ht
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.application ht gtr ntr hc).rename hΔ ρ hρ) f).val ha').val := by
        apply PreResult.application_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) gtr.typing
          (gtr.typing.rename hΔ ρ (hρ.typed hΔ)) ntr.typing (ntr.typing.rename hΔ ρ (hρ.typed hΔ))
          hc _ _ _ _ _ e f he (hef.type_eq gtr.typing) (hef.expr_eq ntr.typing)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb := btr.typing.rename (.cons hΔ hh) (Expr.liftRen ρ) ((hρ.lift D).typed (.cons hΔ hh))
      have hm := hef.expr_eq ht
      have he := hef.type_eq ht
      have hDE := Expr.pi.inj (hef.raw_eq ht.scope.1)
      have hpc : ∀ (_ : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.rename hΔ ρ hρ))
            (preEvaluate Ω C hno (btr.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.normalForm hDE.1) (congrArg Expr.normalForm hDE.2)
        · intro _
          exact (ihd hΔ ρ hρ e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
            (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f hm hpc

end ObservationValues

namespace TypingTree
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {M T : Expr S}
/-- Context conversion retains every nonvariable core and all sort choices. -/
noncomputable def recontext (t : TypingTree P Γ M T) (h : ContextEquivalent P Γ Δ) :
    TypingTree P Δ M T := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      exact .var ht' g.choose_spec.1 g.choose_spec.2
  | sort ht ha hc => exact .sort ((h.typing _ _).mp ht) ha hc
  | product ht d b hr hc ihd ihb =>
      exact .product ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) hr hc
  | abstraction ht d b hp hc ihd ihb =>
      exact .abstraction ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) ((h.typing _ _).mp hp) hc
  | application ht g n hc ihg ihn => exact .application ((h.typing _ _).mp ht) (ihg h) (ihn h) hc
end TypingTree

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)
namespace Environment
variable {Ω C hno} {Γ Δ : List (Expr S)}
def SameData (e : Environment (hw := hw) Ω C hno Γ)
    (f : Environment (hw := hw) Ω C hno Δ) : Prop := e.images = f.images ∧ e.parameters = f.parameters
namespace SameData
variable {e : Environment (hw := hw) Ω C hno Γ} {f : Environment (hw := hw) Ω C hno Δ}
variable (he : e.SameData f)
include he
theorem raw_eq (M : Expr S) : M.subst e.images = M.subst f.images := congrArg (M.subst) he.1
theorem expr_eq (M : Expr S) : (M.subst e.images).normalForm = (M.subst f.images).normalForm :=
  congrArg Expr.normalForm (he.raw_eq M)
theorem cons {A : Expr S} {n m : Expr S}
    (hn : Ω.HasType n (A.subst e.images)) (hm : Ω.HasType m (A.subst f.images))
    (hnm : n = m) (p : Option (RawValue (hw := hw) Ω C hno))
    (hp : PayloadFits Ω C hno (A.subst e.images).normalForm p)
    (hp' : PayloadFits Ω C hno (A.subst f.images).normalForm p) :
    (e.cons hn p hp).SameData (f.cons hm p hp') := by
  constructor
  · funext i; cases i with
    | zero => exact hnm
    | succ i => exact congrFun he.1 i
  · funext i; cases i with
    | zero => rfl
    | succ i => exact congrFun he.2 i
end SameData
end Environment

theorem preEvaluate_recontext {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ)
    (e : Environment (hw := hw) Ω C hno Γ) (f : Environment (hw := hw) Ω C hno Δ)
    (hef : e.SameData f) :
    (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno (t.recontext h) f).parameter ∧
    (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno (t.recontext h) f).read.val := by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht' := (h.typing _ _).mp ht
      let g := ht'.generation
      have hparam : (PreResult.lookup ht hd hc e).parameter =
          (PreResult.lookup ht' g.choose_spec.1 g.choose_spec.2 f).parameter := by
        rw [PreResult.lookup_parameter, PreResult.lookup_parameter]
        exact congrFun hef.2 _
      refine ⟨hparam,?_⟩
      apply PreResult.baseRead_congr ht ht' (hef.expr_eq _) (hef.expr_eq _)
      · exact Iff.rfl
      · exact fun ha hb => PreResult.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreResult.parameter_congr _ _ (hef.expr_eq _)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.expr_eq _)
      · exact congrArg (Candidates.Top Ω) (hef.expr_eq _)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.abstraction ht d b hp hc).recontext h) f).val ha').val := by
        apply PreResult.abstraction_val_congr ht ((h.typing _ _).mp ht) hp ((h.typing _ _).mp hp)
          hc hc _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreResult.val_congr
        exact (ihb (h.cons d.typing) (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg := ihg h e f hef
      have hn := ihn h e f hef
      have he := hef.expr_eq T
      have hv : ∀ ha ha', ((preEvaluate Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEvaluate Ω C hno ((TypingTree.application ht gtr ntr hc).recontext h) f).val ha').val := by
        apply PreResult.application_val_congr ht ((h.typing _ _).mp ht) gtr.typing
          ((h.typing _ _).mp gtr.typing) ntr.typing ((h.typing _ _).mp ntr.typing)
          hc hc _ _ _ _ e f he (hef.expr_eq _) (hef.expr_eq _)
        · exact fun ha ha' => PreResult.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreResult.parameter_congr _ _ he hv
      · apply PreResult.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh := (h.typing _ _).mp d.typing
      have hb := ((h.cons d.typing).typing _ _).mp btr.typing
      have hm := hef.expr_eq (.pi D E)
      have he := hef.expr_eq T
      have hDE := Expr.pi.inj (hef.raw_eq (.pi D E))
      have hpc : ∀ (_ : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C),
          (PreResult.productCandidate d.typing btr.typing hr (preEvaluate Ω C hno d)
            (preEvaluate Ω C hno btr) e).val =
          (PreResult.productCandidate hh hb hr (preEvaluate Ω C hno (d.recontext h))
            (preEvaluate Ω C hno (btr.recontext (h.cons d.typing))) f).val := by
        intro _
        apply PreResult.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.normalForm hDE.1) (congrArg Expr.normalForm hDE.2)
        · intro _
          exact (ihd h e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (h.cons d.typing) (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreResult.parameter_congr _ _ he
        apply PreResult.product_val_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreResult.product_read_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f hm hpc
end ObservationValues

namespace Expr
variable {S : Type u}
def consSub (n : Expr S) (σ : Nat → Expr S) : Nat → Expr S
  | 0 => n
  | i+1 => σ i
end Expr
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
theorem profile_sort (s : S) : Ω.profile (.sort s) = AxProfile P s := by
  ext t
  change (∃ n, PureTypeSystem.HasType P (Ω.context n) ((Expr.sort s).normalForm.rename (Expr.reverseIndex n))
    ((Expr.sort t).rename (Expr.reverseIndex n))) ↔ P.axioms s t
  simp only [Expr.normalForm_of_normal (Normal.sort s),Expr.rename]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨u,ha,hc⟩ := hn.generation
    exact hc.sort_inj ▸ ha
  · intro h; exact ⟨0,PureTypeSystem.HasType.sort_of_valid (Ω.valid 0) h⟩
end ContextTower
namespace FeasibleProfile
variable {S : Type u} {P : Specification S}
theorem singleton {s : S} (h : (AxProfile P s).Nonempty) : FeasibleProfile P {s} := by
  obtain ⟨t,ht⟩ := h
  have hs : HasType P [] (.sort s) (.sort t) := .ax ht
  have hv : HasType P [.sort s] (.var 0) (.sort s) := .var hs
  exact ⟨Set.singleton_nonempty s,[.sort s],.var 0,hv.valid,Normal.var 0,
    Profile.neutral (Normal.var 0) (.var 0) hv⟩
end FeasibleProfile

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
/-- Goodness is deliberately independent of observation parameters. -/
def baseGood (M T : Expr S) (σ : Nat → Expr S) (v : Prop) : Prop :=
  Ω.profile (M.subst σ) ∈ C →
    ∃ s, T = .sort s ∧ ({s} : Set S) ∈ C ∧
      (ActiveLayer P C (Ω.profile (T.subst σ)) → v) ∧
      (¬ ActiveLayer P C (Ω.profile (T.subst σ)) → Neutral M)

noncomputable def goodness {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop × Prop :=
  match t with
  | .var _ _ _ => (True,baseGood Ω C M T σ True)
  | .sort _ _ _ => (True,True)
  | @TypingTree.product _ _ _ D E _ _ c _ _ d e _ _ =>
    let g := (Ω.profile (D.subst σ) ∈ C → (goodness d σ).2) ∧
      ∀ n, Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
        (goodness e (Expr.consSub n σ)).2
    ((({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst σ) ∈ C) → g,
      Ω.profile (Expr.pi D E |>.subst σ) ∈ C → g)
  | @TypingTree.abstraction _ _ _ D m E _ _ _ _ _ b _ _ =>
    let g := ∀ n, Ω.HasType n (D.subst σ) → ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n σ))) →
      (goodness b (Expr.consSub n σ)).1
    (g,baseGood Ω C M T σ g)
  | @TypingTree.application _ _ _ g n D E _ _ f a _ =>
    let v := if ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst σ)) then
      (goodness f σ).1 ∧ (ActiveLayer P C (Ω.profile (D.subst σ)) → (goodness a σ).1)
      else Neutral (.app g n)
    (v,baseGood Ω C M T σ v)

abbrev ValGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).1
abbrev ReadGood {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T) (σ : Nat → Expr S) : Prop :=
  (goodness Ω C t σ).2

def Relevant (Γ : List (Expr S)) (M : Expr S) : Prop :=
  ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ M) K
namespace Relevant
variable {Ω C}
theorem pred {Γ Δ : List (Expr S)} {M N : Expr S} (h : Relevant (P := P) C Γ M)
    (hp : Reach (PrimaryEdge P) (Profile P Δ N) (Profile P Γ M)) : Relevant (P := P) C Δ N := by
  obtain ⟨K,hK,hp'⟩ := h
  exact ⟨K,hK,hp.trans hp'⟩
end Relevant

variable (hw : SystemWeaklyNormalizing P) (hC : IsComponent (PrimaryEdge P) C)
include hw hC
theorem relevant_actual_mem {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : HasType P Γ M (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hr : Relevant (P := P) C Γ M) (hm : Ω.profile (M.subst σ) ∈ C) : Profile P Γ M ∈ C := by
  obtain ⟨K,hK,hp⟩ := hr
  have hg := Ω.profile_subst_growth hw ht hσ
  have hga := ContextTower.HasType.subst ht hσ
  have hpath := Profile.inclusion_path (Ω.profile_feasible hw hga)
    (Profile.feasible (ht.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw ht)) hg
  exact hC.between hm hK hpath.reach hp

theorem normal_baseGood {Γ : List (Expr S)} {M : Expr S} {s : S} {σ : Nat → Expr S}
    (h : HasType P Γ M (.sort s)) (hn : Normal M) (hne : Neutral M)
    (hσ : Ω.TypedSubstitution Γ σ) (hr : Relevant (P := P) C Γ M) {v : Prop}
    (hv : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ)) → v) :
    baseGood Ω C M (.sort s) σ v := by
  intro hm
  have hp := relevant_actual_mem Ω C hw hC h hσ hr hm
  rw [Profile.neutral hn hne h] at hp
  exact ⟨s,rfl,hp,hv,fun _ => hne⟩

theorem normal_good {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    (hn : Normal M) (σ : Nat → Expr S) (hσ : Ω.TypedSubstitution Γ σ) :
    (ActiveLayer P C (Ω.profile (T.subst σ)) → ValGood Ω C t σ) ∧
    (∀ s, T = .sort s → Relevant (P := P) C Γ M → ReadGood Ω C t σ) := by
  induction t generalizing σ with
  | var ht hd hc =>
      refine ⟨fun _ => trivial,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn (.var _) hσ hr (fun _ => trivial)
  | sort ht ha hc => exact ⟨fun _ => trivial,fun _ _ _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv : ValGood Ω C (.abstraction ht d b hp hc) σ := by
        intro n hn' ha
        exact (ihb hn.lam_body (Expr.consSub n σ) (hσ.cons hn')).1 ha
      refine ⟨fun _ => hv,?_⟩
      intro s hs _
      exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hne : Neutral (.app g n) := by
        obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩ := ht.normal_shape hn
        · cases he
        · exact hne
        · cases he
        · cases he
      have hv : ValGood Ω C (.application ht f a hc) σ := by
        dsimp only [ValGood,goodness]
        split
        · rename_i hf
          exact ⟨(ihf hn.app_left σ hσ).1 hf,fun ha => (iha hn.app_right σ hσ).1 ha⟩
        · exact hne
      refine ⟨fun _ => hv,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn hne hσ hr (fun _ => hv)
  | @product Γ D E a b c T ht d e hr hc ihd ihe =>
      have hpi : HasType P Γ (.pi D E) (.sort c) := .product d.typing e.typing hr
      have hp := Profile.triple hw hpi
      have hg : Relevant (P := P) C Γ (.pi D E) →
          (Ω.profile (D.subst σ) ∈ C → ReadGood Ω C d σ) ∧
          (∀ n, Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
            ReadGood Ω C e (Expr.consSub n σ)) := by
        intro hrel
        constructor
        · intro _
          exact (ihd hn.pi_domain σ hσ).2 a rfl (hrel.pred (.single (.domain hp)))
        · intro n hn' _
          exact (ihe hn.pi_body (Expr.consSub n σ) (hσ.cons hn')).2 b rfl
            (hrel.pred (.single (.codomain hp)))
      constructor
      · intro hat hcc
        have hconv : (T.subst σ).normalForm = .sort c :=
          (Expr.normalForm_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
            ((ContextTower.HasType.subst hpi hσ).type_weaklyNormalizing hw) (hc.subst σ)).trans
              (Expr.normalForm_of_normal (Normal.sort c))
        have hax : (AxProfile P c).Nonempty := by
          have hh := hat.nonempty
          rwa [← Ω.profile_normalForm (T.subst σ),hconv,Ω.profile_sort] at hh
        have hs : ({c} : Set S) ⊆ Profile P Γ (.pi D E) := by
          intro r hr'
          have he : r = c := hr'
          subst r
          exact hpi.normalForm hw
        exact hg ⟨{c},hcc.1,(Profile.inclusion_path hp.product (FeasibleProfile.singleton hax) hs).reach⟩
      · intro _ _ hrel
        exact fun _ => hg hrel

end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

/-- Normal-syntax values forget all stored generation choices; normal Reads
also forget their literal sort choice. No functionality hypothesis is used. -/
theorem normal_tree_independence {Γ : List (Expr S)} {M T : Expr S}
    (t : TypingTree P Γ M T) : Normal M →
    ∀ {U : Expr S} (t' : TypingTree P Γ M U) (e : Environment (hw := hw) Ω C hno Γ),
    (Converts T U → (preEvaluate Ω C hno t e).parameter = (preEvaluate Ω C hno t' e).parameter) ∧
    (∀ s s', T = .sort s → U = .sort s' →
      (preEvaluate Ω C hno t e).read.val = (preEvaluate Ω C hno t' e).read.val) := by
  induction t with
  | @var Γ n A T ht hd hc =>
      intro _ U t' e
      cases t' with
      | var ht' hd' hc' =>
          have hv : (PreResult.lookup ht hd hc e).parameter = (PreResult.lookup ht' hd' hc' e).parameter := by
            rw [PreResult.lookup_parameter,PreResult.lookup_parameter]
          refine ⟨fun _ => hv,?_⟩
          intro s s' hs hs'
          have he : s = s' := (hs ▸ hs' ▸ HasType.neutral_unique (.var n) ht ht').sort_inj
          subst s'; subst T; subst U
          apply PreResult.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ hv ha hb
  | sort ht ha hc =>
      intro _ U t' e
      cases t' with
      | sort ht' ha' hc' =>
          constructor
          · intro hh
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            intro _ _
            exact distinguished_congr Ω C hno (e.type_convert_eq ht ht' hh)
          · exact fun _ _ _ _ => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @abstraction _ _ _ E' a' s' _ ht' d' b' hp' hc' =>
          constructor
          · intro hh
            have hproducts : Converts (.pi D E) (.pi D E') := .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have hEE := hproducts.product_compatibility.2
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e (e.type_convert_eq ht ht' hh)
            intro n n' hnt hn' he p hpa hpb hact hact'
            subst n'
            exact PreResult.val_congr _ _ ((ihb hn.lam_body b' (e.cons hnt p hpa)).1 hEE) hact hact'
          · intro r r' hs _
            exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      intro hn U t' e
      cases t' with
      | @application _ _ _ D' E' _ ht' f' a' hc' =>
          have hg : Neutral g := by
            obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩ := ht.normal_shape hn
            · cases he
            · cases hne with | app hne => exact hne
            · cases he
            · cases he
          have hF := HasType.neutral_unique hg f.typing f'.typing
          have hD := hF.product_compatibility.1
          have hv : ∀ (hh : Converts T U),
              (preEvaluate Ω C hno (.application ht f a hc) e).parameter =
              (preEvaluate Ω C hno (.application ht' f' a' hc') e).parameter := by
            intro hh
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.application_val_congr ht ht' f.typing f'.typing a.typing a'.typing hc hc'
              _ _ _ _ e e (e.type_convert_eq ht ht' hh) (e.type_convert_eq f.typing f'.typing hF) rfl
            · exact fun ha hb => PreResult.val_congr _ _ ((ihf hn.app_left f' e).1 hF) ha hb
            · exact (iha hn.app_right a' e).1 hD
          refine ⟨hv,?_⟩
          intro s s' hs hs'
          have hh := HasType.neutral_unique (.app hg) ht ht'
          have he : s = s' := (hs ▸ hs' ▸ hh).sort_inj
          subst s'; subst T; subst U
          apply PreResult.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreResult.val_congr _ _ (hv hh) ha hb
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @product _ _ _ a' b' c' _ ht' d' bt' hr' hc' =>
          have hpc : (PreResult.productCandidate d.typing bt.typing hr (preEvaluate Ω C hno d)
              (preEvaluate Ω C hno bt) e).val =
              (PreResult.productCandidate d'.typing bt'.typing hr' (preEvaluate Ω C hno d')
                (preEvaluate Ω C hno bt') e).val := by
            apply PreResult.productCandidate_congr d.typing bt.typing hr d'.typing bt'.typing hr' _ _ _ _ e e rfl rfl
            · exact fun _ => (ihd hn.pi_domain d' e).2 a a' rfl rfl
            · intro n hn' hn'' p hp hp' _
              exact (ihb hn.pi_body bt' (e.cons hn' p hp)).2 b b' rfl rfl
          constructor
          · intro hh
            have hsorts : Converts (.sort c) (.sort c') := .trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have he : c = c' := hsorts.sort_inj
            apply PreResult.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreResult.product_val_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e (e.type_convert_eq ht ht' hh) rfl
            · exact he ▸ Iff.rfl
            · exact fun _ => hpc
          · intro _ _ _ _
            exact PreResult.product_read_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e rfl (fun _ => hpc)
end PureTypeSystem.ObservationValues

namespace PureTypeSystem
universe u
namespace ContextTower.TypedSubstitution
variable {S : Type u} {P : Specification S} {Ω : ContextTower P} {Γ : List (Expr S)}
    {σ τ : Nat → Expr S}
def Compatible (Γ : List (Expr S)) (σ τ : Nat → Expr S) : Prop :=
  ∀ n, n < Γ.length → Converts (σ n) (τ n)
namespace Compatible
variable (hw : SystemWeaklyNormalizing P)
include hw
theorem expr_eq (he : Compatible Γ σ τ) (hσ : Ω.TypedSubstitution Γ σ)
    (hτ : Ω.TypedSubstitution Γ τ) {M A : Expr S} (h : PureTypeSystem.HasType P Γ M A) :
    (M.subst σ).normalForm = (M.subst τ).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst h hσ).weaklyNormalizing hw)
    ((ContextTower.HasType.subst h hτ).weaklyNormalizing hw) (h.scope.1.subst_converts he)
theorem type_eq (he : Compatible Γ σ τ) (hσ : Ω.TypedSubstitution Γ σ)
    (hτ : Ω.TypedSubstitution Γ τ) {M A : Expr S} (h : PureTypeSystem.HasType P Γ M A) :
    (A.subst σ).normalForm = (A.subst τ).normalForm :=
  Expr.normalForm_converts ((ContextTower.HasType.subst h hσ).type_weaklyNormalizing hw)
    ((ContextTower.HasType.subst h hτ).type_weaklyNormalizing hw) (h.scope.2.subst_converts he)
theorem expr_profile (he : Compatible Γ σ τ) (hσ : Ω.TypedSubstitution Γ σ)
    (hτ : Ω.TypedSubstitution Γ τ) {M A : Expr S} (h : PureTypeSystem.HasType P Γ M A) :
    Ω.profile (M.subst σ) = Ω.profile (M.subst τ) := by
  rw [← Ω.profile_normalForm (M.subst σ),← Ω.profile_normalForm (M.subst τ),he.expr_eq hw hσ hτ h]
theorem type_profile (he : Compatible Γ σ τ) (hσ : Ω.TypedSubstitution Γ σ)
    (hτ : Ω.TypedSubstitution Γ τ) {M A : Expr S} (h : PureTypeSystem.HasType P Γ M A) :
    Ω.profile (A.subst σ) = Ω.profile (A.subst τ) := by
  rw [← Ω.profile_normalForm (A.subst σ),← Ω.profile_normalForm (A.subst τ),he.type_eq hw hσ hτ h]
omit hw in
theorem cons (he : Compatible Γ σ τ) {D n m : Expr S} (hh : Converts n m) :
    Compatible (D :: Γ) (Expr.consSub n σ) (Expr.consSub m τ) := by
  intro i hi
  cases i with
  | zero => exact hh
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
omit hw in
theorem cons_same (he : Compatible Γ σ τ) (D n : Expr S) :
    Compatible (D :: Γ) (Expr.consSub n σ) (Expr.consSub n τ) := he.cons (.refl n)
end Compatible
end ContextTower.TypedSubstitution

namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem baseGood_congr {Γ : List (Expr S)} {M T : Expr S} {σ τ : Nat → Expr S}
    (h : HasType P Γ M T) (hσ : Ω.TypedSubstitution Γ σ) (hτ : Ω.TypedSubstitution Γ τ)
    (he : ContextTower.TypedSubstitution.Compatible Γ σ τ) {v w : Prop} (hv : v ↔ w) :
    baseGood Ω C M T σ v ↔ baseGood Ω C M T τ w := by
  simp only [baseGood,he.expr_profile hw hσ hτ h,he.type_profile hw hσ hτ h,hv]

theorem goodness_compatible {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {σ τ : Nat → Expr S} (hσ : Ω.TypedSubstitution Γ σ) (hτ : Ω.TypedSubstitution Γ τ)
    (he : ContextTower.TypedSubstitution.Compatible Γ σ τ) :
    (ValGood Ω C t σ ↔ ValGood Ω C t τ) ∧ (ReadGood Ω C t σ ↔ ReadGood Ω C t τ) := by
  induction t generalizing σ τ with
  | var ht hd hc => exact ⟨Iff.rfl,baseGood_congr Ω C hw ht hσ hτ he Iff.rfl⟩
  | sort ht ha hc => exact ⟨Iff.rfl,Iff.rfl⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hind (n : Expr S) : Ω.HasType n (D.subst σ) ↔ Ω.HasType n (D.subst τ) := by
        constructor
        · intro hn; exact hn.conversion (ContextTower.HasType.subst d.typing hτ) (d.typing.scope.1.subst_converts he)
        · intro hn; exact hn.conversion (ContextTower.HasType.subst d.typing hσ) (.symm _ _ (d.typing.scope.1.subst_converts he))
      have hv : ValGood Ω C (.abstraction ht d b hp hc) σ ↔ ValGood Ω C (.abstraction ht d b hp hc) τ := by
        dsimp only [ValGood,goodness]
        apply forall_congr'; intro n
        constructor
        · intro h hn
          have hn' := (hind n).mpr hn
          have he' := he.cons_same D n
          rw [← he'.type_profile hw (hσ.cons hn') (hτ.cons hn) b.typing]
          exact fun ha => (ihb (hσ.cons hn') (hτ.cons hn) he').1.mp (h hn' ha)
        · intro h hn
          have hn' := (hind n).mp hn
          have he' := he.cons_same D n
          rw [he'.type_profile hw (hσ.cons hn) (hτ.cons hn') b.typing]
          exact fun ha => (ihb (hσ.cons hn) (hτ.cons hn') he').1.mpr (h hn' ha)
      exact ⟨hv,baseGood_congr Ω C hw ht hσ hτ he hv⟩
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hv : ValGood Ω C (.application ht f a hc) σ ↔ ValGood Ω C (.application ht f a hc) τ := by
        dsimp only [ValGood,goodness]
        have hF := he.type_profile hw hσ hτ f.typing
        have hD := he.type_profile hw hσ hτ a.typing
        rw [hF,hD]
        split
        · exact and_congr (ihf hσ hτ he).1 (imp_congr_right fun _ => (iha hσ hτ he).1)
        · exact Iff.rfl
      exact ⟨hv,baseGood_congr Ω C hw ht hσ hτ he hv⟩
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hind (n : Expr S) : Ω.HasType n (D.subst σ) ↔ Ω.HasType n (D.subst τ) := by
        constructor
        · intro hn; exact hn.conversion (ContextTower.HasType.subst d.typing hτ) (d.typing.scope.1.subst_converts he)
        · intro hn; exact hn.conversion (ContextTower.HasType.subst d.typing hσ) (.symm _ _ (d.typing.scope.1.subst_converts he))
      have hbody : (∀ n, Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C → ReadGood Ω C bt (Expr.consSub n σ)) ↔
          (∀ n, Ω.HasType n (D.subst τ) → Ω.profile (E.subst (Expr.consSub n τ)) ∈ C → ReadGood Ω C bt (Expr.consSub n τ)) := by
        apply forall_congr'; intro n
        constructor
        · intro h hn
          have hn' := (hind n).mpr hn
          have he' := he.cons_same D n
          rw [← he'.expr_profile hw (hσ.cons hn') (hτ.cons hn) bt.typing]
          exact fun hh => (ihb (hσ.cons hn') (hτ.cons hn) he').2.mp (h hn' hh)
        · intro h hn
          have hn' := (hind n).mp hn
          have he' := he.cons_same D n
          rw [he'.expr_profile hw (hσ.cons hn) (hτ.cons hn') bt.typing]
          exact fun hh => (ihb (hσ.cons hn) (hτ.cons hn') he').2.mpr (h hn' hh)
      dsimp only [ValGood,ReadGood,goodness]
      have hD := he.expr_profile hw hσ hτ d.typing
      have hM := he.expr_profile hw hσ hτ ht
      rw [hD,hM]
      have hg := and_congr (imp_congr_right fun (_ : Ω.profile (D.subst τ) ∈ C) => (ihd hσ hτ he).2) hbody
      exact ⟨imp_congr_right fun _ => hg,imp_congr_right fun _ => hg⟩

end ObservationValues

namespace Neutral
variable {S : Type u} {M : Expr S} {ρ : Nat → Nat}
theorem of_rename (h : Neutral (M.rename ρ)) : Neutral M := by
  induction M with
  | var n => exact .var n
  | sort s => cases h
  | lam D m ihD ihm => cases h
  | pi D E ihD ihE => cases h
  | app f n ihf ihn => cases h with | app h => exact .app (ihf h)
theorem rename_iff : Neutral (M.rename ρ) ↔ Neutral M := ⟨of_rename,fun h => h.rename ρ⟩
end Neutral
namespace Expr
variable {S : Type u}
theorem consSub_liftRen (n : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (consSub n σ) ∘ liftRen ρ = consSub n (σ ∘ ρ) := by
  funext i; cases i <;> rfl
end Expr
namespace ObservationValues
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

theorem baseGood_rename {M T : Expr S} (ρ : Nat → Nat) (σ : Nat → Expr S) (v : Prop) :
    baseGood Ω C (M.rename ρ) (T.rename ρ) σ v ↔ baseGood Ω C M T (σ ∘ ρ) v := by
  simp only [baseGood,Expr.subst_rename,Expr.rename_eq_sort,Neutral.rename_iff]

theorem goodness_rename {Γ : List (Expr S)} {M T : Expr S} (t : TypingTree P Γ M T)
    {Δ : List (Expr S)} (hΔ : ValidContext P Δ) (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (σ : Nat → Expr S) :
    goodness Ω C (t.rename hΔ ρ hρ) σ = goodness Ω C t (σ ∘ ρ) := by
  induction t generalizing Δ ρ σ with
  | var ht hd hc =>
      apply Prod.ext
      · rfl
      · exact propext (baseGood_rename Ω C ρ σ True)
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      have hv : (∀ n, Ω.HasType n ((D.rename ρ).subst σ) →
          ActiveLayer P C (Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ))) →
          (goodness Ω C (b.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).1) ↔
          (∀ n, Ω.HasType n (D.subst (σ ∘ ρ)) →
          ActiveLayer P C (Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ)))) →
          (goodness Ω C b (Expr.consSub n (σ ∘ ρ))).1) := by
        simp only [Expr.subst_rename,Expr.consSub_liftRen,hb]
      apply Prod.ext
      · exact propext hv
      · change baseGood Ω C (Expr.lam D m |>.rename ρ) (T.rename ρ) σ _ = _
        exact (propext (baseGood_rename Ω C ρ σ _)).trans
          (congrArg (baseGood Ω C (.lam D m) T (σ ∘ ρ)) (propext hv))
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hg := ihf hΔ ρ hρ σ
      have hn := iha hΔ ρ hρ σ
      have hv : (goodness Ω C ((TypingTree.application ht f a hc).rename hΔ ρ hρ) σ).1 =
          (goodness Ω C (.application ht f a hc) (σ ∘ ρ)).1 := by
        change (if ActiveLayer P C (Ω.profile ((Expr.pi D E |>.rename ρ).subst σ)) then
          (goodness Ω C (f.rename hΔ ρ hρ) σ).1 ∧
            (ActiveLayer P C (Ω.profile ((D.rename ρ).subst σ)) → (goodness Ω C (a.rename hΔ ρ hρ) σ).1)
          else Neutral ((Expr.app g n).rename ρ)) =
          (if ActiveLayer P C (Ω.profile ((Expr.pi D E).subst (σ ∘ ρ))) then
            (goodness Ω C f (σ ∘ ρ)).1 ∧
              (ActiveLayer P C (Ω.profile (D.subst (σ ∘ ρ))) → (goodness Ω C a (σ ∘ ρ)).1)
            else Neutral (.app g n))
        rw [hg,hn]
        rw [Expr.subst_rename,Expr.subst_rename]
        split
        · rfl
        · exact propext Neutral.rename_iff
      apply Prod.ext hv
      change baseGood Ω C (Expr.app g n |>.rename ρ) (T.rename ρ) σ _ = _
      exact (propext (baseGood_rename Ω C ρ σ _)).trans
        (congrArg (baseGood Ω C (.app g n) T (σ ∘ ρ)) hv)
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hh : HasType P Δ (D.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hd := ihd hΔ ρ hρ σ
      have hb (n : Expr S) := ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      let g : Prop := (Ω.profile ((D.rename ρ).subst σ) ∈ C →
          (goodness Ω C (d.rename hΔ ρ hρ) σ).2) ∧
          ∀ n, Ω.HasType n ((D.rename ρ).subst σ) →
            Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ)) ∈ C →
              (goodness Ω C (bt.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).2
      let g' : Prop := (Ω.profile (D.subst (σ ∘ ρ)) ∈ C → (goodness Ω C d (σ ∘ ρ)).2) ∧
          ∀ n, Ω.HasType n (D.subst (σ ∘ ρ)) → Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ))) ∈ C →
            (goodness Ω C bt (Expr.consSub n (σ ∘ ρ))).2
      have he : g = g' := by
        dsimp only [g,g']
        simp only [hd,hb,Expr.subst_rename,Expr.consSub_liftRen]
      change ((({c} : Set S) ∈ C ∧ Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C) → g,
        Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C → g) =
        ((({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C) → g',
        Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C → g')
      simp only [Expr.subst_rename,he]

theorem valGood_retarget {Γ : List (Expr S)} {M T T' : Expr S} (t : TypingTree P Γ M T)
    (ht : HasType P Γ M T') (hc : Converts T' T) (σ : Nat → Expr S) :
    ValGood Ω C (t.retarget ht hc) σ ↔ ValGood Ω C t σ := by
  cases t <;> exact Iff.rfl
end ObservationValues

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
theorem profile_converts {A B : Expr S} (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B)
    (hc : Converts A B) : Ω.profile A = Ω.profile B := by
  rw [← Ω.profile_normalForm A,← Ω.profile_normalForm B,Expr.normalForm_converts hA hB hc]

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem instantiate_profile_ascent {Γ : List (Expr S)} {D E n : Expr S} {s : S}
    (hp : PureTypeSystem.HasType P Γ (.pi D E) (.sort s))
    (hn : PureTypeSystem.HasType P Γ n D) {σ : Nat → Expr S} (hσ : Ω.TypedSubstitution Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.profile ((E.instantiate n).subst σ))
      (Ω.profile (Expr.pi D E |>.subst σ)) := by
  have hp' := ContextTower.HasType.subst hp hσ
  have hn' := ContextTower.HasType.subst hn hσ
  obtain ⟨J,htr,hpath⟩ := Ω.frame_profiles hw hp' hn'
  rw [← Expr.instantiate_subst]
  exact hpath.trans (.single (.codomain htr))

theorem neutral_profile_ascent {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : PureTypeSystem.HasType P Γ M T)
    {σ : Nat → Expr S} (hσ : Ω.TypedSubstitution Γ σ) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Ω.profile (T.subst σ)) (Ω.profile (D.subst σ)) := by
  induction hne generalizing T with
  | var n =>
      obtain ⟨D,hd,hc⟩ := ht.generation
      refine ⟨n,D,rfl,hd,?_⟩
      rw [Ω.profile_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst (PureTypeSystem.HasType.lookup ht.valid hd) hσ).type_weaklyNormalizing hw)
        (hc.subst σ)]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D,E,hf,ha,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hf.product_type_sorted
      obtain ⟨n,A,hh,hl,hr⟩ := ih hf
      refine ⟨n,A,hh,hl,?_⟩
      rw [Ω.profile_converts ((ContextTower.HasType.subst ht hσ).type_weaklyNormalizing hw)
        ((ContextTower.HasType.subst (PureTypeSystem.HasType.application hf ha) hσ).type_weaklyNormalizing hw)
        (hc.subst σ)]
      exact (Ω.instantiate_profile_ascent hw hp ha hσ).trans hr
end ContextTower

namespace ObservationValues
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
    (hw : SystemWeaklyNormalizing P)
/-- Only nonneutral replacements need the activity guard. Variables that
remain neutral are harmless even at a skipped clause. -/
def SubstitutionGuard (Γ : List (Expr S)) (σ ξ : Nat → Expr S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Ω.profile (D.subst ξ) ∈ ObservationLayers P C →
    ActiveLayer P C (Ω.profile (D.subst ξ))

include hw
 theorem neutral_subst_of_inactive {Γ : List (Expr S)} {M T : Expr S}
    (hne : Neutral M) (ht : HasType P Γ M T) {σ ξ : Nat → Expr S}
    (hξ : Ω.TypedSubstitution Γ ξ) (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hH : Ω.profile (T.subst ξ) ∈ ObservationLayers P C)
    (hina : ¬ ActiveLayer P C (Ω.profile (T.subst ξ))) : Neutral (M.subst σ) := by
  apply hne.subst_of_head
  intro n hhead
  by_contra hn
  obtain ⟨i,D,hhead',hd,hpath⟩ := Ω.neutral_profile_ascent hw hne ht hξ
  have he : i = n := Expr.var.inj (hhead'.symm.trans hhead)
  subst i
  have hI := ObservationLayers.positive hH hpath
  exact hina ((hguard n D hd hn hI).predecessor (ObservationLayers.secondary hH hpath).reach)

 theorem skipped_application_subst {Γ : List (Expr S)} {f a D E T : Expr S}
    (h : HasType P Γ (.app f a) T) (hf : HasType P Γ f (.pi D E)) (ha : HasType P Γ a D)
    (hc : Converts T (E.instantiate a)) (hne : Neutral (.app f a))
    {σ ξ : Nat → Expr S} (hξ : Ω.TypedSubstitution Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ)
    (hactive : ActiveLayer P C (Ω.profile (T.subst ξ)))
    (hina : ¬ ActiveLayer P C (Ω.profile (Expr.pi D E |>.subst ξ))) :
    Neutral (Expr.app f a |>.subst σ) := by
  have hF : Ω.profile (Expr.pi D E |>.subst ξ) ∈ ObservationLayers P C := by
    obtain ⟨s,hp⟩ := hf.product_type_sorted
    have he := Ω.profile_converts ((ContextTower.HasType.subst h hξ).type_weaklyNormalizing hw)
      ((ContextTower.HasType.subst (HasType.application hf ha) hξ).type_weaklyNormalizing hw) (hc.subst ξ)
    exact ObservationLayers.positive (he ▸ hactive.layer) (Ω.instantiate_profile_ascent hw hp ha hξ)
  have hnf : Neutral f := by cases hne; assumption
  exact .app (neutral_subst_of_inactive Ω C hw hnf hf hξ hguard hF hina)

 theorem skipped_read_subst {Γ : List (Expr S)} {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) (hne : Neutral M)
    {σ ξ : Nat → Expr S} (hξ : Ω.TypedSubstitution Γ ξ)
    (hguard : SubstitutionGuard Ω C Γ σ ξ) (hs : ({s} : Set S) ∈ C)
    (hina : ¬ ActiveLayer P C (AxProfile P s)) : Neutral (M.subst σ) := by
  have hH : AxProfile P s ∈ ObservationLayers P C :=
    ⟨s,hs,Profile.neutral_axiom hne h,.refl⟩
  apply neutral_subst_of_inactive Ω C hw hne h hξ hguard
  · simpa only [Expr.subst,Ω.profile_sort] using hH
  · simpa only [Expr.subst,Ω.profile_sort] using hina
end ObservationValues
end PureTypeSystem

namespace PureTypeSystem.ObservationValues
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) [Fintype S]
variable (C : Set (Set S)) {hw : SystemWeaklyNormalizing P} (hno : ¬ ForbiddenConfiguration P C)

theorem distinguished_base (T : ActiveType Ω C) :
    RawValue.base (hw := hw) Ω C hno (distinguished (hw := hw) Ω C hno T).val = topBase Ω := by
  unfold distinguished
  split
  · exact (ActualPlain.schema hw).distinguished_base _ _ _
  · split
    · rfl
    · rfl

namespace PreResult
variable {Ω C hno} {Γ : List (Expr S)} {M : Expr S} {s : S}
    {e : Environment (hw := hw) Ω C hno Γ}
theorem baseRead_eq (h : HasType P Γ M (.sort s))
    (v : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm) →
      Value (hw := hw) Ω C hno (Expr.sort s |>.subst e.images).normalForm)
    (hM : Ω.profile (M.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (baseRead h v).val = ((RawValue.base Ω C hno (v ha).val) (e.actualExpression h)).val := by
  have hex : ∃ s', Expr.sort s = Expr.sort s' ∧ ({s'} : Set S) ∈ C := ⟨s,rfl,hs⟩
  simp only [baseRead,dite_eq_left hM,dite_eq_left hex,dite_eq_left ha]

theorem product_read_base {D E : Expr S} {a b c : S}
    (h : HasType P Γ (.pi D E) (.sort s))
    (hd : HasType P Γ D (.sort a)) (hb : HasType P (D :: Γ) E (.sort b))
    (hr : P.rule a b c) (hc : Converts (.sort s) (.sort c))
    (ed : Evaluator (hw := hw) Ω C hno Γ D (.sort a))
    (eb : Evaluator (hw := hw) Ω C hno (D :: Γ) E (.sort b))
    (e : Environment (hw := hw) Ω C hno Γ)
    (hm : Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (product h hd hb hr hc ed eb e).read.val =
      ((RawValue.base Ω C hno ((product h hd hb hr hc ed eb e).val ha).val) (e.actualExpression h)).val := by
  have hh : ({c} : Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).normalForm ∈ C := ⟨hc.sort_inj ▸ hs,hm⟩
  dsimp only [product]
  rw [ite_eq_left hm,dite_eq_left hh,withBase_base]
  simp only [Base.update_same]
end PreResult

theorem preEvaluate_read_base {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) (e : Environment (hw := hw) Ω C hno Γ)
    (hM : Ω.profile (M.subst e.images).normalForm ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst e.images).normalForm)) :
    (preEvaluate Ω C hno t e).read.val =
      ((RawValue.base Ω C hno ((preEvaluate Ω C hno t e).val ha).val) (e.actualExpression t.typing)).val := by
  cases t with
  | var ht hd hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | sort ht hax hc =>
      change (Candidates.Top Ω (Expr.sort _ |>.subst e.images).normalForm) = _
      rw [show ((preEvaluate Ω C hno (.sort ht hax hc) e).val ha).val =
        (distinguished Ω C hno (e.activeType ht ha)).val from rfl,distinguished_base]
      rfl
  | product ht d b hr hc => exact PreResult.product_read_base ht d.typing b.typing hr hc _ _ e hM hs ha
  | abstraction ht d b hp hc => exact PreResult.baseRead_eq ht _ hM hs ha
  | application ht f a hc => exact PreResult.baseRead_eq ht _ hM hs ha

omit hno [Fintype S] in
theorem baseGood_active_iff {M : Expr S} {s : S} {σ : Nat → Expr S} {v : Prop}
    (hm : Ω.profile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ))) :
    baseGood Ω C M (.sort s) σ v ↔ v := by
  constructor
  · intro h
    obtain ⟨s',_,_,hv,_⟩ := h hm
    exact hv ha
  · intro hv _
    exact ⟨s,rfl,hs,fun _ => hv,fun hn => False.elim (hn ha)⟩

omit hno [Fintype S] in
theorem readGood_active_iff {Γ : List (Expr S)} {M : Expr S} {s : S}
    (t : TypingTree P Γ M (.sort s)) {σ : Nat → Expr S}
    (hm : Ω.profile (M.subst σ) ∈ C) (hs : ({s} : Set S) ∈ C)
    (ha : ActiveLayer P C (Ω.profile (Expr.sort s |>.subst σ))) :
    ReadGood Ω C t σ ↔ ValGood Ω C t σ := by
  cases t with
  | var ht hd hc => exact baseGood_active_iff Ω C hm hs ha
  | sort ht hax hc => exact Iff.rfl
  | product ht d b hr hc =>
      dsimp only [ReadGood,ValGood,goodness]
      have hc' := hc.sort_inj
      simp only [← hc',hm,hs,true_and,true_implies]
  | abstraction ht d b hp hc => exact baseGood_active_iff Ω C hm hs ha
  | application ht f a hc => exact baseGood_active_iff Ω C hm hs ha
end PureTypeSystem.ObservationValues

end OAI
