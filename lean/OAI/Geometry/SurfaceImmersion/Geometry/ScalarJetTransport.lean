import OAI.Geometry.SurfaceImmersion.Correction.CoordinatePolynomialPullback

namespace OAI

/-! Exact finite jet-polynomial transport under multiplication by a fixed
smooth scalar function. This accounts for the atlas outer cutoffs before
coordinate transport. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinatePartial_mul {a f : Base → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (v : Fin 2) (x : Base) :
    coordinatePartial (fun y => a y * f y) v x =
      a x * coordinatePartial f v x + f x * coordinatePartial a v x := by
  change fderiv ℝ (fun y => a y * f y) x (coordinateVector v) = _
  rw [fderiv_fun_mul (ha.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rfl

lemma coordinatePartial_coordinatePartial_mul {a f : Base → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (v w : Fin 2) (x : Base) :
    coordinatePartial (coordinatePartial (fun y => a y * f y) w) v x =
      a x * coordinatePartial (coordinatePartial f w) v x +
      coordinatePartial f w x * coordinatePartial a v x +
      coordinatePartial a w x * coordinatePartial f v x +
      f x * coordinatePartial (coordinatePartial a w) v x := by
  have he : coordinatePartial (fun y => a y * f y) w =
      fun y => a y * coordinatePartial f w y + f y * coordinatePartial a w y :=
    funext (coordinatePartial_mul ha hf w)
  change fderiv ℝ (coordinatePartial (fun y => a y * f y) w) x (coordinateVector v) = _
  rw [he,fderiv_fun_add
    ((ha.mul (coordinatePartial_smooth hf w)).differentiable (by simp) x)
    ((hf.mul (coordinatePartial_smooth ha w)).differentiable (by simp) x)]
  simp only [add_apply]
  change coordinatePartial (fun y => a y * coordinatePartial f w y) v x +
      coordinatePartial (fun y => f y * coordinatePartial a w y) v x = _
  rw [coordinatePartial_mul ha (coordinatePartial_smooth hf w),
    coordinatePartial_mul hf (coordinatePartial_smooth ha w)]
  ring

def scalarJetFirst (a : Base → ℝ) (x : Base) (J : LowJet) (v : Fin 2) (k : Fin 4) : ℝ :=
  a x * J (.inr (firstJetSlot v,k)) + J (.inr (0,k)) * coordinatePartial a v x

def scalarJetSecond (a : Base → ℝ) (x : Base) (J : LowJet)
    (v w : Fin 2) (k : Fin 4) : ℝ :=
  a x * J (.inr (secondJetSlot v w,k)) +
    J (.inr (firstJetSlot w,k)) * coordinatePartial a v x +
    coordinatePartial a w x * J (.inr (firstJetSlot v,k)) +
    J (.inr (0,k)) * coordinatePartial (coordinatePartial a w) v x

/-- Multiplication preserves the position slots and transforms the value,
first derivatives, and ordered second derivatives by the product rule. -/
def lowJetScalarProduct (a : Base → ℝ) (p : Base × LowJet) : LowJet
  | .inl i => p.1 i
  | .inr (w,k) => ![a p.1 * p.2 (.inr (0,k)),
      scalarJetFirst a p.1 p.2 0 k,
      scalarJetFirst a p.1 p.2 1 k,
      scalarJetSecond a p.1 p.2 0 0 k,
      scalarJetSecond a p.1 p.2 0 1 k,
      scalarJetSecond a p.1 p.2 1 0 k,
      scalarJetSecond a p.1 p.2 1 1 k] w

lemma scalarJetFirst_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (v : Fin 2) (k : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => scalarJetFirst a p.1 p.2 v k) := by
  exact ((ha.comp contDiff_fst).mul
    ((ContinuousLinearMap.proj (.inr (firstJetSlot v,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)).add
    (((ContinuousLinearMap.proj (.inr (0,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
      ((coordinatePartial_smooth ha v).comp contDiff_fst))

lemma scalarJetSecond_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (v w : Fin 2) (k : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => scalarJetSecond a p.1 p.2 v w k) := by
  have hp (i : Fin 7) : ContDiff ℝ ∞ (fun p : Base × LowJet => p.2 (.inr (i,k))) :=
    (ContinuousLinearMap.proj (.inr (i,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd
  exact ((((ha.comp contDiff_fst).mul (hp (secondJetSlot v w))).add
    ((hp (firstJetSlot w)).mul ((coordinatePartial_smooth ha v).comp contDiff_fst))).add
    (((coordinatePartial_smooth ha w).comp contDiff_fst).mul (hp (firstJetSlot v)))).add
    ((hp 0).mul ((coordinatePartial_smooth (coordinatePartial_smooth ha w) v).comp contDiff_fst))

lemma lowJetScalarProduct_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (lowJetScalarProduct a) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i =>
    exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))
  | inr i =>
    rcases i with ⟨w,k⟩
    fin_cases w
    · have hp : ContDiff ℝ ∞
          (fun p : Base × LowJet => p.2 (Sum.inr ((0 : Fin 7),k))) :=
        (ContinuousLinearMap.proj (Sum.inr ((0 : Fin 7),k) : LowIndex) : LowJet →L[ℝ] ℝ).contDiff.comp
          (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Base × LowJet → LowJet))
      exact (ha.comp
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))).mul hp
    · exact scalarJetFirst_smooth ha 0 k
    · exact scalarJetFirst_smooth ha 1 k
    · exact scalarJetSecond_smooth ha 0 0 k
    · exact scalarJetSecond_smooth ha 0 1 k
    · exact scalarJetSecond_smooth ha 1 0 k
    · exact scalarJetSecond_smooth ha 1 1 k

lemma lowJetScalarProduct_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (x : Base) :
    lowJetScalarProduct a (x,lowJet G x) = lowJet (fun y => a y • G y) x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    rcases i with ⟨w,k⟩
    have hfirst (v : Fin 2) : scalarJetFirst a x (lowJet G x) v k =
        coordinatePartial (fun y => a y * G y k) v x := by
      rw [coordinatePartial_mul ha (contDiff_pi.mp hG k)]
      simp only [scalarJetFirst,lowJet_first_slot]
      rfl
    have hsecond (v w : Fin 2) : scalarJetSecond a x (lowJet G x) v w k =
        coordinatePartial (coordinatePartial (fun y => a y * G y k) w) v x := by
      rw [coordinatePartial_coordinatePartial_mul ha (contDiff_pi.mp hG k)]
      simp only [scalarJetSecond,lowJet_first_slot,lowJet_second_slot]
      rfl
    fin_cases w
    · rfl
    · exact hfirst 0
    · exact hfirst 1
    · exact hsecond 0 0
    · exact hsecond 0 1
    · exact hsecond 1 0
    · exact hsecond 1 1

/-- The smooth coefficient substitution needs no separate position input
because an actual low jet already stores its base point. -/
def scalarLowJetSubstitution (a : Base → ℝ) (J : LowJet) : LowJet :=
  lowJetScalarProduct a (lowPosition J,J)

lemma scalarLowJetSubstitution_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (scalarLowJetSubstitution a) :=
  (lowJetScalarProduct_smooth ha).comp (lowPosition.contDiff.prodMk contDiff_id)

@[simp] lemma scalarLowJetSubstitution_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (x : Base) :
    scalarLowJetSubstitution a (lowJet G x) = lowJet (fun y => a y • G y) x := by
  simpa only [scalarLowJetSubstitution,lowPosition_lowJet] using lowJetScalarProduct_eval ha hG x

/-- Every ordered derivative of the scalar product is a finite expression.
Repeated formal slow differentiation supplies the exact Leibniz expansion. -/
def scalarProductAtom (a : Base → ℝ) : List (Fin 2) → Fin 4 → Expression
  | [],k => .atom [] k (.coeff (fun z => a (lowPosition z.1)))
  | v::w,k => (scalarProductAtom a w k).slow v

lemma scalarProductAtom_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (w : List (Fin 2)) (k : Fin 4) : (scalarProductAtom a w k).SmoothCoeffs univ := by
  induction w with
  | nil => exact (ha.comp (lowPosition.contDiff.comp contDiff_fst)).contDiffOn
  | cons v w ih => exact Expression.smoothCoeffs_slow isOpen_univ v ih

lemma scalarProductAtom_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G)
    (w : List (Fin 2)) (k : Fin 4) (t : ℝ) (x : Base) :
    (scalarProductAtom a w k).eval G (x,t) = jet (fun y => a y • G y) w k x := by
  induction w generalizing x with
  | nil =>
    change G x k * a (lowPosition (lowJet G x)) = a x * G x k
    rw [lowPosition_lowJet]
    ring
  | cons v w ih =>
    rw [scalarProductAtom,Expression.eval_slow isOpen_univ isOpen_univ hG
      (mapsTo_univ _ _) v (scalarProductAtom_smooth ha w k) (mem_univ x) t]
    have he : (fun y => (scalarProductAtom a w k).eval G (y,t)) =
        jet (fun y => a y • G y) w k := funext ih
    rw [he]
    rfl

namespace Expression

/-- Substitute the complete finite jet polynomial of the fixed scalar
product, including positional low-jet coefficients. -/
def scalarProductPullback (a : Base → ℝ) : Expression → Expression
  | .coeff c => .coeff (fun z => c (scalarLowJetSubstitution a z.1,z.2))
  | .atom w k e => (scalarProductAtom a w k).mul (scalarProductPullback a e)
  | .add e f => .add (scalarProductPullback a e) (scalarProductPullback a f)

lemma scalarProductPullback_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (scalarProductPullback a e).SmoothCoeffs univ := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c :=
      contDiffOn_univ.mp (by simpa only [SmoothCoeffs,univ_prod_univ] using he)
    exact (hc.comp (((scalarLowJetSubstitution_smooth ha).comp contDiff_fst).prodMk
      contDiff_snd)).contDiffOn
  | atom w k e ih => exact smoothCoeffs_mul (scalarProductAtom_smooth ha w k) (ih he)
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩

lemma scalarProductPullback_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (e : Expression) (t : ℝ) (x : Base) :
    (scalarProductPullback a e).eval G (x,t) = e.eval (fun y => a y • G y) (x,t) := by
  induction e with
  | coeff c =>
    change c (scalarLowJetSubstitution a (lowJet G x),t) = _
    rw [scalarLowJetSubstitution_eval ha hG]
    rfl
  | atom w k e ih =>
    rw [scalarProductPullback,eval_mul,scalarProductAtom_eval ha hG,ih]
    rfl
  | add e f ihe ihf =>
    change (scalarProductPullback a e).eval G (x,t) +
      (scalarProductPullback a f).eval G (x,t) = _
    rw [ihe,ihf]
    rfl

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
