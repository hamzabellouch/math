import OAI.RepresentationTheory.KazhdanLusztig.Tits
import OAI.RepresentationTheory.KazhdanLusztig.ModuleAlgebra

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

def coordinatePolynomial (a : I → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.monomial (Fintype.equivFin I i).val (a i)

theorem coordinatePolynomial_coeff (a : I → ℝ) (j : I) :
    (coordinatePolynomial a).coeff (Fintype.equivFin I j).val = a j := by
  classical
  rw [coordinatePolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : (Fintype.equivFin I i).val ≠ (Fintype.equivFin I j).val := by
      intro h
      exact hij ((Fintype.equivFin I).injective (Fin.ext h))
    simp [Polynomial.coeff_monomial,hne]
  · simp

theorem coordinatePolynomial_injective : Function.Injective (coordinatePolynomial (I := I)) := by
  intro a b h
  funext i
  simpa only [coordinatePolynomial_coeff] using congrArg (fun p : ℝ[X] => p.coeff
    (Fintype.equivFin I i).val) h

def momentFunctional (t : ℝ) : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i * t^(Fintype.equivFin I i).val
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum,mul_assoc]

theorem coordinatePolynomial_eval (a : I → ℝ) (t : ℝ) :
    (coordinatePolynomial a).eval t = momentFunctional t a := by
  simp [coordinatePolynomial,momentFunctional,Polynomial.eval_finsetSum]


theorem exists_generic_functional {A : Type v} [Countable A]
    (v : A → (I → ℝ)) (hv : Function.Injective v) :
    ∃ f : Module.Dual ℝ (I → ℝ), Function.Injective (fun a => f (v a)) := by
  classical
  let P := {p : A × A // p.1 ≠ p.2}
  let d : P → ℝ[X] := fun p => coordinatePolynomial (v p.val.1) - coordinatePolynomial (v p.val.2)
  have hd : ∀ p, d p ≠ 0 := by
    intro p h
    exact p.property (hv (coordinatePolynomial_injective (sub_eq_zero.mp h)))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  have hex : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have heq : bad = Set.univ := Set.eq_univ_of_forall h
    rw [heq] at hbad
    exact Set.not_countable_univ hbad
  obtain ⟨t,ht⟩ := hex
  refine ⟨momentFunctional t,fun a b hab => ?_⟩
  change momentFunctional t (v a) = momentFunctional t (v b) at hab
  by_contra hne
  apply ht
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(a,b),hne⟩,?_⟩
  change (coordinatePolynomial (v a) - coordinatePolynomial (v b)).eval t = 0
  rw [Polynomial.eval_sub,coordinatePolynomial_eval,coordinatePolynomial_eval,hab,sub_self]

end
end KLInvariance.ReflectionSchedules

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

def height : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum]

variable {M cs}

theorem PositiveRoot.height_pos (a : PositiveRoot M cs) : 0 < height a.val := by
  classical
  have hex : ∃ i, a.val i ≠ 0 := by
    by_contra h
    push Not at h
    exact a.property.1.ne_zero (funext h)
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => a.property.2 j)
    ⟨i,Finset.mem_univ _,lt_of_le_of_ne' (a.property.2 i) hi⟩

def normalizedRoot (a : PositiveRoot M cs) : I → ℝ := (height a.val)⁻¹ • a.val

theorem normalizedRoot_injective : Function.Injective (normalizedRoot (M := M) (cs := cs)) := by
  intro a b hab
  have ha : 0 < (height a.val)⁻¹ := inv_pos.mpr a.height_pos
  have hb : 0 < (height b.val)⁻¹ := inv_pos.mpr b.height_pos
  have hn := congrArg (fun v => form M v v) hab
  change form M ((height a.val)⁻¹ • a.val) ((height a.val)⁻¹ • a.val) =
    form M ((height b.val)⁻¹ • b.val) ((height b.val)⁻¹ • b.val) at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm,b.property.1.norm] at hn
  have hh : (height a.val)⁻¹ = (height b.val)⁻¹ := by nlinarith
  apply Subtype.ext
  change (height a.val)⁻¹ • a.val = (height b.val)⁻¹ • b.val at hab
  rw [← hh] at hab
  exact (smul_right_injective _ ha.ne').eq_iff.mp hab

variable (M cs)

theorem countable_Positiveroot : Countable (PositiveRoot M cs) := by
  let : Countable W := cs.wordProd_surjective.countable
  exact Countable.of_equiv {t : W // cs.IsReflection t} (positiveRootEquiv M cs)


theorem exists_geometric_functional : ∃ f : Module.Dual ℝ (I → ℝ),
    Function.Injective (fun a : PositiveRoot M cs => f a.val / height a.val) := by
  let := countable_Positiveroot M cs
  obtain ⟨f,hf⟩ := ReflectionSchedules.exists_generic_functional
    (normalizedRoot (M := M) (cs := cs)) normalizedRoot_injective
  refine ⟨f,?_⟩
  convert hf using 1
  funext a
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

/-- Betweenness of all positive combinations is the angular-order condition
on every root plane. This is the genuine geometric reflection-order property. -/
theorem functionalRatio_between (f : Module.Dual ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hc : c.val = r • a.val + s • b.val)
    (hab : f a.val / height a.val < f b.val / height b.val) :
    f a.val / height a.val < f c.val / height c.val ∧
      f c.val / height c.val < f b.val / height b.val := by
  have ha := a.height_pos
  have hb := b.height_pos
  have hh := c.height_pos
  have hfc : f c.val = r*f a.val+s*f b.val := by rw [hc]; simp
  have hhc : height c.val = r*height a.val+s*height b.val := by rw [hc]; simp
  rw [div_lt_div_iff₀ ha hb] at hab
  constructor
  · rw [div_lt_div_iff₀ ha hh,hfc,hhc]
    nlinarith [mul_pos hs (sub_pos.mpr hab)]
  · rw [div_lt_div_iff₀ hh hb,hfc,hhc]
    nlinarith [mul_pos hr (sub_pos.mpr hab)]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Conjugation on the actual root lines, represented by positive roots. -/
def positiveAction (w : W) (a : PositiveRoot M cs) : PositiveRoot M cs :=
  positiveRoot M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_represents (w : W) (a : PositiveRoot M cs) :
    Represents M cs (w * (rootReflection M cs a).val * w⁻¹) (positiveAction w a).val :=
  positiveRoot_represents M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_eq_of_nonneg (w : W) (a : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs w a.val i) :
    (positiveAction w a).val = action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w) (positiveAction w a).property.2 hp

theorem positiveAction_eq_of_nonpos (w : W) (a : PositiveRoot M cs)
    (hn : ∀ i, action M cs w a.val i ≤ 0) :
    (positiveAction w a).val = -action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w).neg (positiveAction w a).property.2
    (fun i => neg_nonneg.mpr (hn i))

@[simp] theorem rootReflection_positiveAction (w : W) (a : PositiveRoot M cs) :
    (rootReflection M cs (positiveAction w a)).val = w*(rootReflection M cs a).val*w⁻¹ :=
  (rootReflection_represents M cs _).reflection_unique (positiveAction_represents w a)

@[simp] theorem positiveAction_one (a : PositiveRoot M cs) : positiveAction 1 a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction 1 a)).val = (rootReflection M cs a).val
  simp

theorem positiveAction_mul (w z : W) (a : PositiveRoot M cs) :
    positiveAction (w*z) a = positiveAction w (positiveAction z a) := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (w*z) a)).val =
    (rootReflection M cs (positiveAction w (positiveAction z a))).val
  simp only [rootReflection_positiveAction]
  group

def positiveActionEquiv (w : W) : Equiv.Perm (PositiveRoot M cs) where
  toFun := positiveAction w
  invFun := positiveAction w⁻¹
  left_inv a := by rw [← positiveAction_mul, inv_mul_cancel, positiveAction_one]
  right_inv a := by rw [← positiveAction_mul, mul_inv_cancel, positiveAction_one]

abbrev rootRef (a : PositiveRoot M cs) : W := (rootReflection M cs a).val

theorem positiveAction_involutive (a : PositiveRoot M cs) :
    Function.Involutive (positiveAction (M := M) (cs := cs) (rootRef a)) := by
  intro b
  rw [← positiveAction_mul, (rootReflection M cs a).property.mul_self, positiveAction_one]

def rootInverted (w : W) (a : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs w⁻¹ a.val i ≤ 0

theorem not_rootInverted_iff (w : W) (a : PositiveRoot M cs) :
    ¬ rootInverted w a ↔ ∀ i, 0 ≤ action M cs w⁻¹ a.val i := by
  constructor
  · intro hn
    exact (a.property.1.act w⁻¹).sign.resolve_right hn
  · intro hp hn
    exact (a.property.1.act w⁻¹).not_both hp hn

theorem rootInverted_mul_of_nonneg (x : W) (a b : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs (rootRef a) b.val i) :
    rootInverted (rootRef a*x) b ↔ rootInverted x (positiveAction (rootRef a) b) := by
  unfold rootInverted
  rw [positiveAction_eq_of_nonneg _ _ hp, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul]
  rfl

theorem rootInverted_mul_of_nonpos (x : W) (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    rootInverted (rootRef a*x) b ↔ ¬ rootInverted x (positiveAction (rootRef a) b) := by
  rw [not_rootInverted_iff]
  unfold rootInverted
  rw [positiveAction_eq_of_nonpos _ _ hn, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul, map_neg]
  simp only [LinearEquiv.mul_apply, Pi.neg_apply, neg_nonneg]

theorem negative_pair_sum (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    b.val + (positiveAction (rootRef a) b).val = form M a.val b.val • a.val := by
  rw [positiveAction_eq_of_nonpos _ _ hn, (rootReflection_represents M cs a).action_formula]
  module

theorem negative_pair_coefficient_pos (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) : 0 < form M a.val b.val := by
  have h := congrArg (fun z => height z) (negative_pair_sum a b hn)
  simp only [map_add,map_smul,smul_eq_mul] at h
  have hp := b.height_pos
  have hq := (positiveAction (rootRef a) b).height_pos
  have ha := a.height_pos
  nlinarith

/-- The crucial direct positivity argument: over an ascent in alpha, the
negative root-pair for its reflection cannot both already be inversions.
This works in degenerate planes and does not assume a dihedral presentation. -/
theorem negative_pair_not_both (x : W) (a b : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    ¬ (rootInverted x b ∧ rootInverted x (positiveAction (rootRef a) b)) := by
  rintro ⟨hb,hc⟩
  have hp := (not_rootInverted_iff x a).mp hx
  have hs := congrArg (action M cs x⁻¹) (negative_pair_sum a b hn)
  simp only [map_add,map_smul] at hs
  have hcoef := negative_pair_coefficient_pos a b hn
  have hna : ∀ i, action M cs x⁻¹ a.val i ≤ 0 := by
    intro i
    have hi := congrFun hs i
    change action M cs x⁻¹ b.val i +
      action M cs x⁻¹ (positiveAction (rootRef a) b).val i =
        form M a.val b.val * action M cs x⁻¹ a.val i at hi
    have hb' := hb i
    have hc' := hc i
    nlinarith
  exact (a.property.1.act x⁻¹).not_both hp hna

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_rootInverted (w : W) : {a : PositiveRoot M cs | rootInverted w a}.Finite := by
  exact Set.finite_coe_iff.mp (rootInversions_finite M cs w)

def inversionVector (w : W) : PositiveRoot M cs →₀ ℤ := by
  classical
  refine Finsupp.ofSupportFinite (fun a => if rootInverted w a then 1 else 0) ?_
  simpa only [Function.support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] using finite_rootInverted (M := M) (cs := cs) w

@[simp] theorem inversionVector_apply (w : W) (a : PositiveRoot M cs) :
    inversionVector w a = if rootInverted w a then 1 else 0 := by
  classical
  rfl

theorem inversionVector_sum (w : W) : (inversionVector (M := M) (cs := cs) w).sum
    (fun _ n => n) = (cs.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) w
  have hh : f.support.card = cs.length w := by
    have heq : (f.support : Set (PositiveRoot M cs)) = {a | rootInverted w a} := by
      ext a
      simp [f]
    rw [← Set.ncard_coe_finset, heq, ← Nat.card_coe_set_eq]
    exact card_rootInversions M cs w
  rw [Finsupp.sum]
  calc
    ∑ a ∈ f.support, f a = ∑ _a ∈ f.support, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm := Finsupp.mem_support_iff.mp ha
      by_cases hi : rootInverted w a
      · simp [f,hi]
      · simp [f,hi] at hm
    _ = _ := by simp [hh]

def rootChange (x y : W) : PositiveRoot M cs →₀ ℤ := inversionVector y - inversionVector x

def rootPlane (a b : PositiveRoot M cs) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ {a.val,b.val}

/-- The finitely supported change in root inversions, with the distinguished
root removed, grouped by actual root planes. -/
def planeDefect (x y : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) ((rootChange x y).erase a)

theorem rootInverted_mul_self (x : W) (a : PositiveRoot M cs) :
    rootInverted (rootRef a*x) a ↔ ¬ rootInverted x a := by
  have h := (rootReflection M cs a).property.isLeftInversion_mul_right_iff (w := x)
  simpa only [rootInverted, ← (rootReflection_represents M cs a).inversion_iff a.property.2] using h

theorem rootChange_distinguished (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a) : rootChange x (rootRef a*x) a = 1 := by
  classical
  simp only [rootChange, Finsupp.sub_apply, inversionVector_apply,
    (rootInverted_mul_self x a).mpr hx, hx, ite_true, ite_false, sub_zero]


theorem planeDefect_sum (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (planeDefect x (rootRef a*x) a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  classical
  rw [planeDefect, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.erase_eq_sub_single, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, rootChange_distinguished x a hx,
    rootChange, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    inversionVector_sum, inversionVector_sum]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev partner (a b : PositiveRoot M cs) := positiveAction (rootRef a) b

theorem partner_self (a : PositiveRoot M cs) : partner a a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (rootRef a) a)).val = rootRef a
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.mul_self, one_mul,
    (rootReflection M cs a).property.inv]

theorem partner_involutive (a : PositiveRoot M cs) : Function.Involutive (partner a) :=
  positiveAction_involutive a

theorem partner_eq_self_of_eq (a b : PositiveRoot M cs) : partner a b = a ↔ b = a := by
  constructor
  · intro h
    have hh := congrArg (partner a) h
    rwa [partner_involutive a b,partner_self] at hh
  · rintro rfl
    exact partner_self _

abbrev flipped (a b : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs (rootRef a) b.val i ≤ 0

theorem flipped_partner_iff (a b : PositiveRoot M cs) : flipped a (partner a b) ↔ flipped a b := by
  have hact : action M cs (rootRef a) * action M cs (rootRef a) = 1 := by
    rw [← map_mul, (rootReflection M cs a).property.mul_self, map_one]
  by_cases hb : flipped a b
  · have heq := positiveAction_eq_of_nonpos (rootRef a) b hb
    have hp : flipped a (partner a b) := by
      intro i
      change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0
      rw [heq,map_neg, ← LinearEquiv.mul_apply,hact]
      exact neg_nonpos.mpr (b.property.2 i)
    exact iff_of_true hp hb
  · have hpos := (b.property.1.act (rootRef a)).sign.resolve_right hb
    have heq := positiveAction_eq_of_nonneg (rootRef a) b hpos
    have hp : ¬ flipped a (partner a b) := by
      intro hh
      have hneg : ∀ i, b.val i ≤ 0 := by
        intro i
        have hi := hh i
        change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0 at hi
        rwa [heq, ← LinearEquiv.mul_apply, hact] at hi
      exact b.property.1.not_both b.property.2 hneg
    exact iff_of_false hp hb

theorem partner_mem {P : Submodule ℝ (I → ℝ)} (a b : PositiveRoot M cs)
    (ha : a.val ∈ P) (hb : b.val ∈ P) : (partner a b).val ∈ P := by
  have hm : action M cs (rootRef a) b.val ∈ P := by
    rw [(rootReflection_represents M cs a).action_formula]
    exact P.sub_mem hb (P.smul_mem _ ha)
  rcases (b.property.1.act (rootRef a)).sign with hp|hn
  · exact (positiveAction_eq_of_nonneg (rootRef a) b hp).symm ▸ hm
  · exact (positiveAction_eq_of_nonpos (rootRef a) b hn).symm ▸ P.neg_mem hm

theorem rootPlane_partner (a b : PositiveRoot M cs) : rootPlane a (partner a b) = rootPlane a b := by
  have hle (b : PositiveRoot M cs) : rootPlane a (partner a b) ≤ rootPlane a b := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact partner_mem a b (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  exact le_antisymm (hle b) (by simpa only [partner_involutive a b] using hle (partner a b))

theorem negative_partner_fixed (a b : PositiveRoot M cs) (hn : flipped a b)
    (heq : partner a b = b) : b = a := by
  have hs := negative_pair_sum a b hn
  change b.val + (partner a b).val = form M a.val b.val • a.val at hs
  rw [heq] at hs
  have hc := negative_pair_coefficient_pos a b hn
  have hb : b.val = (form M a.val b.val / 2) • a.val := by
    calc
      b.val = (1/2:ℝ) • (b.val+b.val) := by module
      _ = _ := by rw [hs]; module
  have hnorm := b.property.1.norm
  rw [hb] at hnorm
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm] at hnorm
  have hc2 : form M a.val b.val / 2 = 1 := by nlinarith
  apply Subtype.ext
  simpa only [hc2,one_smul] using hb

/-- Roots in a negative pair which are both positive before the ascent. -/
def goodPairRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  flipped a b ∧ ¬ rootInverted x b ∧ ¬ rootInverted x (partner a b)

theorem goodPairRoot_partner (x : W) (a b : PositiveRoot M cs) :
    goodPairRoot x a (partner a b) ↔ goodPairRoot x a b := by
  simp only [goodPairRoot,flipped_partner_iff,partner_involutive a b]
  tauto

/-- The pairwise change is either zero or two, with no negative case. -/
theorem rootChange_pair (x : W) (a b : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    rootChange x (rootRef a*x) b + rootChange x (rootRef a*x) (partner a b) =
      if goodPairRoot x a b then 2 else 0 := by
  by_cases hn : flipped a b
  · have hn' := (flipped_partner_iff a b).mpr hn
    have hi := rootInverted_mul_of_nonpos x a b hn
    have hi' := rootInverted_mul_of_nonpos x a (partner a b) hn'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    have hnnb := negative_pair_not_both x a b hx hn
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,]
    by_cases hb : rootInverted x b <;> by_cases hc : rootInverted x (partner a b) <;>
      simp_all
  · have hp := (b.property.1.act (rootRef a)).sign.resolve_right hn
    have hn' := mt (flipped_partner_iff a b).mp hn
    have hp' := ((partner a b).property.1.act (rootRef a)).sign.resolve_right hn'
    have hi := rootInverted_mul_of_nonneg x a b hp
    have hi' := rootInverted_mul_of_nonneg x a (partner a b) hp'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,hn,false_and,ite_false]
    ring

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def geometricFunctional : Module.Dual ℝ (I → ℝ) := (exists_geometric_functional M cs).choose

def geometricSlope (a : PositiveRoot M cs) : ℝ := geometricFunctional (M := M) (cs := cs) a.val / height a.val

theorem geometricSlope_injective : Function.Injective (geometricSlope (M := M) (cs := cs)) :=
  (exists_geometric_functional M cs).choose_spec

@[instance_reducible]
def geometricOrder : LinearOrder (PositiveRoot M cs) := LinearOrder.lift' geometricSlope geometricSlope_injective

theorem geometricSlope_between (a b c : PositiveRoot M cs) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : c.val = r • a.val+s • b.val)
    (hab : geometricSlope a < geometricSlope b) :
    geometricSlope a < geometricSlope c ∧ geometricSlope c < geometricSlope b :=
  functionalRatio_between M cs (geometricFunctional (M := M) (cs := cs)) a b c hr hs hc hab

def partnerEquiv (a : PositiveRoot M cs) : Equiv.Perm (PositiveRoot M cs) :=
  Function.Involutive.toPerm (partner a) (partner_involutive a)

@[simp] theorem partnerEquiv_apply (a b : PositiveRoot M cs) : partnerEquiv a b = partner a b := rfl
@[simp] theorem partnerEquiv_symm_apply (a b : PositiveRoot M cs) : (partnerEquiv a).symm b = partner a b := rfl

def extraRoot (x : W) (a b : PositiveRoot M cs) : Prop := b ≠ a ∧ goodPairRoot x a b

theorem extraRoot_partner (x : W) (a b : PositiveRoot M cs) :
    extraRoot x a (partner a b) ↔ extraRoot x a b := by
  simp only [extraRoot,ne_eq,partner_eq_self_of_eq,goodPairRoot_partner]

theorem extraRoot_finite (x : W) (a : PositiveRoot M cs) : {b | extraRoot x a b}.Finite := by
  apply (finite_rootInverted (M := M) (cs := cs) (rootRef a*x)).subset
  intro b hb
  exact (rootInverted_mul_of_nonpos x a b hb.2.1).mpr hb.2.2.2

def halfRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  extraRoot x a b ∧ geometricSlope b < geometricSlope (partner a b)

theorem halfRoot_finite (x : W) (a : PositiveRoot M cs) : {b | halfRoot x a b}.Finite :=
  (extraRoot_finite x a).subset (fun _ h => h.1)

def rootIndicator (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite) : PositiveRoot M cs →₀ ℤ :=
  Finsupp.ofSupportFinite (fun a => if p a then 1 else 0) (by
    simpa only [Function.support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hp)

@[simp] theorem rootIndicator_apply (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite)
    (a : PositiveRoot M cs) : rootIndicator p hp a = if p a then 1 else 0 := rfl

def extraVector (x : W) (a : PositiveRoot M cs) := rootIndicator (extraRoot x a) (extraRoot_finite x a)
def halfVector (x : W) (a : PositiveRoot M cs) := rootIndicator (halfRoot x a) (halfRoot_finite x a)

/-- A choice of one root in each actual two-element negative pair. -/
theorem extraVector_eq_half (x : W) (a : PositiveRoot M cs) :
    extraVector x a = halfVector x a + Finsupp.mapDomain (partnerEquiv a) (halfVector x a) := by
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply,
    extraVector,halfVector,rootIndicator_apply,halfRoot,extraRoot_partner,partner_involutive a b]
  by_cases hb : extraRoot x a b
  · have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hb.1 (negative_partner_fixed a b hb.2.1 (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with h|h
    · simp [hb,h,not_lt_of_gt h]
    · simp [hb,h,not_lt_of_gt h]
  · simp [hb]

/-- All apparent negative contributions cancel under the actual reflection on
root lines; the remaining pairs are precisely `extraVector`. -/
theorem erasedChange_pair (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (rootChange x (rootRef a*x)).erase a +
      Finsupp.mapDomain (partnerEquiv a) ((rootChange x (rootRef a*x)).erase a) =
        extraVector x a + extraVector x a := by
  classical
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply]
  by_cases hb : b=a
  · subst b
    simp [partner_self,extraVector,extraRoot]
  · have hpb : partner a b ≠ a := mt (partner_eq_self_of_eq a b).mp hb
    rw [Finsupp.erase_ne hb,Finsupp.erase_ne hpb,rootChange_pair x a b hx]
    simp only [extraVector,rootIndicator_apply,extraRoot,]
    by_cases hg : goodPairRoot x a b <;> simp [hg,hb]

theorem mapDomain_plane_partner (a : PositiveRoot M cs) (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (Finsupp.mapDomain (partnerEquiv a) f) =
      Finsupp.mapDomain (rootPlane a) f := by
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro b _
  exact rootPlane_partner a b

def planeWeight (x : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) (halfVector x a)


theorem planeDefect_eq_double_weight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a = planeWeight x a + planeWeight x a := by
  have h := congrArg (Finsupp.mapDomain (rootPlane a)) (erasedChange_pair x a hx)
  rw [Finsupp.mapDomain_add,mapDomain_plane_partner,Finsupp.mapDomain_add] at h
  have heq : planeDefect x (rootRef a*x) a = Finsupp.mapDomain (rootPlane a) (extraVector x a) := by
    ext P
    have hh := congrArg (fun f : Submodule ℝ (I → ℝ) →₀ ℤ => f P) h
    simp only [Finsupp.add_apply] at hh
    change planeDefect x (rootRef a*x) a P = _
    dsimp [planeDefect]
    omega
  rw [heq,extraVector_eq_half,Finsupp.mapDomain_add,mapDomain_plane_partner]
  rfl

theorem planeWeight_nonneg (x : W) (a : PositiveRoot M cs) (P : Submodule ℝ (I → ℝ)) :
    0 ≤ planeWeight x a P := by
  classical
  rw [planeWeight,Finsupp.mapDomain,Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro b _
  simp only [Finsupp.single_apply,halfVector,rootIndicator_apply]
  split_ifs <;> norm_num

/-- Exact ambient degree formula, with actual roots, finite support and
nonnegative integral planar weights; no labeled interval isomorphism enters. -/
theorem sum_planeWeight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    2 * (planeWeight x a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  have h := planeDefect_sum x a hx
  rw [planeDefect_eq_double_weight x a hx,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at h
  linarith

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem positiveRoots_independent (a b : PositiveRoot M cs) (hab : a ≠ b) :
    LinearIndependent ℝ ![a.val,b.val] := by
  apply (rootReflection_represents M cs a).independent_of_ne (rootReflection_represents M cs b)
  intro h
  apply hab
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootPlane_finrank (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Module.finrank ℝ (rootPlane a b) = 2 := by
  have h := finrank_span_eq_card (positiveRoots_independent a b hab)
  have hrange : Set.range ![a.val,b.val] = {a.val,b.val} := by
    ext z
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [hrange] at h
  exact h

theorem rootPlane_self_finrank (a : PositiveRoot M cs) :
    Module.finrank ℝ (rootPlane a a) = 1 := by
  have hset : ({a.val,a.val} : Set (I → ℝ)) = {a.val} := by ext z; simp
  rw [rootPlane,hset]
  exact finrank_span_singleton (K := ℝ) (a.property.1.ne_zero)

theorem rootPlane_eq_iff (a b c : PositiveRoot M cs) (hab : a ≠ b) :
    rootPlane a c = rootPlane a b ↔ c ≠ a ∧ c.val ∈ rootPlane a b := by
  constructor
  · intro h
    constructor
    · intro hc
      subst c
      have h' := congrArg (fun P : Submodule ℝ (I → ℝ) => Module.finrank ℝ P) h
      rw [rootPlane_self_finrank,rootPlane_finrank a b hab] at h'
      norm_num at h'
    · rw [← h]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hc,hcP⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro z hz
      rcases (Set.mem_insert_iff.mp hz) with rfl|hz
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · have hzc := Set.mem_singleton_iff.mp hz
        subst z
        exact hcP
    · rw [rootPlane_finrank a c (Ne.symm hc),rootPlane_finrank a b hab]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual finite count of ambient inversions belonging to a root plane.
No Coxeter presentation of the plane subgroup is assumed here. -/
def planeLength (P : Submodule ℝ (I → ℝ)) (w : W) : ℤ :=
  (inversionVector (M := M) (cs := cs) w).sum (fun a n => if a.val ∈ P then n else 0)

theorem rootPlane_grouped_erase (a b : PositiveRoot M cs) (hab : a ≠ b)
    (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      f.sum (fun c n => if c.val ∈ rootPlane a b then n else 0) - f a := by
  classical
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have heq : Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      (f.erase a).sum (fun c n => if c.val ∈ rootPlane a b then n else 0) := by
    rw [Finsupp.mapDomain,Finsupp.sum_apply]
    apply Finset.sum_congr rfl
    intro c hc
    have hca : c ≠ a := by
      intro h
      subst c
      simp only [Finsupp.mem_support_iff,Finsupp.erase_same,ne_eq,not_true_eq_false] at hc
    change (Finsupp.single (rootPlane a c) ((f.erase a) c)) (rootPlane a b) =
      (if c.val ∈ rootPlane a b then (f.erase a) c else 0)
    rw [Finsupp.single_apply]
    by_cases hm : c.val ∈ rootPlane a b
    · rw [ite_eq_left ((rootPlane_eq_iff a b c hab).mpr ⟨hca,hm⟩),ite_eq_left hm]
    · rw [ite_eq_right (fun heq => hm ((rootPlane_eq_iff a b c hab).mp heq).2),ite_eq_right hm]
  rw [heq,Finsupp.erase_eq_sub_single,
    Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp),
    Finsupp.sum_single_index (by simp),ite_eq_left haP]

theorem planeDefect_eq_relative_difference (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  rw [planeDefect,rootPlane_grouped_erase a b hab,rootChange_distinguished x a hx,
    rootChange,Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp)]
  rfl


theorem planeWeight_relative_degree (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    2 * planeWeight x a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  have h := planeDefect_eq_relative_difference x a b hab hx
  rw [planeDefect_eq_double_weight x a hx,Finsupp.add_apply] at h
  linarith

end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_injective : Function.Injective (SymmetricAlgebra.ι k V) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  by_contra hn
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
  have h := congrArg (SymmetricAlgebra.lift f) (LinearMap.mem_ker.mp hv)
  rw [SymmetricAlgebra.lift_ι_apply,map_zero] at h
  exact hf h


def rootIdeal (a : V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span {SymmetricAlgebra.ι k V a}

def rootLine (a : V) : Submodule k V := Submodule.span k {a}

def symQuotientMap (a : V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a)).comp (rootLine (k := k) a).mkQ)

@[simp] theorem symQuotientMap_ι (a v : V) :
    symQuotientMap a (SymmetricAlgebra.ι k V v) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem rootIdeal_le_ker (a : V) : rootIdeal (k := k) a ≤ RingHom.ker (symQuotientMap a) := by
  apply Ideal.span_le.mpr
  intro z hz
  have hz' := Set.mem_singleton_iff.mp hz
  subst z
  change symQuotientMap a (SymmetricAlgebra.ι k V a) = 0
  rw [symQuotientMap_ι]
  have ha : (rootLine (k := k) a).mkQ a = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr (Submodule.subset_span (Set.mem_singleton a))
  rw [ha,map_zero]

def quotientForward (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) →ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  Ideal.Quotient.liftₐ _ (symQuotientMap a) (fun _ hz => rootIdeal_le_ker a hz)

def quotientRootMap (a : V) : V ⧸ rootLine (k := k) a →ₗ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) :=
  (rootLine (k := k) a).liftQ ((Ideal.Quotient.mkₐ k (rootIdeal (k := k) a)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    apply Submodule.span_le.mpr
    intro v hv
    have hv' := Set.mem_singleton_iff.mp hv
    subst v
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

def quotientBackward (a : V) : SymmetricAlgebra k (V ⧸ rootLine (k := k) a) →ₐ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) := SymmetricAlgebra.lift (quotientRootMap a)

@[simp] theorem quotientForward_mk (a : V) (z : SymmetricAlgebra k V) :
    quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = symQuotientMap a z := rfl

@[simp] theorem quotientBackward_ι_mk (a v : V) :
    quotientBackward a (SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v)) =
      Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) := by
  rw [quotientBackward,SymmetricAlgebra.lift_ι_apply]
  rfl

/-- Exact coefficient-ring identification used for the manuscript's C=A/(alpha).
This is an isomorphism of the actual quotient, not a replacement invariant. -/
def rootQuotientEquiv (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  AlgEquiv.ofAlgHom (quotientForward a) (quotientBackward a)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := (rootLine (k := k) a).mkQ_surjective v
      change quotientForward a (quotientBackward a (SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v))) =
        SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v)
      rw [quotientBackward_ι_mk,quotientForward_mk,symQuotientMap_ι])
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change quotientBackward a (quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a)
        (SymmetricAlgebra.ι k V v))) = Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)
      rw [quotientForward_mk,symQuotientMap_ι,quotientBackward_ι_mk])


@[simp] theorem rootQuotientEquiv_mk_ι (a v : V) :
    rootQuotientEquiv a (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) := by
  exact symQuotientMap_ι a v

theorem reducedRoot_ne_zero (a v : V) (hv : v ∉ rootLine (k := k) a) :
    Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) ≠ 0 := by
  intro h
  apply hv
  apply (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp
  change (rootLine (k := k) a).mkQ v = 0
  apply symmetric_ι_injective (k := k)
  have hh := congrArg (rootQuotientEquiv a) h
  simpa only [rootQuotientEquiv_mk_ι,map_zero] using hh

variable {κ : Type*}
theorem linear_homogeneous [Fintype κ] (b : Basis κ k V) (v : V) :
    (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k V v)).IsHomogeneous 1 := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using (MvPolynomial.isHomogeneous_X k i).C_mul (b.repr v i)

/-- Polynomial coordinates on the actual symmetric-algebra quotient. -/
def rootQuotientPolynomial (a : V) (b : Basis κ k (V ⧸ rootLine (k := k) a)) :
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k] MvPolynomial κ k :=
  (rootQuotientEquiv a).trans (SymmetricAlgebra.equivMvPolynomial b)

theorem reducedRoot_homogeneous [Fintype κ] (a v : V)
    (b : Basis κ k (V ⧸ rootLine (k := k) a)) :
    (rootQuotientPolynomial a b
      (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v))).IsHomogeneous 1 := by
  change (SymmetricAlgebra.equivMvPolynomial b
    (rootQuotientEquiv a (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)))).IsHomogeneous 1
  rw [rootQuotientEquiv_mk_ι]
  exact linear_homogeneous b _

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem planeWeight_support_root (x : W) (a : PositiveRoot M cs)
    (P : Submodule ℝ (I → ℝ)) (hP : P ∈ (planeWeight x a).support) :
    ∃ b : PositiveRoot M cs, b ≠ a ∧ rootPlane a b = P := by
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  refine ⟨b,?_,hbP⟩
  have hb' := Finsupp.mem_support_iff.mp hb
  change halfVector x a b ≠ 0 at hb'
  simp only [halfVector,rootIndicator_apply] at hb'
  have hh : halfRoot x a b := by
    by_contra hn
    exact hb' (ite_eq_right hn)
  exact hh.1.1

def planeRoot (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : PositiveRoot M cs :=
  (planeWeight_support_root x a P.val P.property).choose

theorem planeRoot_ne (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : planeRoot x a P ≠ a :=
  (planeWeight_support_root x a P.val P.property).choose_spec.1

theorem planeRoot_plane (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : rootPlane a (planeRoot x a P) = P.val :=
  (planeWeight_support_root x a P.val P.property).choose_spec.2

theorem embed_not_rootLine (a b : PositiveRoot M cs) (hab : b ≠ a) :
    embed M b.val ∉ rootLine (k := ℝ) (embed M a.val) := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hli := (linearIndependent_fin2.mp (positiveRoots_independent b a hab)).2 c
  change c • a.val ≠ b.val at hli
  apply hli
  have hh := congrArg Prod.fst hc
  simpa only [embed,Prod.smul_fst] using hh

abbrev EdgeCoefficient (a : PositiveRoot M cs) :=
  SymmetricAlgebra ℝ (Extended M) ⧸ rootIdeal (k := ℝ) (embed M a.val)

def reducedPlaneRoot (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : EdgeCoefficient a :=
  Ideal.Quotient.mk (rootIdeal (k := ℝ) (embed M a.val))
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M (planeRoot x a P).val))

theorem reducedPlaneRoot_ne_zero (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : reducedPlaneRoot x a P ≠ 0 :=
  reducedRoot_ne_zero _ _ (embed_not_rootLine a _ (planeRoot_ne x a P))

/-- The manuscript's actual product of reduced root forms, with its proved
nonnegative integral plane exponents. No abstract invariant is substituted. -/
def edgeFactor (x : W) (a : PositiveRoot M cs) : EdgeCoefficient a :=
  ∏ P : (planeWeight x a).support, reducedPlaneRoot x a P ^ (planeWeight x a P.val).toNat

def edgeFactorDegree (x : W) (a : PositiveRoot M cs) : ℕ :=
  ∑ P : (planeWeight x a).support, (planeWeight x a P.val).toNat

def edgePolynomial (a : PositiveRoot M cs) : EdgeCoefficient a ≃ₐ[ℝ]
    MvPolynomial (Fin (Module.finrank ℝ (Extended M ⧸ rootLine (k := ℝ) (embed M a.val)))) ℝ :=
  rootQuotientPolynomial (embed M a.val) (Module.finBasis ℝ _)

theorem edgeFactor_nonzero (x : W) (a : PositiveRoot M cs) : edgeFactor x a ≠ 0 := by
  intro h
  have hp := congrArg (edgePolynomial a) h
  simp only [edgeFactor,map_prod,map_pow,map_zero] at hp
  apply (Finset.prod_ne_zero_iff.mpr ?_) hp
  intro P _
  apply pow_ne_zero
  intro h0
  apply reducedPlaneRoot_ne_zero x a P
  apply (edgePolynomial a).injective
  simpa only [map_zero] using h0

theorem edgeFactor_homogeneous (x : W) (a : PositiveRoot M cs) :
    (edgePolynomial a (edgeFactor x a)).IsHomogeneous (edgeFactorDegree x a) := by
  simp only [edgeFactor,map_prod,map_pow,edgeFactorDegree]
  apply MvPolynomial.IsHomogeneous.prod
  intro P _
  have h : (edgePolynomial a (reducedPlaneRoot x a P)).IsHomogeneous 1 :=
    reducedRoot_homogeneous _ _ _
  simpa only [one_mul] using h.pow (planeWeight x a P.val).toNat

theorem edgeFactor_totalDegree (x : W) (a : PositiveRoot M cs) :
    (edgePolynomial a (edgeFactor x a)).totalDegree = edgeFactorDegree x a :=
  (edgeFactor_homogeneous x a).totalDegree
    (by
      intro h0
      apply edgeFactor_nonzero x a
      apply (edgePolynomial a).injective
      simpa only [map_zero] using h0)


theorem edgeFactorDegree_cast (x : W) (a : PositiveRoot M cs) :
    (edgeFactorDegree x a : ℤ) = (planeWeight x a).sum (fun _ n => n) := by
  classical
  simp only [edgeFactorDegree,Nat.cast_sum]
  simp_rw [Int.toNat_of_nonneg (planeWeight_nonneg x a _)]
  exact Finset.sum_coe_sort (planeWeight x a).support (fun P => planeWeight x a P)


theorem edgeFactor_degree_formula (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a) :
    2 * ((edgePolynomial a (edgeFactor x a)).totalDegree : ℤ) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  rw [edgeFactor_totalDegree,edgeFactorDegree_cast]
  exact sum_planeWeight x a hx

end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem rootIdeal_eq_ker (a : V) : rootIdeal (k := k) a = RingHom.ker (symQuotientMap (k := k) a) := by
  apply le_antisymm (rootIdeal_le_ker a)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (rootQuotientEquiv (k := k) a).injective
  change quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = _
  rw [quotientForward_mk,map_zero]
  exact hz

theorem rootIdeal_isPrime (a : V) : (rootIdeal (k := k) a).IsPrime := by
  rw [rootIdeal_eq_ker]
  exact RingHom.ker_isPrime _

theorem symmetric_ι_prime (a : V) (ha : a ≠ 0) : Prime (SymmetricAlgebra.ι k V a) := by
  have hn : SymmetricAlgebra.ι k V a ≠ 0 := by
    intro h
    apply ha
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  exact (Ideal.span_singleton_prime hn).mp (rootIdeal_isPrime a)

theorem reducedRoot_prime (a v : V) (hv : v ∉ rootLine (k := k) a) :
    Prime (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) := by
  apply (MulEquiv.prime_iff (rootQuotientEquiv (k := k) a)).mp
  rw [rootQuotientEquiv_mk_ι]
  apply symmetric_ι_prime
  intro h
  exact hv ((Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp h)

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_dvd_iff (a v : V) :
    SymmetricAlgebra.ι k V a ∣ SymmetricAlgebra.ι k V v ↔ v ∈ rootLine (k := k) a := by
  rw [← Ideal.mem_span_singleton]
  change SymmetricAlgebra.ι k V v ∈ rootIdeal (k := k) a ↔ _
  rw [rootIdeal_eq_ker]
  change symQuotientMap a (SymmetricAlgebra.ι k V v) = 0 ↔ _
  rw [symQuotientMap_ι]
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp
    change (rootLine (k := k) a).mkQ v = 0
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  · intro h
    have h0 : (rootLine (k := k) a).mkQ v = 0 :=
      (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr h
    rw [h0,map_zero]

theorem mkQ_mem_span_iff (a b v : V) :
    (rootLine (k := k) a).mkQ v ∈
      Submodule.span k { (rootLine (k := k) a).mkQ b } ↔
      v ∈ Submodule.span k {a,b} := by
  have ha : (rootLine (k := k) a).mkQ a = 0 :=
    (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr
      (Submodule.subset_span (Set.mem_singleton _))
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    have h0 : (rootLine (k := k) a).mkQ (v-c • b) = 0 := by
      rw [map_sub,map_smul,← hc,sub_self]
    have hm := (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp h0
    obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp hm
    apply Submodule.mem_span_pair.mpr
    exact ⟨d,c,by rw [hd]; module⟩
  · intro h
    obtain ⟨d,c,hv⟩ := Submodule.mem_span_pair.mp h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    rw [← hv,map_add,map_smul,map_smul,ha,smul_zero,zero_add]

theorem reducedRoot_dvd_iff (a b v : V) :
    Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V b) ∣
      Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) ↔
        v ∈ Submodule.span k {a,b} := by
  let e := rootQuotientEquiv (k := k) a
  have hd (z w : SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) :
      z ∣ w ↔ e z ∣ e w := by
    constructor
    · exact map_dvd e
    · intro h
      simpa only [AlgEquiv.symm_apply_apply] using map_dvd e.symm h
  rw [hd]
  change rootQuotientEquiv a _ ∣ rootQuotientEquiv a _ ↔ _
  rw [rootQuotientEquiv_mk_ι,rootQuotientEquiv_mk_ι,symmetric_ι_dvd_iff]
  exact mkQ_mem_span_iff a b v

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem embed_mem_span_pair (a b c : I → ℝ) :
    embed M c ∈ Submodule.span ℝ {embed M a,embed M b} ↔
      c ∈ Submodule.span ℝ {a,b} := by
  constructor
  · intro h
    obtain ⟨r,s,h⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨r,s,?_⟩
    exact congrArg Prod.fst h
  · intro h
    obtain ⟨r,s,h⟩ := Submodule.mem_span_pair.mp h
    refine Submodule.mem_span_pair.mpr ⟨r,s,?_⟩
    apply Prod.ext
    · exact h
    · simp only [embed,Prod.snd_add,Prod.smul_snd,smul_zero,add_zero]

theorem reducedPlaneRoot_prime (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : Prime (reducedPlaneRoot x a P) :=
  reducedRoot_prime _ _ (embed_not_rootLine a _ (planeRoot_ne x a P))


theorem reducedPlaneRoot_dvd_iff (x : W) (a : PositiveRoot M cs)
    (P Q : (planeWeight x a).support) :
    reducedPlaneRoot x a P ∣ reducedPlaneRoot x a Q ↔ P = Q := by
  rw [reducedPlaneRoot,reducedPlaneRoot,reducedRoot_dvd_iff,embed_mem_span_pair]
  change (planeRoot x a Q).val ∈ rootPlane a (planeRoot x a P) ↔ P = Q
  have h := rootPlane_eq_iff a (planeRoot x a P) (planeRoot x a Q)
    (planeRoot_ne x a P).symm
  rw [planeRoot_plane,planeRoot_plane] at h
  rw [planeRoot_plane]
  constructor
  · intro hm
    apply Subtype.ext
    exact (h.mpr ⟨planeRoot_ne x a Q,hm⟩).symm
  · intro heq
    exact (h.mp (congrArg Subtype.val heq).symm).2

end
end KLInvariance.TitsSpace


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable (source target : E → V)

def IsPath (x y : V) : List E → Prop
  | [] => x = y
  | e :: p => source e = x ∧ IsPath (target e) y p

variable [Semiring R]
def pathTerm (T : R) (v : V → R) : List E → V → R
  | [], x => v x
  | e :: p, x => if source e = x then T * pathTerm T v p (target e) else 0

/-- One elementary matrix `1+T E_xy`, acting without choosing an enumeration
of the finite vertex set. -/
def step (T : R) (e : E) (v : V → R) : V → R :=
  fun x => v x + if source e = x then T * v (target e) else 0

/-- Edges are listed in decreasing schedule order, so the chronologically
last transfer is the outermost one. -/
def dispatch (T : R) (v : V → R) : List E → V → R
  | [] => v
  | e :: p => step source target T e (dispatch T v p)

/-- The full matrix expansion, each sublist contributing exactly one path
term. Noncomposable sublists contribute zero by the definition of pathTerm. -/
theorem dispatch_eq_path_sum (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ((p.sublists').map (fun q => pathTerm source target T v q x)).sum := by
  classical
  induction p generalizing x with
  | nil => simp [dispatch, List.sublists', pathTerm]
  | cons e p ih =>
    rw [dispatch,step,List.sublists'_cons,List.map_append,List.sum_append,List.map_map]
    rw [ih x]
    congr 1
    by_cases he : source e = x
    · simp only [Function.comp_def,pathTerm,he,ite_true]
      rw [List.sum_map_mul_left,ih (target e)]
    · simp [Function.comp_def,he,pathTerm]

/-- With a delta initial value, a path contributes its length weight, not an
invariant defined by the desired conclusion. -/
theorem pathTerm_delta (T : R) (x y : V) (p : List E) :
    pathTerm source target T (fun z => if z = y then 1 else 0) p x =
      if IsPath source target x y p then T ^ p.length else 0 := by
  classical
  induction p generalizing x with
  | nil => simp [pathTerm,IsPath]
  | cons e p ih =>
    simp only [pathTerm,IsPath,List.length_cons]
    by_cases he : source e = x
    · rw [ite_eq_left he,ih]
      by_cases hp : IsPath source target (target e) y p
      · simp only [hp,he,and_self,ite_true,pow_succ']
      · simp [hp,he]
    · simp [he]

/-- The entry of the elementary-matrix product is exactly the sum of weights
of directed schedule-subpaths. -/
theorem entry_eq_weighted_paths (T : R) (p : List E) (x y : V) :
    dispatch source target T (fun z => if z = y then 1 else 0) p x =
      ((p.sublists').map (fun q =>
        if IsPath source target x y q then T ^ q.length else 0)).sum := by
  classical
  rw [dispatch_eq_path_sum]
  congr 1
  exact List.map_congr_left (fun q _ => pathTerm_delta source target T x y q)


section LabelOrder
variable {Λ : Type*} [LinearOrder Λ] (label : E → Λ)

/-- Ties in a legitimate reflection schedule cannot occur on a composable
pair. Hence every nonzero term in the schedule expansion has strictly
rather than merely weakly decreasing labels. -/
theorem decreasing_of_schedule_path
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    {p : List E} {x y : V}
    (hp : IsPath source target x y p)
    (hs : p.Pairwise (fun e f => label f ≤ label e)) :
    p.Pairwise (fun e f => label f < label e) := by
  induction p generalizing x with
  | nil => exact List.Pairwise.nil
  | cons e p ih =>
    cases p with
    | nil => simp
    | cons f p =>
      have ht : IsPath source target (target e) y (f :: p) := hp.2
      have hef : label f < label e := by
        apply lt_of_le_of_ne ((List.pairwise_cons.mp hs).1 f (List.mem_cons_self))
        intro heq
        exact hties e f heq.symm ht.1.symm
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih ht hs.tail⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hef
      · exact lt_of_le_of_lt ((List.pairwise_cons.mp hs.tail).1 g hg) hef

/-- Every strictly decreasing edge list contained in a weakly decreasing
schedule occurs as a sublist. This also handles arbitrary ordering of ties:
a strict list can use at most one edge of each label. -/
theorem sublist_of_decreasing_subset {p schedule : List E}
    (hp : p.Pairwise (fun e f => label f < label e))
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hmem : p ⊆ schedule) : List.Sublist p schedule := by
  induction schedule generalizing p with
  | nil =>
    have : p = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun a ha => List.not_mem_nil (hmem ha))
    subst p
    exact List.Sublist.refl []
  | cons e schedule ih =>
    cases p with
    | nil => exact List.nil_sublist _
    | cons f p =>
      by_cases hef : e = f
      · subst f
        apply List.Sublist.cons_cons
        apply ih hp.tail hs.tail
        intro g hg
        rcases List.mem_cons.mp (hmem (List.mem_cons_of_mem e hg)) with heq | hin
        · have hlt := (List.pairwise_cons.mp hp).1 g hg
          rw [heq] at hlt
          exact (lt_irrefl _ hlt).elim
        · exact hin
      · apply List.Sublist.cons
        apply ih hp hs.tail
        intro g hg
        have hfg : f ∈ schedule := (List.mem_cons.mp (hmem (List.mem_cons_self))).resolve_left
          (Ne.symm hef)
        have hfe : label f ≤ label e := (List.pairwise_cons.mp hs).1 f hfg
        rcases List.mem_cons.mp (hmem hg) with heq | hin
        · subst g
          rcases List.mem_cons.mp hg with h | h
          · exact (hef h).elim
          · exact (not_lt_of_ge hfe ((List.pairwise_cons.mp hp).1 e h)).elim
        · exact hin

end LabelOrder

end
end KLInvariance.SchedulePaths

namespace KLInvariance.ReflectionPlane
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The product of three normalized reflections in a root plane is again
an actual orthogonal reflection. The plane itself need not be nondegenerate. -/
theorem reflection_triple_in_plane
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (a b c : V) (ha : B a a = 2) (hb : B b b = 2) (hc : B c c = 2)
    (hplane : c ∈ Submodule.span ℝ {a,b}) :
    ∃ d : V, ∃ hd : B d d = 2,
      Module.reflection ha * Module.reflection hb * Module.reflection hc =
        Module.reflection hd := by
  obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
  subst c
  let p := B a b
  let r := p*x+y
  let d := x • b - r • a
  have hba : B b a = p := hB.eq b a
  have hnorm : x^2+p*x*y+y^2=1 := by
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba] at hc
    dsimp [p]
    nlinarith [hc]
  have hd : B d d = 2 := by
    dsimp [d,r]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba]
    change x*(x*2-(p*x+y)*p)-(p*x+y)*(x*p-(p*x+y)*2)=2
    nlinarith [hnorm]
  refine ⟨d,hd,?_⟩
  apply LinearEquiv.ext
  intro v
  let A := B a v
  let C := B b v
  have h₁ : -A+p*C+(x-p*r)*(x*A+y*C)= r*(x*C-r*A) := by
    dsimp [r]
    linear_combination (A-p*C)*hnorm
  have h₂ : -C+r*(x*A+y*C)= -x*(x*C-r*A) := by
    dsimp [r]
    linear_combination C*hnorm
  calc
    (Module.reflection ha * Module.reflection hb * Module.reflection hc) v =
        v + (-A+p*C+(x-p*r)*(x*A+y*C)) • a +
          (-C+r*(x*A+y*C)) • b := by
      simp only [LinearEquiv.mul_apply,Module.reflection_apply,map_sub,map_smul,
        map_add,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,ha,hb,hba]
      dsimp [A,C,r,p]
      module
    _ = v + (r*(x*C-r*A)) • a + (-x*(x*C-r*A)) • b := by rw [h₁,h₂]
    _ = Module.reflection hd v := by
      simp only [Module.reflection_apply]
      dsimp [d]
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
      dsimp [A,C]
      module

end KLInvariance.ReflectionPlane

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- A product of three genuine Coxeter reflections in one root plane is a
Coxeter reflection, using the proved reflection faithfulness of the actual
Tits extension. This is the sufficiency direction of graph diamond closure. -/
theorem Represents.triple_isReflection {t s r : W} {a b c : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hc : Represents M cs r c)
    (hplane : c ∈ Submodule.span ℝ {a,b}) : cs.IsReflection (t*s*r) := by
  have hplane' : embed M c ∈ Submodule.span ℝ {embed M a,embed M b} := by
    obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
    apply Submodule.mem_span_pair.mpr
    refine ⟨x,y,?_⟩
    ext
    · exact congrFun hxy _
    · simp [embed]
  obtain ⟨d,hd,he⟩ := ReflectionPlane.reflection_triple_in_plane (extendedForm M)
    (extendedForm_spec M).1 (embed M a) (embed M b) (embed M c)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm) hplane'
  apply isReflection_of_moving_rank_one M cs
  have heq : extendedAction M cs (t*s*r) = Module.reflection hd := by
    rw [map_mul,map_mul,ha.extendedAction_eq,hb.extendedAction_eq,hc.extendedAction_eq]
    exact he
  rw [heq]
  exact Realization.finrank_reflection_sub_id _ _ hd

end
end KLInvariance.TitsSpace

/-! NEW GRAPH CLOSURE -/
namespace KLInvariance
universe u v
variable {I : Type u} [klPreservedInstance7 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

include klPreservedInstance7 in
 theorem BruhatStep.label_reflection {x y : W} (h : BruhatStep cs x y) :
    cs.IsReflection (y*x⁻¹) := by
  have _ := klPreservedInstance7
  obtain ⟨_,t,ht,rfl⟩ := h
  simpa [mul_assoc] using ht

 theorem BruhatStep.composable_labels_ne {x y z : W}
    (h : BruhatStep cs x y) (h' : BruhatStep cs y z) :
    y*x⁻¹ ≠ z*y⁻¹ := by
  intro he
  have hh : z*x⁻¹=1 := by
    calc
      z*x⁻¹ = (z*y⁻¹)*(y*x⁻¹) := by group
      _ = (y*x⁻¹)*(y*x⁻¹) := by rw [← he]
      _ = 1 := h.label_reflection.mul_self
  have hzx : z = x := by simpa using congrArg (fun w => w*x) hh
  have hlen := lt_trans h.1 h'.1
  simp [hzx] at hlen

namespace TitsSpace
open Module

 def graphRoot {x y : W} (h : BruhatStep cs x y) : PositiveRoot M cs :=
   positiveRoot M cs ⟨y*x⁻¹,h.label_reflection⟩

 theorem graphRoot_represents {x y : W} (h : BruhatStep cs x y) :
    Represents M cs (y*x⁻¹) (graphRoot h).val :=
  positiveRoot_represents M cs ⟨y*x⁻¹,h.label_reflection⟩

 theorem graphRoot_ne_of_same_source {x a b : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs x b) (hab : a ≠ b) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  have hl := (graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb)
  exact hab ((mul_right_cancel_iff).mp hl)

 theorem graphRoot_ne_of_path {x a z : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs a z) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  exact ha.composable_labels_ne hb ((graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb))

 theorem graphRoot_square_plane {x a b z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (haz : BruhatStep cs a z) (hbz : BruhatStep cs b z) (hab : a ≠ b) :
    rootPlane (graphRoot hxa) (graphRoot haz) =
      rootPlane (graphRoot hxa) (graphRoot hxb) := by
  have hp := (graphRoot_represents haz).plane_eq_of_product_eq
    (graphRoot_represents hxa) (graphRoot_represents hbz) (graphRoot_represents hxb)
    (Ne.symm (hxa.composable_labels_ne haz)) (Ne.symm (hxb.composable_labels_ne hbz))
    (by group : (z*a⁻¹)*(a*x⁻¹)=(z*b⁻¹)*(b*x⁻¹))
  have hp' := congrArg (Submodule.map
    (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))) hp
  have hp'' : rootPlane (graphRoot haz) (graphRoot hxa) =
      rootPlane (graphRoot hbz) (graphRoot hxb) := by
    simpa only [rootPlane,Submodule.map_span,Set.image_insert_eq,
      Set.image_singleton,LinearMap.fst_apply,embed] using hp'
  have hm : (graphRoot hxb).val ∈ rootPlane (graphRoot hxa) (graphRoot haz) := by
    rw [rootPlane,Set.pair_comm]
    change (graphRoot hxb).val ∈ rootPlane (graphRoot haz) (graphRoot hxa)
    rw [hp'']
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ((rootPlane_eq_iff (graphRoot hxa) (graphRoot haz) (graphRoot hxb)
    (graphRoot_ne_of_path hxa haz)).mpr
    ⟨Ne.symm (graphRoot_ne_of_same_source hxa hxb hab),hm⟩).symm

/-- Soundness of the eight-edge diamond closure rule for the genuine Bruhat
reflection graph. Vertex ranks need not be consecutive; the proof uses actual
root planes and reflection faithfulness, not a labeled graph isomorphism. -/
 theorem bruhatStep_diamond_closure {x a b c d z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (hac : BruhatStep cs a c) (had : BruhatStep cs a d)
    (hbc : BruhatStep cs b c) (hbd : BruhatStep cs b d)
    (hcz : BruhatStep cs c z) (hdz : BruhatStep cs d z)
    (hab : a ≠ b) (hcd : c ≠ d) : BruhatStep cs x z := by
  let P := rootPlane (graphRoot hxa) (graphRoot hxb)
  let Q := rootPlane (graphRoot hac) (graphRoot had)
  have hPc := graphRoot_square_plane hxa hxb hac hbc hab
  have hPd := graphRoot_square_plane hxa hxb had hbd hab
  have hacP : (graphRoot hac).val ∈ P := by
    change (graphRoot hac).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPc]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hadP : (graphRoot had).val ∈ P := by
    change (graphRoot had).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPd]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hQP : Q=P := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact hacP
      · have hv' := Set.mem_singleton_iff.mp hv
        rw [hv']
        exact hadP
    · dsimp [Q,P]
      rw [rootPlane_finrank _ _ (graphRoot_ne_of_same_source hac had hcd),
        rootPlane_finrank _ _ (graphRoot_ne_of_same_source hxa hxb hab)]
  have hQc := graphRoot_square_plane hac had hcz hdz hcd
  have hm : (graphRoot hxa).val ∈
      Submodule.span ℝ {(graphRoot hcz).val,(graphRoot hac).val} := by
    rw [Set.pair_comm]
    change (graphRoot hxa).val ∈ rootPlane (graphRoot hac) (graphRoot hcz)
    rw [hQc]
    change (graphRoot hxa).val ∈ Q
    rw [hQP]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have href := (graphRoot_represents hcz).triple_isReflection
    (graphRoot_represents hac) (graphRoot_represents hxa) hm
  have heq : (z*c⁻¹)*(c*a⁻¹)*(a*x⁻¹)=z*x⁻¹ := by group
  rw [heq] at href
  exact ⟨lt_trans hxa.1 (lt_trans hac.1 hcz.1), z*x⁻¹,href,by group⟩

end TitsSpace
end
end KLInvariance

namespace KLInvariance
universe u

/-- The entirely unlabelled closure used in graph reconstruction. Its
completeness for Bruhat graphs is a separate obligation; this definition
neither changes Bruhat order nor defines the R/KL polynomials. -/
inductive DiamondEdges {X : Type u} [PartialOrder X] : X → X → Prop
  | cover {x y : X} : x ⋖ y → DiamondEdges x y
  | diamond {x a b c d z : X} :
      DiamondEdges x a → DiamondEdges x b →
      DiamondEdges a c → DiamondEdges a d →
      DiamondEdges b c → DiamondEdges b d →
      DiamondEdges c z → DiamondEdges d z →
      a ≠ b → c ≠ d → DiamondEdges x z

 theorem DiamondEdges.map {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} (h : DiamondEdges x y) : DiamondEdges (e x) (e y) := by
  induction h with
  | cover h => exact DiamondEdges.cover ((apply_covBy_apply_iff e).mpr h)
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact DiamondEdges.diamond hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (e.injective he)) (fun he => hcd (e.injective he))

 theorem DiamondEdges.map_iff {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} : DiamondEdges (e x) (e y) ↔ DiamondEdges x y := by
  constructor
  · intro h
    simpa only [OrderIso.symm_apply_apply] using h.map e.symm
  · exact DiamondEdges.map e

 theorem bruhatStep_of_interval_covBy
    {I W : Type*} {M : CoxeterMatrix I} [Group W] (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (h : x ⋖ y) : BruhatStep cs x.val y.val := by
  rcases Relation.ReflTransGen.cases_head h.le with heq | ⟨z,hxz,hzy⟩
  · exact (h.ne (Subtype.ext heq)).elim
  · have hle : BruhatLE cs x.val z := Relation.ReflTransGen.single hxz
    let v : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 hle,
      bruhat_trans cs hzy y.property.2⟩
    have hv : v = x ∨ v = y := h.eq_or_eq hle hzy
    rcases hv with hv | hv
    · have heq : z = x.val := congrArg Subtype.val hv
      exact (lt_irrefl _ (heq ▸ hxz.1)).elim
    · have heq : z = y.val := congrArg Subtype.val hv
      exact heq ▸ hxz


 theorem diamondEdges_bruhatStep
    {I W : Type*} [Fintype I] {M : CoxeterMatrix I} [Group W]
    (cs : CoxeterSystem M W) {u b : W} {x y : Interval cs u b}
    (h : DiamondEdges x y) : BruhatStep cs x.val y.val := by
  induction h with
  | cover h => exact bruhatStep_of_interval_covBy cs h
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact TitsSpace.bruhatStep_diamond_closure hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (Subtype.ext he)) (fun he => hcd (Subtype.ext he))

end KLInvariance


namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem alt_add_two (i : Bool) (n : ℕ) :
    alt i (n+2) = i :: (!i) :: alt i n := by
  simp only [alt_succ,Bool.not_not]

theorem alt_odd_sandwich (i : Bool) (n : ℕ) :
    alt i (2*(n+1)+1) = i :: (alt (!i) (2*n+1) ++ [i]) := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    have h₁ : 2*(n+1+1)+1 = (2*(n+1)+1)+2 := by omega
    have h₂ : 2*(n+1)+1 = (2*n+1)+2 := by omega
    rw [h₁,alt_add_two,ih,h₂,alt_add_two]
    simp only [Bool.not_not,List.cons_append]

theorem odd_alt_reflection (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.IsReflection (cs.wordProd (alt i (2*n+1))) := by
  induction n generalizing i with
  | zero => simpa [alt] using cs.isReflection_simple i
  | succ n ih =>
    rw [alt_odd_sandwich,cs.wordProd_cons,cs.wordProd_append]
    obtain ⟨w,j,hw⟩ := ih (!i)
    refine ⟨cs.simple i*w,j,?_⟩
    simp only [cs.wordProd_cons,cs.wordProd_nil,mul_one,hw,mul_inv_rev,
      cs.inv_simple]
    group

theorem reflection_iff_odd (cs : CoxeterSystem M W) (w : W) :
    cs.IsReflection w ↔ Odd (cs.length w) := by
  constructor
  · exact fun h => h.odd_length
  · intro h
    obtain ⟨n,hn⟩ := h
    obtain ⟨i,hi⟩ := exists_alt cs w
    rw [hi,hn]
    convert odd_alt_reflection cs i n using 2

theorem step_iff_odd (cs : CoxeterSystem M W) (x y : W) :
    BruhatStep cs x y ↔ cs.length x < cs.length y ∧ Odd (cs.length y-cs.length x) := by
  have hm := cs.length_mul_mod_two y x⁻¹
  rw [cs.length_inv] at hm
  constructor
  · rintro ⟨hlen,t,ht,hprod⟩
    refine ⟨hlen,?_⟩
    have hteq : y*x⁻¹=t := by rw [hprod]; group
    have ho := ht.odd_length
    rw [← hteq,Nat.odd_iff] at ho
    rw [Nat.odd_iff]
    omega
  · rintro ⟨hlen,ho⟩
    refine ⟨hlen,y*x⁻¹,?_,by group⟩
    rw [reflection_iff_odd,Nat.odd_iff]
    rw [Nat.odd_iff] at ho
    omega

theorem two_elements_length (cs : CoxeterSystem M W) {n : ℕ} (hn : 0 < n)
    {w : W} (hw : n < cs.length w) :
    ∃ a b : W, a ≠ b ∧ ∀ z, cs.length z = n ↔ z = a ∨ z = b := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hi,length_alt]
  have hr₁ := reduced_alt_take cs hr (show n+1 ≤ cs.length w by omega)
  have hr₀ := reduced_alt_take cs hr (Nat.le_of_lt hw)
  have hr₂ : cs.IsReduced (alt (!i) n) := by simpa using hr₁.drop 1
  have hlen₀ : cs.length (cs.wordProd (alt i n)) = n := by simpa using hr₀.eq
  have hlen₂ : cs.length (cs.wordProd (alt (!i) n)) = n := by simpa using hr₂.eq
  refine ⟨cs.wordProd (alt i n),cs.wordProd (alt (!i) n),?_,?_⟩
  · intro heq
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hp : cs.wordProd (alt i (k+1+1)) = cs.wordProd (alt (!i) k) := by
      rw [alt_succ,cs.wordProd_cons,← heq,alt_succ,cs.wordProd_cons,
        cs.simple_mul_simple_cancel_left]
    have hlen := cs.length_wordProd_le (alt (!i) k)
    have hred := hr₁.eq
    rw [hp,length_alt] at hred
    rw [length_alt] at hlen
    omega
  · intro z
    constructor
    · intro hz
      obtain ⟨j,hj⟩ := exists_alt cs z
      rw [hz] at hj
      have hj' : j=i ∨ j=(!i) := by cases j <;> cases i <;> simp
      rcases hj' with rfl|rfl
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (rfl|rfl) <;> assumption

theorem two_step_rank_two (cs : CoxeterSystem M W) {x y : W}
    (hlen : cs.length y = cs.length x+2) :
    ∃ a b : W, a ≠ b ∧
      ∀ z, (BruhatStep cs x z ∧ BruhatStep cs z y) ↔ z=a ∨ z=b := by
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs (by omega : 0 < cs.length x+1)
    (w := y) (by omega)
  refine ⟨a,b,hab,?_⟩
  intro z
  rw [← hab',step_iff_odd,step_iff_odd]
  constructor
  · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
    omega
  · intro hz
    constructor <;> constructor
    · omega
    · rw [Nat.odd_iff]; omega
    · omega
    · rw [Nat.odd_iff]; omega

end KLInvariance.Dihedral

namespace KLInvariance
variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

theorem interval_covBy_of_length_succ (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : x ≤ y)
    (hlen : cs.length y.val = cs.length x.val+1) : x ⋖ y := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨lt_iff_le_and_ne.mpr ⟨hxy,?_⟩,?_⟩
  · intro heq
    have := congrArg (fun z : Interval cs u b => cs.length z.val) heq
    omega
  · intro z hxz hzy
    by_cases hz : z=x
    · exact Or.inl hz
    · right
      by_contra hzy'
      have h₁ := length_lt_of_bruhat_ne cs hxz (fun he => hz (Subtype.ext he.symm))
      have h₂ := length_lt_of_bruhat_ne cs hzy (fun he => hzy' (Subtype.ext he))
      omega

namespace Dihedral
variable {M₂ : CoxeterMatrix Bool}

theorem two_interval_elements_length (cs : CoxeterSystem M₂ W)
    {u b : W} (x y : Interval cs u b) {n : ℕ}
    (hn₁ : cs.length x.val < n) (hn₂ : n < cs.length y.val) :
    ∃ a c : Interval cs u b, a ≠ c ∧ cs.length a.val=n ∧ cs.length c.val=n := by
  obtain ⟨a,c,hac,hlevel⟩ := two_elements_length cs (by omega : 0<n) hn₂
  have ha := (hlevel a).mpr (Or.inl rfl)
  have hc := (hlevel c).mpr (Or.inr rfl)
  have hmem (z : W) (hz : cs.length z=n) :
      BruhatLE cs u z ∧ BruhatLE cs z b :=
    ⟨bruhat_trans cs x.property.1 (shorter_bruhat cs (by omega)),
      bruhat_trans cs (shorter_bruhat cs (by omega)) y.property.2⟩
  exact ⟨⟨a,hmem a ha⟩,⟨c,hmem c hc⟩,
    fun he => hac (congrArg Subtype.val he),ha,hc⟩

/-- Completeness of the actual unlabelled eight-edge closure for genuine
rank-two Coxeter systems. This is a necessary local case of Dyer's general
reconstruction, not a replacement main theorem. -/
theorem diamondEdges_of_bruhatStep (cs : CoxeterSystem M₂ W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      cs.length y.val-cs.length x.val=n → BruhatStep cs x.val y.val →
      DiamondEdges x y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hlen hxy
    have hodd := ((step_iff_odd cs x.val y.val).mp hxy).2
    rw [hlen,Nat.odd_iff] at hodd
    by_cases hn : n=1
    · apply DiamondEdges.cover
      exact interval_covBy_of_length_succ cs (Relation.ReflTransGen.single hxy) (by omega)
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨a,a₂,hab,ha,hb⟩ := two_interval_elements_length cs x y
        (n := cs.length x.val+1) (by omega) (by have := hxy.1; omega)
      obtain ⟨c,d,hcd,hc,hd⟩ := two_interval_elements_length cs x y
        (n := cs.length x.val+2) (by omega) (by have := hxy.1; omega)
      have hcover {p q : Interval cs u b}
          (hpq : cs.length q.val=cs.length p.val+1) : DiamondEdges p q :=
        DiamondEdges.cover (interval_covBy_of_length_succ cs
          (shorter_bruhat cs (by omega)) hpq)
      have htop {p : Interval cs u b} (hp : cs.length p.val=cs.length x.val+2) :
          DiamondEdges p y := by
        apply ih (cs.length y.val-cs.length p.val) (by have := hxy.1; omega) p y rfl
        rw [step_iff_odd]
        constructor
        · have := hxy.1; omega
        · rw [Nat.odd_iff]; have := hxy.1; omega
      exact DiamondEdges.diamond (hcover (by omega)) (hcover (by omega))
        (hcover (by omega)) (hcover (by omega)) (hcover (by omega)) (hcover (by omega))
        (htop hc) (htop hd) hab hcd

end Dihedral
end KLInvariance


end

end OAI
