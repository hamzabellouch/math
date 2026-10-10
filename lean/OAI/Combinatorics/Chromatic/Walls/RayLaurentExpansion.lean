import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallUnits

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
open scoped LaurentSeries RatFunc
noncomputable section
namespace LaurentRay
local instance : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ

lemma reciprocal_transcendental : Transcendental ℚ ((RatFunc.X : RatFunc ℚ)⁻¹) := by
  intro h
  exact (RatFunc.transcendental_X (K:=ℚ)) (IsAlgebraic.inv_iff.mp h)

def reciprocalEval : Polynomial ℚ →ₐ[ℚ] RatFunc ℚ :=
  Polynomial.aeval ((RatFunc.X : RatFunc ℚ)⁻¹)
lemma reciprocalEval_injective : Function.Injective reciprocalEval :=
  transcendental_iff_injective.mp reciprocal_transcendental
lemma reciprocalEval_regular :
    (nonZeroDivisors (Polynomial ℚ)) ≤ (nonZeroDivisors (RatFunc ℚ)).comap reciprocalEval :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ reciprocalEval_injective

def reciprocal : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom reciprocalEval.toRingHom reciprocalEval_regular
lemma reciprocal_X : reciprocal RatFunc.X=(RatFunc.X : RatFunc ℚ)⁻¹ := by
  have hh:=RatFunc.liftRingHom_apply_div reciprocalEval.toRingHom reciprocalEval_regular Polynomial.X 1
  change reciprocal (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X /
    algebraMap (Polynomial ℚ) (RatFunc ℚ) 1)=reciprocalEval Polynomial.X/reciprocalEval 1 at hh
  simpa [reciprocalEval] using hh

def atInfinity : RatFunc ℚ →+* LaurentSeries ℚ :=
  (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp reciprocal

lemma atInfinity_injective : Function.Injective atInfinity := atInfinity.injective

lemma atInfinity_v : atInfinity RationalRay.v=HahnSeries.single (-1 : ℤ) (1:ℚ) := by
  change algebraMap (RatFunc ℚ) (LaurentSeries ℚ) (reciprocal RatFunc.X)=_
  rw [reciprocal_X,map_inv₀]
  change ((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ)⁻¹=_
  rw [RatFunc.coe_X,HahnSeries.inv_single]
  simp only [inv_one]

lemma atInfinity_v_pow (k : ℤ) :
    atInfinity (RationalRay.v^k)=HahnSeries.single (-k) (1:ℚ) := by
  rw [map_zpow₀,atInfinity_v, RatFunc.single_zpow (-1),←zpow_mul,neg_one_mul]
  exact (RatFunc.single_zpow (-k)).symm

lemma atInfinity_q : atInfinity RationalRay.q=HahnSeries.single (2:ℤ) (1:ℚ) := by
  exact atInfinity_v_pow (-2)

lemma map_elementaryCoeff {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (q u : K) (n : ℕ) : φ (elementaryCoeff q u n)=elementaryCoeff (φ q) (φ u) n := by
  induction n with
  | zero => exact map_one φ
  | succ n ih => simp only [elementaryCoeff,map_mul,map_div₀,map_sub,map_one,map_pow,ih]

lemma map_elementary {K L : Type*} [Field K] [Field L] (φ : K →+* L) (q u : K) :
    PowerSeries.map φ (elementary q u)=elementary (φ q) (φ u) := by
  ext n
  rw [coeff_map,coeff_elementary,coeff_elementary,map_elementaryCoeff]

lemma elementary_atInfinity (k : ℤ) :
    PowerSeries.map atInfinity (elementary RationalRay.q (RationalRay.v^k))=
      elementary (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (-k) (1:ℚ)) := by
  rw [map_elementary]
  change elementary (atInfinity RationalRay.q) (atInfinity (RationalRay.v^k))=_
  rw [atInfinity_q,atInfinity_v_pow]
lemma map_complete {K L : Type*} [Field K] [Field L] (φ : K →+* L) (q u : K) :
    PowerSeries.map φ (complete q u)=complete (φ q) (φ u) := by
  unfold complete
  have hm : PowerSeries.map φ (elementary q (-u))=elementary (φ q) (-φ u) := by
    rw [map_elementary,map_neg]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [constant_elementary]; exact one_ne_zero)).mpr
  rw [←hm,←map_mul,PowerSeries.inv_mul_cancel _ (by rw [constant_elementary]; exact one_ne_zero),map_one]

lemma complete_atInfinity (k : ℤ) :
    PowerSeries.map atInfinity (complete RationalRay.q (RationalRay.v^k))=
      complete (HahnSeries.single (2:ℤ) (1:ℚ)) (HahnSeries.single (-k) (1:ℚ)) := by
  rw [map_complete,atInfinity_q,atInfinity_v_pow]

lemma atInfinity_eval_monomial (a : ℕ) (k : ℤ) :
    atInfinity (PositiveRay.eval (LaurentPolynomial.C a * LaurentPolynomial.T k))=
      HahnSeries.single (-k) (a:ℚ) := by
  rw [map_mul,PositiveRay.eval_T,map_mul,atInfinity_v_pow]
  have hc : PositiveRay.eval (LaurentPolynomial.C a)=(a:RatFunc ℚ) := by
    simp [PositiveRay.eval]
  rw [hc,map_natCast,←HahnSeries.single_zero_natCast,HahnSeries.single_mul_single,
    zero_add,mul_one]

lemma atInfinity_eval_coeff (p : LaurentPolynomial ℕ) (j : ℤ) :
    (atInfinity (PositiveRay.eval p)).coeff j=(p.coeff (-j):ℚ) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,HahnSeries.coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
      Nat.cast_add,hp,hq]
  | C_mul_T k a =>
    rw [atInfinity_eval_monomial,HahnSeries.coeff_single,←LaurentPolynomial.single_eq_C_mul_T]
    simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
    by_cases h : j= -k
    · subst j; simp
    · have h' : k≠ -j := by omega
      simp [h,h']

lemma positive_coeff_atInfinity {F : PowerSeries (RatFunc ℚ)} (hF : PositiveRay.Positive F)
    (n : ℕ) (j : ℤ) : ∃a : ℕ,(atInfinity (coeff n F)).coeff j=(a:ℚ) := by
  obtain ⟨A,rfl⟩:=hF
  rw [coeff_map,atInfinity_eval_coeff]
  exact ⟨(coeff n A).coeff (-j),rfl⟩

end LaurentRay
end
end ElementaryPositivity.WallUnits
end
end
section
section
namespace ElementaryPositivity.FiniteFunctionValues
noncomputable section
variable {α β : Type*} [Fintype α]
def values (f : α → β) : Multiset β := Finset.univ.val.map f

lemma count_values [DecidableEq β] (f : α → β) (b : β) :
    (values f).count b=Fintype.card {x : α // f x=b} := by
  classical
  simp only [values,Multiset.count_map,Fintype.card_subtype,Finset.filter_val,Finset.card,eq_comm]

lemma values_comp (e : Equiv.Perm α) (f : α → β) : values (f ∘ e)=values f := by
  rw [values,←Multiset.map_map,Multiset.map_univ_val_equiv]
  rfl

lemma values_eq_iff [DecidableEq β] (f g : α → β) :
    values f=values g ↔ ∃e : Equiv.Perm α,∀x,g (e x)=f x := by
  classical
  constructor
  · intro h
    have hc (b : β) : Fintype.card {x : α // f x=b}=Fintype.card {x : α // g x=b} := by
      rw [←count_values,←count_values,h]
    let ee (b : β) : {x : α // f x=b} ≃ {x : α // g x=b}:=Fintype.equivOfCardEq (hc b)
    exact ⟨Equiv.ofFiberEquiv ee,Equiv.ofFiberEquiv_map ee⟩
  · rintro ⟨e,he⟩
    have hf : f=g ∘ e := funext (fun x=>(he x).symm)
    rw [hf,values_comp]

lemma values_fin {n : ℕ} (f : Fin n → β) : values f=(List.ofFn f:Multiset β) := by
  rw [values,Finset.val_univ_fin,List.ofFn_eq_map]
  rfl

lemma values_card (f : α → β) : (values f).card=Fintype.card α := by
  simp [values]

lemma values_fin_surjective {n : ℕ} (s : Sym β n) : ∃f : Fin n → β,values f=s.val := by
  classical
  obtain ⟨l,hl⟩:=Quotient.exists_rep s.val
  have hl' : (l:Multiset β)=s.val:=hl
  have hn : l.length=n := by simpa only [←Multiset.coe_card,hl'] using s.property
  subst n
  refine ⟨l.get,?_⟩
  rw [values_fin,List.ofFn_get]
  exact hl'
end
end ElementaryPositivity.FiniteFunctionValues
end
end

end OAI
