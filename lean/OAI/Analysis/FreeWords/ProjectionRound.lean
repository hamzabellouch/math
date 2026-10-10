import Mathlib
import OAI.Analysis.FreeWords.ProjectionSubdivision
import OAI.Analysis.FreeWords.RationalWeights
import OAI.Analysis.FreeWords.UnitaryExtension

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionRoundPartialOrder₁ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionRoundPreorder₁ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionRoundLE₁ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionRoundStarOrderedRing₁ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem partial_matrix_system_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (i₀ : ι) (hτ : ∀ i, τ.map (p i)=τ.map (p i₀)) :
    ∃ e : ι → ι → ConcreteAlgebra M,
      (∀ i j k l, e i j*e k l=if j=k then e i l else 0) ∧
      (∑ i, e i i)=1 ∧ (∀ i j, star (e i j)=e j i) ∧
      (∀ i, e i i=p i) := by
  choose v hv using fun i => projection_equivalent_of_trace M τ hF (p i₀) (p i)
    (hp i₀) (hp i) (hτ i).symm
  have hvpartial (i : ι) : Partial (v i) := partial_of_initial_projection (by rw [(hv i).1]; exact hp i₀)
  have hvp (i : ι) : v i*p i₀=v i := by rw [← (hv i).1,← mul_assoc]; exact hvpartial i
  have hpv (i : ι) : p i*v i=v i := by rw [← (hv i).2]; exact hvpartial i
  have hsvp (i : ι) : star (v i)*p i=star (v i) := by
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hpv i)
  have hprod (i j : ι) : star (v i)*v j=if i=j then p i₀ else 0 := by
    by_cases hij : i=j
    · subst j; simpa only [ite_true] using (hv i).1
    · rw [ite_eq_right hij]
      calc
        star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hsvp,hpv]
        _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
        _ = 0 := by rw [horth i j hij,mul_zero,zero_mul]
  let e (i j : ι) := v i*star (v j)
  refine ⟨e,?_,?_,?_,?_⟩
  · intro i j k l
    change (v i*star (v j))*(v k*star (v l))=if j=k then v i*star (v l) else 0
    calc
      (v i*star (v j))*(v k*star (v l)) = (v i*(star (v j)*v k))*star (v l) := by simp only [mul_assoc]
      _ = if j=k then v i*star (v l) else 0 := by rw [hprod]; split_ifs <;> simp only [hvp,mul_zero,zero_mul]
  · simpa only [e,funext (fun i => (hv i).2)] using h1
  · intro i j; simp only [e,star_mul,star_star]
  · intro i
    exact (hv i).2

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionRoundPartialOrder₂ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionRoundPreorder₂ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionRoundLE₂ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionRoundStarOrderedRing₂ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem subprojections_orthogonal {M : VonNeumannAlgebra H}
    {p q a b : ConcreteAlgebra M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (ha : IsStarProjection a) (hb : IsStarProjection b)
    (hap : a ≤ p) (hbq : b ≤ q) (hpq : p*q=0) : a*b=0 := by
  calc
    a*b = (a*p)*(q*b) := by rw [(ha.le_iff_mul_eq_left hp).mp hap,
      (hb.le_iff_mul_eq_right hq).mp hbq]
    _ = a*(p*q)*b := by simp only [mul_assoc]
    _ = 0 := by rw [hpq,mul_zero,zero_mul]

theorem orthogonal_sum_projection {ι A : Type*} [Fintype ι] [Ring A] [StarRing A]
    (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) : IsStarProjection (∑ i, p i) := by
  classical
  have hm (i j : ι) : p i*p j=if i=j then p i else 0 := by
    split_ifs with h
    · subst j; exact (hp i).isIdempotentElem.eq
    · exact ho i j h
  constructor
  · change (∑ i, p i)*(∑ i, p i)=∑ i, p i
    simp only [Finset.sum_mul,Finset.mul_sum,hm,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · change star (∑ i, p i)=∑ i, p i
    simp only [star_sum,fun i => (hp i).isSelfAdjoint.star_eq]

theorem round_projection_partition {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hD : IsDiffuse M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : 0 < n) (k : ι → ℕ) (r : ℕ)
      (q : ι → ConcreteAlgebra M) (s : ConcreteAlgebra M),
      (∑ i, k i)+r=n ∧
      (∀ i, IsStarProjection (q i)) ∧ (∀ i, q i ≤ p i) ∧
      (∀ i j, i≠j → q i*q j=0) ∧
      (∀ i, τ.map (q i)=(k i:ℂ)*(n:ℂ)⁻¹) ∧
      IsStarProjection s ∧ s=1-∑ i, q i ∧
      τ.map s=(r:ℂ)*(n:ℂ)⁻¹ ∧ (τ.map s).re < ε := by
  classical
  let w : ι → ℝ := fun i => (τ.map (p i)).re
  have hw (i : ι) : 0 ≤ w i := (Complex.nonneg_iff.mp (trace_projection_nonneg τ (hp i))).1
  have hw1 : ∑ i, w i=1 := by
    change (∑ i, (τ.map (p i)).re)=1
    rw [← Complex.re_sum,← map_sum,h1,τ.normalized,Complex.one_re]
  obtain ⟨n,hn,k,r,hkr,hkw,hr⟩ := round_probability_weights w hw hw1 ε hε
  have hnC : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  choose q hq hqp hτq using fun i => projection_with_trace M τ hD (p i) (hp i)
    ((k i:ℝ)/(n:ℝ)) (div_nonneg (Nat.cast_nonneg _) hnR.le) (hkw i)
  have hqle (i : ι) : q i ≤ p i := ((hq i).le_iff_mul_eq_left (hp i)).mpr (hqp i)
  have hqo (i j : ι) (hij : i≠j) : q i*q j=0 :=
    subprojections_orthogonal (hp i) (hp j) (hq i) (hq j) (hqle i) (hqle j) (ho i j hij)
  have hsum := orthogonal_sum_projection q hq hqo
  have hle : (∑ i, q i) ≤ (1 : ConcreteAlgebra M) := by
    rw [← h1]
    exact Finset.sum_le_sum (fun i _ => hqle i)
  let s : ConcreteAlgebra M := 1-∑ i, q i
  have hs : IsStarProjection s := (hsum.le_iff_sub (IsStarProjection.one _)).mp hle
  have hτq' (i : ι) : τ.map (q i)=(k i:ℂ)*(n:ℂ)⁻¹ := by
    rw [hτq i,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_natCast,div_eq_mul_inv]
  have hτs : τ.map s=(r:ℂ)*(n:ℂ)⁻¹ := by
    dsimp only [s]
    rw [map_sub,τ.normalized,map_sum]
    simp only [hτq',← Finset.sum_mul,← Nat.cast_sum]
    have hkrC : ((∑ i, k i):ℂ)+(r:ℂ)=(n:ℂ) := by exact_mod_cast hkr
    push_cast
    field_simp
    linear_combination -hkrC
  refine ⟨n,hn,k,r,q,s,hkr,hq,hqle,hqo,hτq',hs,rfl,hτs,?_⟩
  rw [hτs]
  have he : ((r:ℂ)*(n:ℂ)⁻¹).re=(r:ℝ)/(n:ℝ) := by
    rw [← div_eq_mul_inv,← Complex.ofReal_natCast r,← Complex.ofReal_natCast n,
      ← Complex.ofReal_div,Complex.ofReal_re]
  rw [he]
  exact hr

end

end KKProjectionSupport

namespace KKTraceTransfer

open KKUltraTrace KKProjectionSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance projectionRoundPartialOrder₃ (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance projectionRoundPreorder₃ (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance projectionRoundLE₃ (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance projectionRoundStarOrderedRing₃ (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem traceNorm_eq_gns {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (a : ConcreteAlgebra M) : traceNorm τ a=‖gnsVector (tracePositive τ) a‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ,gnsVector_inner]
  rfl

theorem traceNorm_nonneg {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (a : ConcreteAlgebra M) : 0 ≤ traceNorm τ a := Real.sqrt_nonneg _

theorem traceNorm_add_le {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (a b : ConcreteAlgebra M) : traceNorm τ (a+b) ≤ traceNorm τ a+traceNorm τ b := by
  simp only [traceNorm_eq_gns,map_add]
  exact norm_add_le _ _

theorem traceNorm_mul_le {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (a b : ConcreteAlgebra M) : traceNorm τ (a*b) ≤ ‖a‖*traceNorm τ b := by
  simp only [traceNorm_eq_gns]
  rw [← gnsStarAlgHom_vector]
  exact (((tracePositive τ).gnsStarAlgHom a).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _))

theorem traceNorm_one {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) :
    traceNorm τ 1=1 := by
  simp only [traceNorm,star_one,mul_one,τ.normalized,Complex.one_re,Real.sqrt_one]

theorem traceNorm_le_norm {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (a : ConcreteAlgebra M) : traceNorm τ a ≤ ‖a‖ := by
  simpa only [mul_one,traceNorm_one] using traceNorm_mul_le τ a 1

theorem traceNorm_projection_sq {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    {p : ConcreteAlgebra M} (hp : IsStarProjection p) : (traceNorm τ p)^2=(τ.map p).re := by
  have h := congrArg Complex.re (traceNorm_sq τ p)
  simpa only [Complex.ofReal_re,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using h

end

end KKTraceTransfer
end

end OAI
