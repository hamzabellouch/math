import Mathlib
import OAI.Analysis.BoundedHochschild.PartialIsometries

namespace OAI

/-! Matrix systems, expectations and rational projection approximation. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

private lemma projection_orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htp : t ≤ p-r) : r*t=0 := by
  have hh := (ht.le_iff_mul_eq_right ((hr.le_iff_sub hp).mp hrp)).mp htp
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

include e hτ htr hfaith in
lemma exists_partition_trace (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (n : ℕ) {p : M} (hp : IsStarProjection p) {t : ℝ} (ht : 0 ≤ t)
    (hpt : (τ p).re = (n : ℝ)*t) :
    ∃ q : Fin n → M, (∀ i, IsStarProjection (q i)) ∧
      (∀ i, q i ≤ p) ∧ (∀ i j, i ≠ j → q i*q j=0) ∧
      (∑ i, q i)=p ∧ ∀ i, (τ (q i)).re=t := by
  induction n generalizing p with
  | zero =>
    have htp : τ p=0 := by
      apply Complex.ext
      · simpa using hpt
      · exact (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2.symm
    have hp0 : p=0 := hfaith p (by simpa only [hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq] using htp)
    subst p
    exact ⟨Fin.elim0, by simp, by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    have hle : t ≤ (τ p).re := by
      rw [hpt, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) ht]
    obtain ⟨a,ha,hap,hat⟩ := HochschildDiffuse.exists_projection_of_trace τ e
      (HochschildSakai.mul_hasPreadjoint e) hτ htr hfaith hdiff hp t ht hle
    have hpa := (ha.le_iff_sub hp).mp hap
    have hpat : (τ (p-a)).re = (n : ℝ)*t := by
      rw [map_sub,Complex.sub_re,hpt,hat,Nat.cast_add,Nat.cast_one]
      ring
    obtain ⟨q,hq,hqp,hqo,hqs,hqt⟩ := ih hpa hpat
    refine ⟨Fin.cases a q,?_,?_,?_,?_,?_⟩
    · intro i
      exact Fin.cases ha hq i
    · intro i
      exact Fin.cases hap (fun j => (hqp j).trans (sub_le_self _ ha.nonneg)) i
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact projection_orthogonal_of_le_sub hp ha (hq j) hap (hqp j)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          have hh := projection_orthogonal_of_le_sub hp ha (hq i) hap (hqp i)
          simpa only [star_mul, (hq i).isSelfAdjoint.star_eq, ha.isSelfAdjoint.star_eq,
            star_zero,Fin.cases_zero,Fin.cases_succ] using congrArg star hh
        · intro hij
          exact hqo i j (fun he => hij (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero,Fin.cases_succ,hqs]
      abel
    · intro i
      exact Fin.cases hat hqt i

 
structure MatrixSystem (M : Type*) [Ring M] [StarRing M] (n : ℕ) where
  entry : Fin n → Fin n → M
  star_entry : ∀ i j, star (entry i j)=entry j i
  entry_mul : ∀ i j k l, entry i j*entry k l=if j=k then entry i l else 0
  sum_diagonal : ∑ i, entry i i=1

omit [PartialOrder M] [StarOrderedRing M] in
private lemma mul_of_initial_projection {v p : M} (hp : IsStarProjection p)
    (hv : star v*v=p) : v*p=v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  calc
    star (v*p-v)*(v*p-v) = p*(star v*v)*p-p*(star v*v)-(star v*v)*p+star v*v := by
      simp only [star_sub,star_mul,hp.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv,hp.isIdempotentElem.eq]; abel

include e hτ htr hfaith in
 

theorem exists_matrixSystem (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M) (n : ℕ) (hn : 0<n) :
    Nonempty (MatrixSystem M n) := by
  classical
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  obtain ⟨p,hp,_hpp,hpo,hps,hpt⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    n (IsStarProjection.one M) (inv_nonneg.mpr hn'.le)
      (by rw [h1,Complex.one_re,mul_inv_cancel₀ (ne_of_gt hn')])
  let i0 : Fin n := ⟨0,hn⟩
  have ht : ∀ i, τ (p i0)=τ (p i) := by
    intro i
    apply Complex.ext
    · rw [hpt,hpt]
    · exact (Complex.nonneg_iff.mp (τ.map_nonneg (hp i0).nonneg)).2.symm.trans
        (Complex.nonneg_iff.mp (τ.map_nonneg (hp i).nonneg)).2
  choose v hv0 hv using fun i => exists_partialIso_of_equal_trace e τ hτ htr hfaith
    h1 hfactor (hp i0) (hp i) (ht i)
  have hvi : ∀ i, v i*p i0=v i := fun i => mul_of_initial_projection (hp i0) (hv0 i)
  have hvf : ∀ i, p i*v i=v i := by
    intro i
    rw [← hv i,mul_assoc,hv0 i,hvi i]
  have hvs : ∀ i, star (v i)*p i=star (v i) := by
    intro i
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hvf i)
  have hcross : ∀ i j, i ≠ j → star (v i)*v j=0 := by
    intro i j hij
    calc
      star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hvs,hvf]
      _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
      _ = 0 := by rw [hpo i j hij,mul_zero,zero_mul]
  refine ⟨⟨fun i j => v i*star (v j),?_,?_,?_⟩⟩
  · intro i j
    simp only [star_mul,star_star]
  · intro i j k l
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      calc
        (v i*star (v j))*(v j*star (v l)) = v i*(star (v j)*v j)*star (v l) := by
          simp only [mul_assoc]
        _ = v i*star (v l) := by rw [hv0,hvi]
    · rw [ite_eq_right h]
      calc
        (v i*star (v j))*(v k*star (v l)) = v i*(star (v j)*v k)*star (v l) := by
          simp only [mul_assoc]
        _ = 0 := by rw [hcross j k h,mul_zero,zero_mul]
  · simpa only [hv] using hps

end HochschildMatrixSystems

 

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M]
variable {n : ℕ} (E : MatrixSystem M n)

 
def expectation : M →ₗ[ℂ] M where
  toFun x := (n : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j*x*E.entry j i
  map_add' x y := by simp only [mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp only [mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
    exact smul_comm _ _ _

lemma expectation_apply (x : M) : E.expectation x =
    (n : ℂ)⁻¹ • ∑ i, ∑ j, E.entry i j*x*E.entry j i := rfl

lemma expectation_star (x : M) : E.expectation (star x) = star (E.expectation x) := by
  simp [expectation_apply, star_smul, star_sum, star_mul, E.star_entry,mul_assoc]

lemma entry_mul_expectation (a b : Fin n) (x : M) :
    E.entry a b*E.expectation x =
      (n : ℂ)⁻¹ • ∑ j, E.entry a j*x*E.entry j b := by
  classical
  simp only [expectation_apply,mul_smul_comm,Finset.mul_sum,← mul_assoc,E.entry_mul]
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

lemma expectation_mul_entry (a b : Fin n) (x : M) :
    E.expectation x*E.entry a b =
      (n : ℂ)⁻¹ • ∑ j, E.entry a j*x*E.entry j b := by
  have hh := congrArg star (E.entry_mul_expectation b a (star x))
  simpa [star_mul,← E.expectation_star,E.star_entry,star_smul,star_sum,mul_assoc] using hh

lemma commute_expectation (x : M) (i j : Fin n) :
    Commute (E.expectation x) (E.entry i j) :=
  (E.expectation_mul_entry i j x).trans (E.entry_mul_expectation i j x).symm

lemma expectation_eq_self (hn : n ≠ 0) (x : M)
    (hx : ∀ i j, Commute x (E.entry i j)) : E.expectation x=x := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  calc
    E.expectation x = (n : ℂ)⁻¹ • ∑ i, ∑ j, x*(E.entry i j*E.entry j i) := by
      simp only [expectation_apply,← mul_assoc,← fun i j => (hx i j).eq]
    _ = (n : ℂ)⁻¹ • ((n : ℂ) • (x * ∑ i, E.entry i i)) := by
      simp only [E.entry_mul,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
      simp only [← Finset.mul_sum,nsmul_eq_mul,Nat.cast_smul_eq_nsmul]
    _ = x := by rw [E.sum_diagonal,mul_one,smul_smul,inv_mul_cancel₀ hnC,one_smul]

lemma expectation_idempotent (hn : n ≠ 0) (x : M) :
    E.expectation (E.expectation x)=E.expectation x :=
  E.expectation_eq_self hn _ (E.commute_expectation x)

variable [PartialOrder M]

lemma trace_expectation (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hn : n ≠ 0) (x : M) : τ (E.expectation x)=τ x := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hterm (i j : Fin n) : τ (E.entry i j*x*E.entry j i)=τ (x*E.entry j j) := by
    rw [htr,← mul_assoc,E.entry_mul,ite_eq_left rfl,htr]
  simp only [expectation_apply,map_smul,map_sum,hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← map_sum,← Finset.mul_sum,
    E.sum_diagonal,mul_one,smul_eq_mul]
  simp [← Nat.cast_smul_eq_nsmul ℂ n (τ x),smul_eq_mul,hnC]

lemma trace_adjoint (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (x y : M) : τ (E.expectation x*y)=τ (x*E.expectation y) := by
  classical
  have hterm (i j : Fin n) : τ ((E.entry i j*x*E.entry j i)*y)=
      τ (x*(E.entry j i*y*E.entry i j)) := by
    rw [mul_assoc,mul_assoc,htr]
    simp only [mul_assoc]
  simp only [expectation_apply,smul_mul_assoc,mul_smul_comm,map_smul,
    Finset.sum_mul,Finset.mul_sum,map_sum,hterm]
  rw [Finset.sum_comm]

lemma trace_residual_expectation (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    τ (star (x-E.expectation x)*E.expectation x)=0 := by
  rw [← E.trace_adjoint τ htr,E.expectation_star,map_sub,E.expectation_idempotent hn,
    sub_self,star_zero,zero_mul,map_zero]

variable [StarOrderedRing M]

lemma norm_sq (τ : M →ₚ[ℂ] ℂ) (x : M) :
    ‖τ.toPreGNS x‖^2=(τ (star x*x)).re := by
  have hh := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS x))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re] using hh

lemma expectation_pythagoras (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    ‖τ.toPreGNS x‖^2 = ‖τ.toPreGNS (E.expectation x)‖^2 +
      ‖τ.toPreGNS (x-E.expectation x)‖^2 := by
  have hh := E.trace_residual_expectation τ htr hn x
  have hh' : τ (star (E.expectation x)*(x-E.expectation x))=0 := by
    have hs := congrArg star hh
    rw [← map_star τ] at hs
    simpa only [star_mul,star_star,star_zero] using hs
  rw [norm_sq,norm_sq,norm_sq]
  have he : τ (star x*x)=τ (star (E.expectation x)*E.expectation x)+
      τ (star (x-E.expectation x)*(x-E.expectation x)) := by
    have hdecomp : star x*x=star (E.expectation x)*E.expectation x+
        star (x-E.expectation x)*(x-E.expectation x)+
        (star (x-E.expectation x)*E.expectation x+star (E.expectation x)*(x-E.expectation x)) := by
      simp only [star_sub]
      noncomm_ring
    simp only [hdecomp,map_add,hh,hh',add_zero]
  rw [he,Complex.add_re]

lemma expectation_gns_contract (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (x : M) :
    ‖τ.toPreGNS (E.expectation x)‖ ≤ ‖τ.toPreGNS x‖ := by
  have hh := E.expectation_pythagoras τ htr hn x
  nlinarith [sq_nonneg ‖τ.toPreGNS (x-E.expectation x)‖,
    norm_nonneg (τ.toPreGNS x),norm_nonneg (τ.toPreGNS (E.expectation x))]

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
open BoundedHochschild HochschildRigidity HochschildComparison
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma exists_matrixSystem_of_partition (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {n : ℕ} (hn : 0<n) (p : Fin n → M) (hp : ∀ i, IsStarProjection (p i))
    (hpo : ∀ i j, i ≠ j → p i*p j=0) (hps : ∑ i, p i=1)
    (ht : ∀ i j, τ (p i)=τ (p j)) :
    ∃ E : MatrixSystem M n, ∀ i, E.entry i i=p i := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  choose v hv0 hv using fun i => exists_partialIso_of_equal_trace e τ hτ htr hfaith
    h1 hfactor (hp i0) (hp i) (ht i0 i)
  have hvi : ∀ i, v i*p i0=v i := by
    intro i
    apply sub_eq_zero.mp
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    calc
      star (v i*p i0-v i)*(v i*p i0-v i) =
          p i0*(star (v i)*v i)*p i0-p i0*(star (v i)*v i)-
            (star (v i)*v i)*p i0+star (v i)*v i := by
              simp only [star_sub,star_mul,(hp i0).isSelfAdjoint.star_eq]
              noncomm_ring
      _ = 0 := by simp only [hv0,(hp i0).isIdempotentElem.eq,sub_self,zero_sub,neg_add_cancel]
  have hvf : ∀ i, p i*v i=v i := by
    intro i
    rw [← hv i,mul_assoc,hv0 i,hvi i]
  have hvs : ∀ i, star (v i)*p i=star (v i) := by
    intro i
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hvf i)
  have hcross : ∀ i j, i ≠ j → star (v i)*v j=0 := by
    intro i j hij
    calc
      star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hvs,hvf]
      _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
      _ = 0 := by rw [hpo i j hij,mul_zero,zero_mul]
  refine ⟨⟨fun i j => v i*star (v j),?_,?_,?_⟩,?_⟩
  · intro i j
    simp only [star_mul,star_star]
  · intro i j k l
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      calc
        (v i*star (v j))*(v j*star (v l)) = v i*(star (v j)*v j)*star (v l) := by
          simp only [mul_assoc]
        _ = v i*star (v l) := by rw [hv0,hvi]
    · rw [ite_eq_right h]
      calc
        (v i*star (v j))*(v k*star (v l)) = v i*(star (v j)*v k)*star (v l) := by
          simp only [mul_assoc]
        _ = 0 := by rw [hcross j k h,mul_zero,zero_mul]
  · simpa only [hv] using hps
  · exact hv

lemma projection_trace_real (p : M) (hp : IsStarProjection p) : τ p = ((τ p).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2.symm

include e hτ htr hfaith in
lemma exists_rational_subprojection (hdiff : HochschildDiffuse.NoMinimalProjections M)
    {p : M} (hp : IsStarProjection p) (n : ℕ) (hn : 0<n) (h1 : τ 1=1) :
    ∃ (k : ℕ) (q : M), k ≤ n ∧ IsStarProjection q ∧ q ≤ p ∧
      (τ q).re=(k : ℝ)/(n : ℝ) ∧
      ‖τ.toPreGNS (p-q)‖^2 < (n : ℝ)⁻¹ := by
  let t : ℝ := (τ p).re
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).1
  have ht1 : t ≤ 1 := by
    have hh := Complex.re_le_re (τ.monotone hp.le_one)
    change (τ p).re ≤ (τ 1).re at hh
    simpa only [h1,Complex.one_re] using hh
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  let k : ℕ := ⌊(n : ℝ)*t⌋₊
  have hklo : (k : ℝ) ≤ (n : ℝ)*t := Nat.floor_le (mul_nonneg hnR.le ht0)
  have hkhi : (n : ℝ)*t < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hkn : k ≤ n := by
    apply Nat.cast_le.mp (le_trans hklo _)
    exact mul_le_of_le_one_right hnR.le ht1
  have hkt : (k : ℝ)/(n : ℝ) ≤ t := (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hklo)
  obtain ⟨q,hq,hqp,hqt⟩ := HochschildDiffuse.exists_projection_of_trace τ e
    (HochschildSakai.mul_hasPreadjoint e) hτ htr hfaith hdiff hp
    ((k : ℝ)/(n : ℝ)) (div_nonneg (Nat.cast_nonneg k) hnR.le) hkt
  refine ⟨k,q,hkn,hq,hqp,hqt,?_⟩
  have hr := (hq.le_iff_sub hp).mp hqp
  rw [MatrixSystem.norm_sq,hr.isSelfAdjoint.star_eq,hr.isIdempotentElem.eq,
    map_sub,Complex.sub_re,hqt]
  change t-(k : ℝ)/(n : ℝ) < (n : ℝ)⁻¹
  apply (mul_lt_mul_iff_left₀ hnR).mp
  rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hnR),inv_mul_cancel₀ (ne_of_gt hnR)]
  linarith

include e hτ htr hfaith in
 

lemma exists_rational_partition (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (h1 : τ 1=1) {q : M} (hq : IsStarProjection q) {n k : ℕ} (hn : 0<n)
    (hkn : k ≤ n) (hqt : (τ q).re=(k : ℝ)/(n : ℝ)) :
    ∃ p : Fin (k+(n-k)) → M,
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i ≠ j → p i*p j=0) ∧
      (∑ i, p i)=1 ∧ (∀ i, (τ (p i)).re=(n : ℝ)⁻¹) ∧
      (∑ i : Fin k, p (Fin.castAdd (n-k) i))=q := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  obtain ⟨a,ha,haq,hao,has,hat⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    k hq (inv_nonneg.mpr hnR.le) (by simpa only [div_eq_mul_inv] using hqt)
  have hqc : IsStarProjection (1-q) := hq.one_sub
  have hqct : (τ (1-q)).re = ((n-k : ℕ) : ℝ)*(n : ℝ)⁻¹ := by
    rw [map_sub,h1,Complex.sub_re,Complex.one_re,hqt,Nat.cast_sub hkn]
    field_simp
  obtain ⟨b,hb,hbq,hbo,hbs,hbt⟩ := exists_partition_trace e τ hτ htr hfaith hdiff
    (n-k) hqc (inv_nonneg.mpr hnR.le) hqct
  let p : Fin (k+(n-k)) → M := Fin.addCases a b
  have hcross : ∀ i j, a i*b j=0 := by
    intro i j
    calc
      a i*b j = (a i*q)*((1-q)*b j) := by
        rw [(ha i).le_iff_mul_eq_left hq |>.mp (haq i),
          (hb j).le_iff_mul_eq_right hqc |>.mp (hbq j)]
      _ = 0 := by rw [mul_assoc,← mul_assoc q, mul_sub,mul_one,hq.isIdempotentElem.eq,
        sub_self,zero_mul,mul_zero]
  refine ⟨p,?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [p,Fin.addCases_left] using ha i
    · simpa only [p,Fin.addCases_right] using hb i
  · intro i j
    refine Fin.addCases ?_ ?_ i <;> intro i <;> refine Fin.addCases ?_ ?_ j <;> intro j hij
    · simpa only [p,Fin.addCases_left] using hao i j (fun h => hij (congrArg (Fin.castAdd (n-k)) h))
    · simpa only [p,Fin.addCases_left,Fin.addCases_right] using hcross i j
    · simpa only [p,Fin.addCases_left,Fin.addCases_right,star_mul,star_zero,(hb i).isSelfAdjoint.star_eq,
        (ha j).isSelfAdjoint.star_eq] using congrArg star (hcross j i)
    · simpa only [p,Fin.addCases_right] using hbo i j (fun h => hij (congrArg (Fin.natAdd k) h))
  · simp only [p,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right,has,hbs]
    abel
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [p,Fin.addCases_left] using hat i
    · simpa only [p,Fin.addCases_right] using hbt i
  · simpa only [p,Fin.addCases_left] using has

include e hτ htr hfaith in
 

theorem exists_matrix_projection_approx (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p : M} (hp : IsStarProjection p) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (E : MatrixSystem M n) (s : Finset (Fin n)), 0<n ∧
      IsStarProjection (∑ i ∈ s, E.entry i i) ∧ (∑ i ∈ s, E.entry i i) ≤ p ∧
      ‖τ.toPreGNS (p-∑ i ∈ s, E.entry i i)‖ < ε := by
  classical
  obtain ⟨n,hnR⟩ := exists_nat_gt ((ε^2)⁻¹)
  have hn : 0<n := by
    exact_mod_cast (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg ε)) hnR)
  have hnRpos : (0:ℝ)<n := by exact_mod_cast hn
  have hinv : (n:ℝ)⁻¹<ε^2 := (inv_lt_comm₀ hnRpos (sq_pos_of_pos hε)).mpr hnR
  obtain ⟨k,q,hkn,hq,hqp,hqt,herr⟩ := exists_rational_subprojection e τ hτ htr hfaith
    hdiff hp n hn h1
  obtain ⟨a,ha,hao,has,hat,haq⟩ := exists_rational_partition e τ hτ htr hfaith
    hdiff h1 hq hn hkn hqt
  have hn' : 0<k+(n-k) := by omega
  have ht : ∀ i j, τ (a i)=τ (a j) := by
    intro i j
    rw [projection_trace_real τ _ (ha i),projection_trace_real τ _ (ha j),hat,hat]
  obtain ⟨E,hE⟩ := exists_matrixSystem_of_partition e τ hτ htr hfaith h1 hfactor hn'
    a ha hao has ht
  let s : Finset (Fin (k+(n-k))) := Finset.univ.map (Fin.castAddEmb (n-k))
  have hs : (∑ i ∈ s, E.entry i i)=q := by
    simp only [s,Finset.sum_map,hE]
    exact haq
  refine ⟨k+(n-k),E,s,hn',hs ▸ hq,hs ▸ hqp,?_⟩
  rw [hs]
  have hh := herr.trans hinv
  nlinarith [norm_nonneg (τ.toPreGNS (p-q))]

end HochschildMatrixSystems
end

end OAI
