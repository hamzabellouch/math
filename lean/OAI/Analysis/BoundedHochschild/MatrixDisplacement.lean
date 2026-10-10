import Mathlib
import OAI.Analysis.BoundedHochschild.MatrixSystems
import OAI.Analysis.BoundedHochschild.MatrixCommutants

namespace OAI

/-! Projection displacement and energy-decreasing matrix extensions. -/

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
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
lemma positive_contraction_bound_of_projections
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (F : M →ₗ[ℂ] V) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ a : M, ‖F a‖ ≤ B*‖a‖)
    (hproj : ∀ p : M, IsStarProjection p → ‖F p‖ ≤ K)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ‖F a‖ ≤ K := by
  have hb : ∀ n : ℕ, ∀ a : M, 0 ≤ a → a ≤ 1 →
      ‖F a‖ ≤ K+(1/2:ℝ)^n*B := by
    intro n
    induction n with
    | zero =>
        intro a ha0 ha1
        have hn : ‖a‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ ha0).mpr ha1
        have hh := (hbound a).trans (mul_le_of_le_one_right hB hn)
        simpa only [pow_zero,one_mul] using hh.trans (le_add_of_nonneg_left hK)
    | succ n ih =>
        intro a ha0 ha1
        obtain ⟨p,hp,h0,h1⟩ := exists_dyadic_projection e a ha0 ha1
        have hh := ih ((2:ℝ) • a-p) h0 h1
        have he : (2:ℝ) • F a=F ((2:ℝ) • a-p)+F p := by
          simp only [map_sub,← Complex.coe_smul,map_smul,sub_add_cancel]
        have ht := norm_add_le (F ((2:ℝ) • a-p)) (F p)
        rw [← he,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
        rw [pow_succ]
        nlinarith [hproj p hp]
  have ht : Tendsto (fun n : ℕ => K+(1/2:ℝ)^n*B) atTop (𝓝 K) := by
    convert tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
         (by norm_num : (1/2:ℝ)<1)).mul_const B) using 1
    simp
  exact ge_of_tendsto ht (Eventually.of_forall fun n => hb n a ha0 ha1)

include e in
lemma contraction_bound_of_projections
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (F : M →ₗ[ℂ] V) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbound : ∀ a : M, ‖F a‖ ≤ B*‖a‖)
    (hproj : ∀ p : M, IsStarProjection p → ‖F p‖ ≤ K)
    (a : M) (ha : ‖a‖ ≤ 1) : ‖F a‖ ≤ 4*K := by
  obtain ⟨x,hx0,hxn,he⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hb (i : Fin 4) : ‖F (x i)‖ ≤ K :=
    positive_contraction_bound_of_projections e F B K hB hK hbound hproj (x i)
      (hx0 i) ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (hx0 i)).mp ((hxn i).trans ha))
  rw [he,map_sum]
  calc
    ‖∑ i : Fin 4, F (Complex.I^(i:ℕ) • x i)‖ ≤
        ∑ i : Fin 4, ‖F (Complex.I^(i:ℕ) • x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, K := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [map_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul] using hb i
    _ = 4*K := by simp

variable (τ : M →ₚ[ℂ] ℂ)

def commutatorGNS (a : M) : M →ₗ[ℂ] τ.PreGNS :=
  τ.toPreGNS.toLinearMap.comp
    (((ContinuousLinearMap.mul ℂ M).flip a - ContinuousLinearMap.mul ℂ M a).toLinearMap)

omit [StarOrderedRing M] in
lemma commutatorGNS_apply (a x : M) : commutatorGNS τ a x=τ.toPreGNS (x*a-a*x) := rfl

lemma commutatorGNS_bound (h1 : τ 1=1) (a x : M) :
    ‖commutatorGNS τ a x‖ ≤ (2*‖a‖)*‖x‖ := by
  change ‖τ.toPreGNS (x*a-a*x)‖ ≤ _
  calc
    _ ≤ ‖x*a-a*x‖ := preGNS_norm_le τ h1 _
    _ ≤ ‖x*a‖+‖a*x‖ := norm_sub_le _ _
    _ ≤ ‖x‖*‖a‖+‖a‖*‖x‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

include e in
lemma norm_sub_trace_le_of_projection_commutators
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (a : M) (K : ℝ) (hK : 0 ≤ K)
    (hp : ∀ p : M, IsStarProjection p → ‖τ.toPreGNS (p*a-a*p)‖ ≤ K) :
    ‖τ.toPreGNS (a-(τ a) • (1:M))‖ ≤ 4*K := by
  apply HochschildDixmier.norm_sub_trace_le_of_conjugations e τ (mul_hasPreadjoint e)
    hτ h1 htr hfaith hfactor a (4*K)
  intro u
  have : Nontrivial M := ⟨⟨1,0,by
    intro hz
    have hh : (1:ℂ)=0 := h1.symm.trans ((congrArg τ hz).trans (map_zero τ))
    exact one_ne_zero hh⟩⟩
  have hnu : ‖(u:M)‖ ≤ 1 := (CStarRing.norm_coe_unitary u).le
  have hh := contraction_bound_of_projections e (commutatorGNS τ a) (2*‖a‖) K
    (by positivity) hK (commutatorGNS_bound τ h1 a) hp (u:M) hnu
  have he : HochschildDixmier.conjugate u a-a=((u:M)*a-a*(u:M))*star (u:M) := by
    simp only [HochschildDixmier.conjugate_apply,sub_mul,mul_assoc,Unitary.mul_star_self_of_mem u.prop,
      mul_one]
  rw [he,show star (u:M)=((star u:unitary M):M) from rfl,
    preGNS_norm_unitary_right τ htr]
  exact hh

include e in
 

theorem exists_projection_displacement
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (a : M) (ha : 0<‖τ.toPreGNS (a-(τ a) • (1:M))‖) :
    ∃ p : M, IsStarProjection p ∧
      ‖τ.toPreGNS (a-(τ a) • (1:M))‖/8 < ‖τ.toPreGNS (p*a-a*p)‖ := by
  by_contra hn
  push Not at hn
  have hh := norm_sub_trace_le_of_projection_commutators e τ hτ h1 htr hfaith hfactor a
    (‖τ.toPreGNS (a-(τ a) • (1:M))‖/8) (by positivity) hn
  linarith

end HochschildQuantization

 

 

open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n m : ℕ} (E : MatrixSystem M n) (F : MatrixSystem E.commutant m)

omit [PartialOrder M] [StarOrderedRing M] in
lemma coe_entry_star (c d : Fin m) : star (F.entry c d : M) = (F.entry d c : M) := by
  change ((star (F.entry c d) : E.commutant) : M) = _
  rw [F.star_entry]

omit [PartialOrder M] [StarOrderedRing M] in
lemma coe_entry_mul (a b c d : Fin m) :
    (F.entry a b : M)*(F.entry c d : M) = if b=c then (F.entry a d : M) else 0 := by
  change ((F.entry a b * F.entry c d : E.commutant) : M) = _
  rw [F.entry_mul]
  split <;> rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma coe_sum_diagonal : ∑ c : Fin m, (F.entry c c : M) = 1 := by
  have h := congrArg (fun z : E.commutant => (z : M)) F.sum_diagonal
  simpa only [← E.commutant.subtype_apply, map_sum, map_one] using h

 

def extend : MatrixSystem M (n*m) where
  entry i j := E.entry (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
    (F.entry (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 : M)
  star_entry i j := by
    simp only [star_mul,E.star_entry,E.coe_entry_star F]
    exact ((F.entry _ _).property _ _).eq
  entry_mul i j k l := by
    classical
    have hterm (a b c d : Fin n × Fin m) :
        (E.entry a.1 b.1*(F.entry a.2 b.2 : M))*(E.entry c.1 d.1*(F.entry c.2 d.2 : M))=
        if b=c then E.entry a.1 d.1*(F.entry a.2 d.2 : M) else 0 := by
      calc
        _ = (E.entry a.1 b.1*E.entry c.1 d.1)*((F.entry a.2 b.2 : M)*(F.entry c.2 d.2 : M)) := by
          rw [mul_assoc,← mul_assoc (F.entry a.2 b.2 : M),((F.entry a.2 b.2).property c.1 d.1).eq]
          noncomm_ring
        _ = _ := by
          rw [E.entry_mul,E.coe_entry_mul F]
          by_cases h1 : b.1=c.1 <;> by_cases h2 : b.2=c.2 <;>
            simp [h1,h2,Prod.ext_iff]
    convert hterm (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)
      (finProdFinEquiv.symm k) (finProdFinEquiv.symm l) using 1
    simp only [Equiv.apply_eq_iff_eq]
  sum_diagonal := by
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,E.coe_sum_diagonal F,mul_one]
    exact E.sum_diagonal

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_entry (a b : Fin n) (c d : Fin m) :
    (E.extend F).entry (finProdFinEquiv (a,c)) (finProdFinEquiv (b,d))=
      E.entry a b*(F.entry c d : M) := by simp only [extend,Equiv.symm_apply_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma entry_sum_extension (a b : Fin n) :
    ∑ c : Fin m, (E.extend F).entry (finProdFinEquiv (a,c)) (finProdFinEquiv (b,c))=E.entry a b := by
  simp only [E.extend_entry,← Finset.mul_sum,E.coe_sum_diagonal F,mul_one]

omit [PartialOrder M] [StarOrderedRing M] in
lemma commutant_entry_sum_extension (c d : Fin m) :
    ∑ a : Fin n, (E.extend F).entry (finProdFinEquiv (a,c)) (finProdFinEquiv (a,d))=(F.entry c d : M) := by
  simp only [E.extend_entry,← Finset.sum_mul,E.sum_diagonal,one_mul]

 
omit [PartialOrder M] [StarOrderedRing M] in
lemma extension_expectation_commutes (x : M) :
    (∀ a b, Commute ((E.extend F).expectation x) (E.entry a b)) ∧
    (∀ c d, Commute ((E.extend F).expectation x) (F.entry c d : M)) := by
  constructor
  · intro a b
    rw [← E.entry_sum_extension F a b]
    apply Commute.sum_right
    intro c hc
    exact (E.extend F).commute_expectation x _ _
  · intro c d
    rw [← E.commutant_entry_sum_extension F c d]
    apply Commute.sum_right
    intro a ha
    exact (E.extend F).commute_expectation x _ _

omit [StarOrderedRing M] in
lemma extension_residual_orthogonal (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (hm : m ≠ 0) (x : M) :
    τ (star (E.expectation x-(E.extend F).expectation x)*(E.extend F).expectation x)=0 := by
  have ht := (E.extend F).trace_residual_expectation τ htr (Nat.mul_ne_zero hn hm) x
  rw [star_sub,sub_mul,map_sub] at ht ⊢
  rw [← E.expectation_star,E.trace_adjoint τ htr,
    E.expectation_eq_self hn _ (E.extension_expectation_commutes F x).1]
  exact ht

lemma extension_pythagoras (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (hm : m ≠ 0) (x : M) :
    ‖τ.toPreGNS (E.expectation x)‖^2 = ‖τ.toPreGNS ((E.extend F).expectation x)‖^2 +
      ‖τ.toPreGNS (E.expectation x-(E.extend F).expectation x)‖^2 := by
  have hh := E.extension_residual_orthogonal F τ htr hn hm x
  have hh' : τ (star ((E.extend F).expectation x)*
      (E.expectation x-(E.extend F).expectation x))=0 := by
    have hs := congrArg star hh
    rw [← map_star τ] at hs
    simpa only [star_mul,star_star,star_zero] using hs
  rw [norm_sq,norm_sq,norm_sq]
  have he : τ (star (E.expectation x)*E.expectation x)=
      τ (star ((E.extend F).expectation x)*(E.extend F).expectation x)+
      τ (star (E.expectation x-(E.extend F).expectation x)*
        (E.expectation x-(E.extend F).expectation x)) := by
    have hdecomp : star (E.expectation x)*E.expectation x=
        star ((E.extend F).expectation x)*(E.extend F).expectation x+
        star (E.expectation x-(E.extend F).expectation x)*
          (E.expectation x-(E.extend F).expectation x)+
        (star (E.expectation x-(E.extend F).expectation x)*(E.extend F).expectation x+
          star ((E.extend F).expectation x)*(E.expectation x-(E.extend F).expectation x)) := by
      simp only [star_sub]
      noncomm_ring
    simp only [hdecomp,map_add,hh,hh',add_zero]
  rw [he,Complex.add_re]

lemma extension_gns_contract (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (hn : n ≠ 0) (hm : m ≠ 0) (x : M) :
    ‖τ.toPreGNS ((E.extend F).expectation x)‖ ≤ ‖τ.toPreGNS (E.expectation x)‖ := by
  have hh := E.extension_pythagoras F τ htr hn hm x
  nlinarith [sq_nonneg ‖τ.toPreGNS (E.expectation x-(E.extend F).expectation x)‖,
    norm_nonneg (τ.toPreGNS (E.expectation x)),
    norm_nonneg (τ.toPreGNS ((E.extend F).expectation x))]

end MatrixSystem
end HochschildMatrixSystems

 

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma commutator_gns_le (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (a x : M) :
    ‖τ.toPreGNS (x*a-a*x)‖ ≤ 2*‖a‖*‖τ.toPreGNS x‖ := by
  calc
    _ ≤ ‖τ.toPreGNS (x*a)‖+‖τ.toPreGNS (a*x)‖ := by
      rw [map_sub]; exact norm_sub_le _ _
    _ ≤ ‖a‖*‖τ.toPreGNS x‖+‖a‖*‖τ.toPreGNS x‖ :=
      add_le_add (preGNS_norm_mul_right_le τ htr _ _) (preGNS_norm_mul_le τ _ _)
    _ = _ := by ring

include e in
lemma exists_matrix_displacement
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (a : M) (ha : 0<‖τ.toPreGNS (a-(τ a) • (1:M))‖) :
    ∃ (m : ℕ) (F : MatrixSystem M m) (s : Finset (Fin m)), 0 < m ∧
      IsStarProjection (∑ i ∈ s,F.entry i i) ∧
      ‖τ.toPreGNS (a-(τ a) • (1:M))‖/16 <
        ‖τ.toPreGNS ((∑ i ∈ s,F.entry i i)*a-a*(∑ i ∈ s,F.entry i i))‖ := by
  obtain ⟨p,hp,hpdisp⟩ := exists_projection_displacement e τ hτ h1 htr hfaith hfactor a ha
  let t := ‖τ.toPreGNS (a-(τ a) • (1:M))‖
  let ε : ℝ := t/(64*(‖a‖+1))
  have hε : 0<ε := div_pos ha (by positivity)
  obtain ⟨m,F,s,hm,hq,hqp,happrox⟩ := exists_matrix_projection_approx e τ hτ htr hfaith
    hdiff h1 hfactor hp hε
  refine ⟨m,F,s,hm,hq,?_⟩
  let q := ∑ i ∈ s,F.entry i i
  have herr : ‖τ.toPreGNS (p*a-a*p)‖ ≤ ‖τ.toPreGNS (q*a-a*q)‖+2*‖a‖*ε := by
    calc
      _ = ‖τ.toPreGNS (q*a-a*q)+τ.toPreGNS ((p-q)*a-a*(p-q))‖ := by
        rw [← map_add]; congr 2; noncomm_ring
      _ ≤ ‖τ.toPreGNS (q*a-a*q)‖+‖τ.toPreGNS ((p-q)*a-a*(p-q))‖ := norm_add_le _ _
      _ ≤ ‖τ.toPreGNS (q*a-a*q)‖+2*‖a‖*ε :=
        add_le_add_right ((commutator_gns_le τ htr a (p-q)).trans
          (mul_le_mul_of_nonneg_left happrox.le (by positivity))) _
  have hsmall : 2*‖a‖*ε ≤ t/32 := by
    have heq : ε*(64*(‖a‖+1))=t := div_mul_cancel₀ _ (by positivity)
    nlinarith [hε.le]
  change t/16 < ‖τ.toPreGNS (q*a-a*q)‖
  change t/8 < _ at hpdisp
  linarith

end HochschildQuantization

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildMatrixSystems
namespace MatrixSystem
open BoundedHochschild HochschildRigidity HochschildSakai HochschildQuantization
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {n : ℕ} (E : MatrixSystem M n)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma commutant_gns_norm (a : E.commutant) :
    ‖(E.commutantTrace τ).toPreGNS a‖ = ‖τ.toPreGNS (a:M)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq,norm_sq]
  rfl

include e in
 

theorem exists_energy_decreasing_extension
    (hn : 0<n) (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (x : M) (hx : 0<‖τ.toPreGNS (E.expectation x-(τ x) • (1:M))‖) :
    ∃ (m : ℕ) (F : MatrixSystem E.commutant m), 0 < m ∧
      ‖τ.toPreGNS ((E.extend F).expectation x)‖^2 +
        (‖τ.toPreGNS (E.expectation x-(τ x) • (1:M))‖/32)^2 <
          ‖τ.toPreGNS (E.expectation x)‖^2 := by
  classical
  let hL := mul_hasPreadjoint e
  let hR := mul_right_hasPreadjoint e
  obtain ⟨P,hPn,hP⟩ := exists_abstract_star_preadjoint e
  let eC := E.commutantPredualEquiv e hL hR P hP
  let ρ := E.commutantTrace τ
  let a : E.commutant := ⟨E.expectation x,E.commute_expectation x⟩
  have hat : ρ a=τ x := E.trace_expectation τ htr (Nat.ne_of_gt hn) x
  have han : ‖ρ.toPreGNS (a-(ρ a) • (1:E.commutant))‖=
      ‖τ.toPreGNS (E.expectation x-(τ x) • (1:M))‖ := by
    rw [E.commutant_gns_norm τ]
    rw [hat]
    rfl
  obtain ⟨m,F,s,hm,hq,hdisp⟩ := exists_matrix_displacement eC ρ
    (E.commutantTrace_normal e hL hR P hP τ hτ)
    (E.commutantTrace_one τ h1) (E.commutantTrace_tracial τ htr)
    (E.commutantTrace_faithful τ hfaith)
    (E.factor_of_commutant _ rfl hfactor)
    (E.commutant_no_minimal ⟨0,hn⟩ hdiff) a (han ▸ hx)
  refine ⟨m,F,hm,?_⟩
  let q : E.commutant := ∑ i ∈ s,F.entry i i
  let b : M := (E.extend F).expectation x
  have hbq : Commute b (q:M) := by
    change Commute b (E.commutant.subtype (∑ i ∈ s,F.entry i i))
    rw [map_sum]
    apply Commute.sum_right
    intro i hi
    exact (E.extension_expectation_commutes F x).2 i i
  have hqnorm : ‖(q:M)‖ ≤ 1 := hq.norm_le
  have hbound : ‖ρ.toPreGNS (q*a-a*q)‖ ≤ 2*‖τ.toPreGNS (E.expectation x-b)‖ := by
    rw [E.commutant_gns_norm τ]
    change ‖τ.toPreGNS ((q:M)*E.expectation x-E.expectation x*(q:M))‖ ≤ _
    have he : (q:M)*E.expectation x-E.expectation x*(q:M)=
        (q:M)*(E.expectation x-b)-(E.expectation x-b)*(q:M) := by
      have hh := hbq.eq
      noncomm_ring [hh]
    rw [he,map_sub]
    calc
      _ ≤ ‖τ.toPreGNS ((q:M)*(E.expectation x-b))‖+
          ‖τ.toPreGNS ((E.expectation x-b)*(q:M))‖ := norm_sub_le _ _
      _ ≤ ‖(q:M)‖*‖τ.toPreGNS (E.expectation x-b)‖+
          ‖(q:M)‖*‖τ.toPreGNS (E.expectation x-b)‖ :=
        add_le_add (preGNS_norm_mul_le τ _ _) (preGNS_norm_mul_right_le τ htr _ _)
      _ ≤ _ := by nlinarith [norm_nonneg (τ.toPreGNS (E.expectation x-b))]
  rw [han] at hdisp
  have hp := E.extension_pythagoras F τ htr (Nat.ne_of_gt hn) (Nat.ne_of_gt hm) x
  change ‖τ.toPreGNS (E.expectation x)‖^2=‖τ.toPreGNS b‖^2+
    ‖τ.toPreGNS (E.expectation x-b)‖^2 at hp
  have hstrict : ‖τ.toPreGNS (E.expectation x-(τ x) • (1:M))‖/32 <
      ‖τ.toPreGNS (E.expectation x-b)‖ := by linarith
  have hs := sq_lt_sq₀ (by positivity : 0 ≤ ‖τ.toPreGNS (E.expectation x-(τ x) • (1:M))‖/32)
    (norm_nonneg (τ.toPreGNS (E.expectation x-b)))
  change ‖τ.toPreGNS b‖^2+_ < _
  linarith [hs.mpr hstrict]

end MatrixSystem
end HochschildMatrixSystems
end

end OAI
