import Mathlib
import OAI.NumberTheory.PrimePackets.RealMellin
import OAI.NumberTheory.PrimePackets.SubquadraticGrowth

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma idealThetaXi_normalized_reflection_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ)^s * idealThetaXi σ hn I s =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        (((FractionalIdeal.absNorm (traceDualIdeal I).val : ℝ) : ℂ)^(1-s) *
          idealThetaXi σ hn (traceDualIdeal I) (1-s)) := by
  rw [idealThetaXi_reflection_totallyReal σ hn  I s, ← mul_assoc, abs_inv,
    embeddingMatrix_abs_det_fractionalIdeal]
  rw [traceDual_functional_factor (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))
    (fractionalIdeal_absNorm_pos I) (fractionalIdeal_absNorm_pos (traceDualIdeal I))
    (traceDualIdeal_norm_product σ hn I), mul_assoc]

lemma classThetaXi_reflection_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (s : ℂ) :
    classThetaXi σ hn s =
      Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        classThetaXi σ hn (1-s) := by
  unfold classThetaXi
  trans Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
    ∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (traceDualIdeal (classRepresentative K c)).val : ℝ) : ℂ)^(1-s) *
        idealThetaXi σ hn (traceDualIdeal (classRepresentative K c)) (1-s)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c _ => idealThetaXi_normalized_reflection_totallyReal σ hn  _ s)
  congr 1
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
        ((FractionalIdeal.absNorm (classRepresentative K (traceDualClassEquiv K c)).val : ℝ) : ℂ)^(1-s) *
          idealThetaXi σ hn (classRepresentative K (traceDualClassEquiv K c)) (1-s) := by
      apply Finset.sum_congr rfl
      intro c _
      apply idealThetaXi_normalized_congr_totallyReal σ hn 
      rw [classRepresentative_spec, traceDualClassEquiv_apply]
    _ = _ := (traceDualClassEquiv K).sum_comp (fun c : ClassGroup (𝓞 K) =>
      ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^(1-s) *
        idealThetaXi σ hn (classRepresentative K c) (1-s))

theorem completedThetaXi_functionalEquation_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     (s : ℂ) :
    completedThetaXi σ hn s = completedThetaXi σ hn (1-s) := by
  unfold completedThetaXi
  rw [classThetaXi_reflection_totallyReal σ hn  s]
  calc
    _ = ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
        (Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) *
          Complex.exp (((1/2 : ℂ)-s)*(Real.log |(NumberField.discr K : ℝ)| : ℂ))) *
        classThetaXi σ hn (1-s) := by ring
    _ = _ := by rw [completion_reflection_factor]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma completedThetaXi_conj_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  (s : ℂ) :
    completedThetaXi σ hn (conj s) = conj (completedThetaXi σ hn s) := by
  have H : Differentiable ℂ (conj ∘ completedThetaXi σ hn ∘ conj) := by
    intro z
    apply differentiableAt_conj_conj_iff.mpr
    exact completedThetaXi_entire σ hn _
  have HE := entire_eq_of_real_eq H (completedThetaXi_entire σ hn) (fun r hr => by
    simp only [Function.comp_apply, Complex.conj_ofReal]
    rw [completedThetaXi_real_eq_totallyReal σ hn  hr, totallyRealCompletedXi_real])
  have HE' := congrArg conj (congrFun HE s)
  simpa using HE'

lemma completedThetaXi_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    completedThetaXi σ hn 1 = completedXiBoundaryValue K := by
  have HL : Tendsto (fun r : ℝ => completedThetaXi σ hn r) (𝓝[>] 1)
      (𝓝 (completedThetaXi σ hn 1)) := by
    exact (completedThetaXi_entire σ hn 1).continuousAt.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left)
  apply tendsto_nhds_unique HL
  apply (tendsto_completedXi_from_right K).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (completedThetaXi_real_eq_totallyReal σ hn  hr).symm

lemma completedThetaXi_zero_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    completedThetaXi σ hn 0 = completedXiBoundaryValue K := by
  rw [completedThetaXi_functionalEquation_totallyReal σ hn  0, sub_zero,
    completedThetaXi_one_totallyReal σ hn ]

lemma completedThetaXi_ne_zero_of_re_gt_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_eq_totallyReal σ hn  hs]
  exact totallyRealCompletedXi_ne_zero K hs

lemma completedThetaXi_ne_zero_of_re_neg_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : s.re < 0) :
    completedThetaXi σ hn s ≠ 0 := by
  rw [completedThetaXi_functionalEquation_totallyReal σ hn  s]
  apply completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn 
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma dedekindXiZeros_re_mem_Icc_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) 
    {s : ℂ} (hs : s ∈ dedekindXiZeros σ hn) : s.re ∈ Icc (0:ℝ) 1 := by
  constructor
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_neg_totallyReal σ hn  (lt_of_not_ge h) hs
  · by_contra h
    exact completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn  (lt_of_not_ge h) hs

lemma dedekindXiZeros_ne_one_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    (1 : ℂ) ∉ dedekindXiZeros σ hn := by
  change completedThetaXi σ hn 1 ≠ 0
  rw [completedThetaXi_one_totallyReal σ hn ]
  exact completedXiBoundaryValue_ne_zero K

lemma dedekindXiZeros_ne_zero_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  :
    (0 : ℂ) ∉ dedekindXiZeros σ hn := by
  change completedThetaXi σ hn 0 ≠ 0
  rw [completedThetaXi_zero_totallyReal σ hn ]
  exact completedXiBoundaryValue_ne_zero K

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

theorem dedekindXi_hasSum_realZeroPole_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℝ} (hs : 1 < s) :
    HasSum (realZeroPole (completedThetaXi σ hn) s)
      (1/s + 1/(s-1) + Real.log |(NumberField.discr K : ℝ)|/2 +
        deriv (realDedekindZeta K) s / realDedekindZeta K s +
          archimedeanZetaTerm (finrank ℚ K) s) := by
  have H := hasSum_realZeroPole (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero_totallyReal σ hn )
    (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation_totallyReal σ hn  z).symm)
    (fun z hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn  hz).2) hs
  rwa [completedThetaXi_logDeriv_totallyReal σ hn  (by simpa using hs),
    totallyRealCompletedXi_logDeriv_re K hs] at H

lemma dedekindXi_realZeroPole_nonneg_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {s : ℝ} (hs : 1 < s) (ρ : ℂ) :
    0 ≤ realZeroPole (completedThetaXi σ hn) s ρ :=
  realZeroPole_nonneg (completedThetaXi_entire σ hn) (dedekindXiZeros_ne_zero_totallyReal σ hn )
    (fun _ hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn  hz).2) hs ρ

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

lemma completedThetaXi_logDeriv_base_le_totallyReal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
     {B L : ℝ}
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL1 : 1 ≤ L)
    (hB : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm (d+1) s| ≤ B) :
    (logDeriv (completedThetaXi σ hn) (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+B+1 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hLp; linarith
  have hsu : 1+1/L ≤ 2 := by
    have H := (div_le_one hLp).mpr hL1
    linarith
  rw [completedThetaXi_logDeriv_totallyReal σ hn  (by simpa using hs),
    totallyRealCompletedXi_logDeriv_re K hs, hn, ← hL]
  have HG := (abs_le.mp (hB (1+1/L) ⟨hs.le,hsu⟩)).2
  have HD : deriv (realDedekindZeta K) (1+1/L) / realDedekindZeta K (1+1/L) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (realDedekindZeta_deriv_nonpos K hs)
      (realDedekindZeta_pos K hs).le
  have Hr : 1/(1+1/L) ≤ 1 := (div_le_one (by linarith)).mpr hs.le
  have HE : 1/(1+1/L-1) = L := by field_simp; ring
  rw [HE]
  linarith

theorem dedekind_near_one_zero_real_simple_unique_totallyReal (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        ,
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  obtain ⟨B,hB,harch⟩ := archimedeanZetaTerm_bounded (d+1)
  refine ⟨max 1 (26*(B+1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K _ _ _ σ hn  hL ρ hρ hρbox
  have hL1 : 1 < Real.log |(NumberField.discr K : ℝ)| :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := by linarith
  have Hbase := completedThetaXi_logDeriv_base_le_totallyReal σ hn  rfl hL1.le harch
  apply nearOneBox_real_simple_unique (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero_totallyReal σ hn ) (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation_totallyReal σ hn  z).symm)
    (completedThetaXi_conj_totallyReal σ hn )
    (fun z hz => (dedekindXiZeros_re_mem_Icc_totallyReal σ hn  hz).2)
    hLp (lt_of_le_of_lt (le_max_right _ _) hL) _ hρ hρbox
  simpa only [add_assoc] using Hbase

end PrimeDegreePackets.HeckeMellin

open IntermediateField Module
namespace PrimeDegreePackets

lemma normalClosure_isTotallyReal {K L : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Field L] [CharZero L]
    [Algebra.IsAlgebraic ℚ L] :
    NumberField.IsTotallyReal (normalClosure ℚ K L) := by
  let M : IntermediateField ℚ L :=
    (NumberField.maximalRealSubfield L).toIntermediateField (fun q => by
      simp)
  have hM : normalClosure ℚ K L ≤ M := by
    rw [normalClosure_le_iff]
    intro f
    let : NumberField.IsTotallyReal f.fieldRange :=
      NumberField.IsTotallyReal.ofRingEquiv f.equivFieldRange.toRingEquiv
    exact NumberField.IsTotallyReal.le_maximalRealSubfield f.fieldRange.toSubfield
  change NumberField.IsTotallyReal (normalClosure ℚ K L).toSubfield
  exact NumberField.isTotallyReal_iff_le_maximalRealSubfield.mpr hM

 
def embeddingPermutation {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] (σ : N ≃ₐ[F] N) : Equiv.Perm (K →ₐ[F] N) where
  toFun f := σ.toAlgHom.comp f
  invFun f := σ.symm.toAlgHom.comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

 

lemma embeddingPermutation_injective {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] [Algebra.IsAlgebraic F K]
    [IsNormalClosure F K N] :
    Function.Injective (embeddingPermutation (F := F) (K := K) (N := N)) := by
  intro σ τ h
  let E : IntermediateField F N := {
    carrier := {x | σ x = τ x}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by intro x y hx hy; change σ x = τ x at hx; change σ y = τ y at hy
                   change σ (x+y) = τ (x+y); simp only [map_add,hx,hy]
    mul_mem' := by intro x y hx hy; change σ x = τ x at hx; change σ y = τ y at hy
                   change σ (x*y) = τ (x*y); simp only [map_mul,hx,hy]
    inv_mem' := by intro x hx; change σ x = τ x at hx
                   change σ (x⁻¹) = τ (x⁻¹); simp only [map_inv₀,hx]
    algebraMap_mem' := by intro r; simp }
  have hE : normalClosure F K N ≤ E := by
    rw [normalClosure_le_iff]
    intro f x hx
    obtain ⟨y,rfl⟩ := hx
    exact congrArg (fun p : Equiv.Perm (K →ₐ[F] N) => p f y) h
  have ht : normalClosure F K N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
  rw [ht] at hE
  ext x
  exact hE (show x ∈ (⊤ : IntermediateField F N) from trivial)

 

theorem normalClosure_finrank_le_factorial {F K N : Type*} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra F N] [FiniteDimensional F K] [FiniteDimensional F N]
    [IsNormalClosure F K N] [IsGalois F N] :
    finrank F N ≤ (finrank F K).factorial := by
  rw [←IsGalois.card_aut_eq_finrank F N]
  calc
    Nat.card (N ≃ₐ[F] N) ≤ Nat.card (Equiv.Perm (K →ₐ[F] N)) :=
      Nat.card_le_card_of_injective _ embeddingPermutation_injective
    _ = (Nat.card (K →ₐ[F] N)).factorial := Nat.card_perm
    _ ≤ (finrank F K).factorial := Nat.factorial_le (card_algHom_le_finrank F K N)

 

theorem totallyReal_normalClosure_degree {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] :
    NumberField.IsTotallyReal (normalClosure ℚ K (AlgebraicClosure K)) ∧
      finrank ℚ (normalClosure ℚ K (AlgebraicClosure K)) ≤ (finrank ℚ K).factorial := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans ℚ K _
  let : IsAlgClosure ℚ (AlgebraicClosure K) := ⟨inferInstance,inferInstance⟩
  let : Nonempty (K →ₐ[ℚ] AlgebraicClosure K) := ⟨IsScalarTower.toAlgHom ℚ K _⟩
  let : IsNormalClosure ℚ K (normalClosure ℚ K (AlgebraicClosure K)) :=
    isNormalClosure_normalClosure ℚ K (AlgebraicClosure K)
  let : Normal ℚ (normalClosure ℚ K (AlgebraicClosure K)) := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ (normalClosure ℚ K (AlgebraicClosure K)) := {}
  exact ⟨normalClosure_isTotallyReal,normalClosure_finrank_le_factorial⟩

end PrimeDegreePackets

open Module IntermediateField
open scoped BigOperators NumberField Pointwise
namespace PrimeDegreePackets

lemma subalgebra_sup_toSubmodule_mul {F N : Type*} [CommSemiring F] [CommSemiring N]
    [Algebra F N] (A B : Subalgebra F N) :
    (A ⊔ B).toSubmodule = A.toSubmodule * B.toSubmodule := by
  simpa only [Algebra.adjoin_union,Algebra.adjoin_eq] using
    Algebra.adjoin_union_coe_submodule F (A : Set N) (B : Set N)

lemma intermediate_finset_sup_toSubmodule {F N I : Type*} [Field F] [Field N]
    [Algebra F N] [Algebra.IsAlgebraic F N]
    (s : Finset I) (A : I → IntermediateField F N) :
    (s.sup A).toSubalgebra.toSubmodule = ∏ i ∈ s, (A i).toSubalgebra.toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.toSubmodule_bot]
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.prod_insert hi,
      IntermediateField.sup_toSubalgebra_of_isAlgebraic,subalgebra_sup_toSubmodule_mul,ih]
    exact Or.inl inferInstance

 

theorem normalClosure_integral_basis_height {K N I : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [IsNormalClosure ℚ K N]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 1 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    ∃ c : Basis (Fin (finrank ℚ N)) ℚ N,
      (∀ i, IsIntegral ℤ (c i)) ∧
      ∀ (σ : N →ₐ[ℚ] ℂ) i, ‖σ (c i)‖ ≤ B ^ finrank ℚ K := by
  classical
  let S (f : K →ₐ[ℚ] N) : Set N := Set.range (fun i => f (b i))
  let P : Set N := ∏ f : K →ₐ[ℚ] N, S f
  have hspan (f : K →ₐ[ℚ] N) :
      Submodule.span ℚ (S f) = f.fieldRange.toSubalgebra.toSubmodule := by
    change Submodule.span ℚ (Set.range (f.toLinearMap ∘ b)) = _
    rw [Set.range_comp,← Submodule.map_span,b.span_eq,Submodule.map_top]
    rfl
  have htop : Submodule.span ℚ P = ⊤ := by
    unfold P
    rw [← Submodule.prod_span]
    simp_rw [hspan]
    rw [← intermediate_finset_sup_toSubmodule]
    have hn : Finset.univ.sup (fun f : K →ₐ[ℚ] N => f.fieldRange) = ⊤ := by
      rw [Finset.sup_univ_eq_iSup]
      exact (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
    rw [hn]
    rfl
  have hP (x : N) (hx : x ∈ P) : IsIntegral ℤ x ∧
      ∀ σ : N →ₐ[ℚ] ℂ, ‖σ x‖ ≤ B ^ finrank ℚ K := by
    obtain ⟨v,hv,rfl⟩ := (Set.mem_fintype_prod S x).mp hx
    constructor
    · apply IsIntegral.prod
      intro f _
      obtain ⟨i,hi⟩ := hv f
      rw [← hi]
      exact map_isIntegral_int f (hb i)
    · intro σ
      rw [map_prod,norm_prod]
      calc
        ∏ f : K →ₐ[ℚ] N, ‖σ (v f)‖ ≤ ∏ _f : K →ₐ[ℚ] N, B := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro f _
          obtain ⟨i,hi⟩ := hv f
          rw [← hi]
          exact hheight (σ.comp f) i
        _ = B ^ Fintype.card (K →ₐ[ℚ] N) := by simp
        _ ≤ B ^ finrank ℚ K := by
          apply pow_le_pow_right₀ hB
          simpa only [Fintype.card_eq_nat_card] using card_algHom_le_finrank ℚ K N
  let c₀ := Basis.ofSpan (show ⊤ ≤ Submodule.span ℚ P from htop.ge)
  let T := (linearIndepOn_empty ℚ (id : N → N)).extend (Set.empty_subset P)
  have : Finite T := c₀.linearIndependent.finite
  let : Fintype T := Fintype.ofFinite T
  let e : T ≃ Fin (finrank ℚ N) := Fintype.equivFinOfCardEq (finrank_eq_card_basis c₀).symm
  let c := c₀.reindex e
  refine ⟨c,?_,?_⟩
  · intro i
    exact (hP (c i) (Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℚ P from htop.ge) ⟨e.symm i,by simp [c,Basis.coe_reindex,c₀]⟩)).1
  · intro σ i
    exact (hP (c i) (Basis.ofSpan_subset (show ⊤ ≤ Submodule.span ℚ P from htop.ge) ⟨e.symm i,by simp [c,Basis.coe_reindex,c₀]⟩)).2 σ

 

theorem normalClosure_discr_le_basis_height {K N I : Type*}
    [Field K] [NumberField K] [Field N] [NumberField N] [IsNormalClosure ℚ K N]
    [Fintype I] [DecidableEq I] (b : Basis I ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℝ} (hB : 1 ≤ B)
    (hheight : ∀ (σ : K →ₐ[ℚ] ℂ) i, ‖σ (b i)‖ ≤ B) :
    |(NumberField.discr N : ℝ)| ≤
      ((finrank ℚ N).factorial * (B ^ finrank ℚ K) ^ finrank ℚ N)^2 := by
  obtain ⟨c,hc,hheightc⟩ := normalClosure_integral_basis_height (N := N) b hb hB hheight
  simpa only [Fintype.card_fin] using abs_discr_le_integral_basis_height c hc
    (pow_nonneg (le_trans zero_le_one hB) _) hheightc

end PrimeDegreePackets


namespace PrimeDegreePackets

 

def smallIntegralBasisConstant (d : ℕ) : ℝ :=
  max 1 (2 / (1 / (2*(d+1)))^d + d / (2*(d+1)))

def closureDiscriminantConstant (d : ℕ) : ℝ :=
  (((d+1).factorial).factorial *
    (2*smallIntegralBasisConstant d)^((d+1)*(d+1).factorial))^2

lemma closureDiscriminantConstant_pos (d : ℕ) : 0 < closureDiscriminantConstant d := by
  have h : 1 ≤ smallIntegralBasisConstant d := le_max_left _ _
  unfold closureDiscriminantConstant
  positivity

 

theorem normalClosure_discr_polynomial {d : ℕ} {K N : Type*}
    [Field K] [NumberField K] [Field N] [NumberField N]
    [IsNormalClosure ℚ K N]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    |(NumberField.discr N : ℝ)| ≤ closureDiscriminantConstant d *
      |(NumberField.discr K : ℝ)| ^ (2*((d+1)*(d+1).factorial)) := by
  classical
  let C := smallIntegralBasisConstant d
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  let D : ℝ := |(NumberField.discr K : ℝ)|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  let B := C * (Real.sqrt D + 1)
  have hB : 1 ≤ B := by
    have hs := Real.sqrt_nonneg D
    dsimp [B]
    nlinarith
  have hBD : B ≤ (2*C)*D := by
    have hs : Real.sqrt D ≤ D := (Real.sqrt_le_iff).2 ⟨hD0,by nlinarith⟩
    dsimp [B]
    nlinarith
  obtain ⟨b,hb,hheight⟩ := totallyReal_small_integral_basis σ hn
  have hheightB : ∀ (ρ : K →ₐ[ℚ] ℂ) i, ‖ρ (b i)‖ ≤ B := by
    intro ρ i
    apply (hheight ρ i).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hfirst := normalClosure_discr_le_basis_height (N := N) b hb hB hheightB
  let : Normal ℚ N := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ N := {}
  have hm : finrank ℚ N ≤ (d+1).factorial := by
    simpa only [hn] using (normalClosure_finrank_le_factorial (F := ℚ) (K := K) (N := N))
  have hBB : 1 ≤ (2*C)*D := hB.trans hBD
  have hp : (B ^ finrank ℚ K) ^ finrank ℚ N ≤
      ((2*C)*D)^((d+1)*(d+1).factorial) := by
    rw [hn,← pow_mul]
    exact (pow_le_pow_left₀ (le_trans zero_le_one hB) hBD _).trans
      (pow_le_pow_right₀ hBB (Nat.mul_le_mul_left _ hm))
  have hf : ((finrank ℚ N).factorial : ℝ) ≤ (((d+1).factorial).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hm
  calc
    |(NumberField.discr N : ℝ)| ≤
      ((finrank ℚ N).factorial * (B ^ finrank ℚ K) ^ finrank ℚ N)^2 := hfirst
    _ ≤ ((((d+1).factorial).factorial : ℝ) *
        ((2*C)*D)^((d+1)*(d+1).factorial))^2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul hf hp (by positivity) (by positivity)
    _ = closureDiscriminantConstant d * D ^ (2*((d+1)*(d+1).factorial)) := by
      dsimp [closureDiscriminantConstant,C]
      simp only [mul_pow]
      rw [← pow_mul]
      ring

 

theorem normalClosure_log_discr_uniform (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K N : Type*) [Field K] [NumberField K]
      [Field N] [NumberField N] [IsNormalClosure ℚ K N]
      (_σ : OrderedEmbeddings (d+1) K), finrank ℚ K = d+1 →
        Real.log (3*|(NumberField.discr N : ℝ)|) ≤
          C * Real.log (3*|(NumberField.discr K : ℝ)|) := by
  let A := closureDiscriminantConstant d
  let k := 2*((d+1)*(d+1).factorial)
  have hA : 0 < A := closureDiscriminantConstant_pos d
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := |Real.log (3*A)| / Real.log 3 + k + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro K N _ _ _ _ _ σ hn
  let D : ℝ := |(NumberField.discr K : ℝ)|
  let DN : ℝ := |(NumberField.discr N : ℝ)|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hDN : 0 < DN := by
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero N)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hbound : DN ≤ A*D^k := normalClosure_discr_polynomial σ hn
  have hlog : Real.log 3 ≤ Real.log (3*D) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hlogpos : 0 < Real.log (3*D) := h3.trans_le hlog
  have hx : |Real.log (3*A)| ≤
      (|Real.log (3*A)| / Real.log 3) * Real.log (3*D) := by
    have H := mul_le_mul_of_nonneg_left hlog
      (div_nonneg (abs_nonneg (Real.log (3*A))) h3.le)
    rwa [div_mul_cancel₀ _ h3.ne'] at H
  have hlogD : Real.log D ≤ Real.log (3*D) :=
    Real.log_le_log hD0 (by linarith)
  calc
    Real.log (3*DN) ≤ Real.log (3*(A*D^k)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hbound (by norm_num))
    _ = Real.log (3*A) + k*Real.log D := by
      rw [← mul_assoc,Real.log_mul (by positivity) (by positivity),Real.log_pow]
    _ ≤ |Real.log (3*A)| + k*Real.log (3*D) :=
      add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left hlogD (by positivity))
    _ ≤ C*Real.log (3*D) := by
      dsimp [C]
      nlinarith

end PrimeDegreePackets
end
end

end OAI
