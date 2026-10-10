import Mathlib
import OAI.NumberTheory.PrimePackets.FunctionalEquation

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
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
namespace PrimeDegreePackets

lemma isTotallyReal_of_isNormalClosure {K N : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Field N] [NumberField N] [IsNormalClosure ℚ K N] :
    NumberField.IsTotallyReal N := by
  have ht : normalClosure ℚ K N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
  have h := normalClosure_isTotallyReal (K := K) (L := N)
  rw [ht] at h
  let := h
  exact NumberField.IsTotallyReal.ofRingEquiv ((IntermediateField.topEquiv (F := ℚ) (E := N)).toRingEquiv)

lemma abs_discr_le_of_algHom {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] (f : K →ₐ[ℚ] N) :
    |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr N : ℝ)| := by
  let : Algebra K N := f.toRingHom.toAlgebra
  have H := Int.natAbs_le_of_dvd_ne_zero (NumberField.discr_dvd_discr K N)
    (NumberField.discr_ne_zero N)
  have H' : (|(NumberField.discr K)| : ℤ) ≤ |NumberField.discr N| := by
    simpa only [Int.natCast_natAbs] using (show ((NumberField.discr K).natAbs : ℤ) ≤
      ((NumberField.discr N).natAbs : ℤ) from by exact_mod_cast H)
  exact_mod_cast H'

lemma normalClosure_abs_discr_ge {K N : Type*} [Field K] [NumberField K]
    [Field N] [NumberField N] [IsNormalClosure ℚ K N] :
    |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr N : ℝ)| := by
  obtain ⟨f⟩ := IntermediateField.nonempty_algHom_of_splits
    (fun x : K => ⟨Algebra.IsIntegral.isIntegral x,
      IsNormalClosure.splits (F := ℚ) (K := K) (L := N) x⟩)
  exact abs_discr_le_of_algHom f

namespace HeckeMellin
open AnalyticGrowth

 

lemma boundedDegree_near_one_zero_real_simple_unique (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ}, d+1 ≤ n →
      ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1),
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  classical
  choose C hC hzero using dedekind_near_one_zero_real_simple_unique_totallyReal
  refine ⟨(∑ i ∈ Finset.range n, C i)+1,?_,?_⟩
  · have H := Finset.sum_nonneg (s := Finset.range n) (fun i _ => (hC i).le)
    linarith
  intro d hd K _ _ _ σ hn hL
  apply hzero d σ hn
  have H := Finset.single_le_sum (fun i _ => (hC i).le)
    (show d ∈ Finset.range n from Finset.mem_range.mpr (by omega))
  linarith

 

theorem normalClosure_zero_box_uniform (d : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ {K N : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        [Field N] [NumberField N] [IsNormalClosure ℚ K N] [NumberField.IsTotallyReal N]
        (_σ : OrderedEmbeddings (d+1) K) (_hn : finrank ℚ K = d+1)
        {m : ℕ} (τ : OrderedEmbeddings (m+1) N) (hm : finrank ℚ N = m+1),
      T < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros τ hm →
        InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) ρ →
        zeroMultiplicity (completedThetaXi τ hm) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ z, z ∈ dedekindXiZeros τ hm →
            InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) z → z = ρ := by
  obtain ⟨C,hC,hdisc⟩ := normalClosure_log_discr_uniform d
  obtain ⟨T,hT,hzero⟩ := boundedDegree_near_one_zero_real_simple_unique (d+1).factorial
  refine ⟨C,T,hC,hT,?_⟩
  intro K N _ _ _ _ _ _ _ σ hn m τ hm hL ρ hρ hbox
  let : Normal ℚ N := IsNormalClosure.normal (K := K)
  let : IsGalois ℚ N := {}
  have hdim : m+1 ≤ (d+1).factorial := by
    simpa only [hm,hn] using (normalClosure_finrank_le_factorial (F := ℚ) (K := K) (N := N))
  have hDK : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hDN : 0 < |(NumberField.discr N : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero N)
  have hlog : Real.log |(NumberField.discr K : ℝ)| ≤
      Real.log |(NumberField.discr N : ℝ)| :=
    Real.log_le_log hDK normalClosure_abs_discr_ge
  have hLN : 0 < Real.log |(NumberField.discr N : ℝ)| := hT.trans (hL.trans_le hlog)
  have hbound : Real.log |(NumberField.discr N : ℝ)| ≤
      C*Real.log (3*|(NumberField.discr K : ℝ)|) :=
    (Real.log_le_log hDN (by nlinarith)).trans (hdisc K N σ hn)
  have hboxes : ∀ z, InNearOneBox (C*Real.log (3*|(NumberField.discr K : ℝ)|)) z →
      InNearOneBox (Real.log |(NumberField.discr N : ℝ)|) z := by
    intro z hz
    have hi := one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<4) hLN)
      (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤4))
    exact ⟨by linarith [hz.1], hz.2.trans hi⟩
  obtain ⟨hs,hr,hu⟩ := hzero hdim τ hm (hL.trans_le hlog) ρ hρ (hboxes ρ hbox)
  exact ⟨hs,hr,fun z hz hb => hu z hz (hboxes z hb)⟩

end HeckeMellin
end PrimeDegreePackets


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

lemma integralFractionalIdeals_norm_summable {K : Type*} [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) : Summable (fun J : integralFractionalIdeals K =>
      (FractionalIdeal.absNorm J.1.val : ℝ)^(-s)) := by
  have H := ENNReal.summable_toReal (show
    (∑' J : integralFractionalIdeals K,
      ENNReal.ofReal ((FractionalIdeal.absNorm J.1.val : ℝ)^(-s))) ≠ ⊤ from by
    rw [integralFractionalIdeals_norm_tsum hs]; exact ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)] using H

lemma integralFractionalIdeals_absNorm_ge_one {K : Type*} [Field K] [NumberField K]
    (J : integralFractionalIdeals K) : 1 ≤ (FractionalIdeal.absNorm J.1.val : ℝ) := by
  obtain ⟨I,hI⟩ := (integralFractionalIdealsEquiv K).surjective J
  subst J
  change 1 ≤ (FractionalIdeal.absNorm (I.1 : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by simpa only [ne_eq, Ideal.absNorm_eq_zero_iff] using I.2))

 
def idealClassDirichlet (K : Type*) [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' J : integralFractionalIdeals K,
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)

lemma idealClassDirichlet_summable {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun J : integralFractionalIdeals K =>
      w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)) := by
  classical
  let M := ∑ c : ClassGroup (𝓞 K), ‖w c‖
  apply Summable.of_norm_bounded ((integralFractionalIdeals_norm_summable hs).mul_left M)
  intro J
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _), Complex.neg_re]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _)
  exact Finset.single_le_sum (fun c _ => norm_nonneg (w c)) (Finset.mem_univ _)

lemma idealClassDirichlet_differentiableOn {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) :
    DifferentiableOn ℂ (idealClassDirichlet K w) {s | 1 < s.re} := by
  classical
  intro s hs
  obtain ⟨t,ht,hts⟩ := exists_between (show 1 < s.re from hs)
  let M := ∑ c : ClassGroup (𝓞 K), ‖w c‖
  have H : DifferentiableOn ℂ (idealClassDirichlet K w) {z | t < z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((integralFractionalIdeals_norm_summable ht).mul_left M)
    · intro J
      apply Differentiable.differentiableOn
      apply Differentiable.const_mul
      apply Differentiable.const_cpow (differentiable_id.neg)
      exact Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne')
    · exact isOpen_lt continuous_const Complex.continuous_re
    · intro J z hz
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _), Complex.neg_re]
      apply mul_le_mul
      · exact Finset.single_le_sum (fun c _ => norm_nonneg (w c)) (Finset.mem_univ _)
      · exact Real.rpow_le_rpow_of_exponent_le (integralFractionalIdeals_absNorm_ge_one J) (neg_le_neg (le_of_lt (show t < z.re from hz)))
      · exact Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _
      · exact Finset.sum_nonneg (fun c _ => norm_nonneg (w c))
  exact (H.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hts)).differentiableWithinAt

 
def idealClassThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), w c⁻¹ *
    (((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^s *
      idealThetaXi σ hn (classRepresentative K c) s)

lemma idealClassThetaXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) :
    Differentiable ℂ (idealClassThetaXi σ hn w) := by
  unfold idealClassThetaXi
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.const_mul
  apply Differentiable.mul _ (idealThetaXi_entire σ hn _)
  apply Differentiable.const_cpow differentiable_id
  exact Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt (fractionalIdeal_absNorm_pos _)))

lemma idealClassDirichlet_partition {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    idealClassDirichlet K w s = ∑ c : ClassGroup (𝓞 K), w c⁻¹ *
      ∑' J : integralIdealClassFiber (classRepresentative K c),
        ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s) := by
  classical
  let F := fun J : integralFractionalIdeals K =>
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)
  have H := ((idealClassPartitionEquiv K).summable_iff.mpr
    (idealClassDirichlet_summable w hs)).tsum_sigma
  change (∑' x, F (idealClassPartitionEquiv K x)) = _ at H
  rw [(idealClassPartitionEquiv K).tsum_eq F] at H
  simp only [tsum_fintype] at H
  rw [idealClassDirichlet, show (∑' J, F J) = _ from H]
  apply Finset.sum_congr rfl
  intro c _
  change (∑' J : integralIdealClassFiber (classRepresentative K c),
    w (ClassGroup.mk K J.1) * ((FractionalIdeal.absNorm J.1.val : ℝ) : ℂ)^(-s)) = _
  simp_rw [show ∀ J : integralIdealClassFiber (classRepresentative K c),
    ClassGroup.mk K J.1 = c⁻¹ from fun J => by rw [J.2.2,classRepresentative_spec]]
  exact tsum_mul_left

lemma idealThetaMellin_normalized_real {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℝ} (hs : 1 < s) :
    (FractionalIdeal.absNorm I.val : ℝ)^s *
      (nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) I s).toReal =
    2 * realHeckeFactor (d+1) s *
      ∑' J : integralIdealClassFiber I, (FractionalIdeal.absNorm J.1.val : ℝ)^(-s) := by
  have HS : 0 < s := zero_lt_one.trans hs
  have H : ENNReal.ofReal ((FractionalIdeal.absNorm I.val : ℝ)^s) *
        nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ) I s =
      2 * ENNReal.ofReal (realHeckeFactor (d+1) s) *
        ∑' J : integralIdealClassFiber I,
          ENNReal.ofReal ((FractionalIdeal.absNorm J.val.val : ℝ)^(-s)) := by
    unfold nonnegativeIdealThetaMellin
    rw [fractionalIdealTheta_mellin_lintegral_totallyReal σ hn I
      (orderedThetaLogDomain_fundamental σ) HS,
      rpow_cancel_ennreal_factor (fractionalIdeal_absNorm_pos I) s (realHeckeFactor_nonneg _ HS)]
  have H' := congrArg ENNReal.toReal H
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)] at H'
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _),
    ENNReal.toReal_ofReal (realHeckeFactor_nonneg _ HS)] using H'

 

theorem idealClassThetaXi_real_eq {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (w : ClassGroup (𝓞 K) → ℂ) {s : ℝ} (hs : 1 < s) :
    idealClassThetaXi σ hn w s =
      ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      (2*realHeckeFactor (d+1) s : ℝ) * idealClassDirichlet K w s := by
  classical
  rw [idealClassDirichlet_partition w (by simpa using hs)]
  unfold idealClassThetaXi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [idealThetaXi_eq_integral_totallyReal σ hn _ (by simpa using hs),
    idealThetaMellinIntegral_real]
  have H := congrArg (fun r : ℝ => (r : ℂ))
    (idealThetaMellin_normalized_real σ hn (classRepresentative K c) hs)
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_tsum] at H
  simp_rw [Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le,
    Complex.ofReal_neg] at H
  rw [Complex.ofReal_mul]
  calc
    _ = w c⁻¹ *
      (((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
      ((((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^(s : ℂ)) *
        ((nonnegativeIdealThetaMellin σ hn (orderedThetaLogDomain σ)
          (classRepresentative K c) s).toReal : ℂ))) := by ring
    _ = _ := by rw [H]; push_cast; ring

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 
def completedIdealClassXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
    Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) *
      idealClassThetaXi σ hn w s

lemma completedIdealClassXi_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) :
    Differentiable ℂ (completedIdealClassXi σ hn w) := by
  unfold completedIdealClassXi
  exact (Differentiable.const_mul (by fun_prop) _).mul (idealClassThetaXi_entire σ hn w)

lemma completedIdealClassXi_real_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) {s : ℝ} (hs : 1 < s) :
    completedIdealClassXi σ hn w s = (s : ℂ)*(s-1)*
      completionExponential (d+1) |(NumberField.discr K : ℝ)| s *
        Complex.Gamma (s/2)^(d+1)*idealClassDirichlet K w s := by
  unfold completedIdealClassXi
  rw [idealClassThetaXi_real_eq σ hn w hs, Complex.ofReal_mul, Complex.ofReal_ofNat,
    realHeckeFactor_ofReal]
  let E : ℂ := Complex.exp ((s : ℂ)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2)
  let P : ℂ := (Real.pi : ℂ)^(-(s : ℂ)/2)
  let G : ℂ := Complex.Gamma ((s : ℂ)/2)
  have H := hecke_factor_cancellation (d+1) (by omega) (s : ℂ) P G
  calc
    _ = E * (((2:ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
        ((((d+1 : ℕ) : ℂ)*s/2)*(((d+1 : ℕ) : ℂ)*s/2-((d+1 : ℕ) : ℂ)/2)) *
        (2*(2/((d+1 : ℕ) : ℂ)*((1/2:ℂ)*P*G)^(d+1)))) * idealClassDirichlet K w s := by
      dsimp [E,P,G]
      ring
    _ = E * ((s : ℂ)*(s-1)*P^(d+1)*G^(d+1)) * idealClassDirichlet K w s := by rw [H]
    _ = (s : ℂ)*(s-1)*(E*P^(d+1))*G^(d+1)*idealClassDirichlet K w s := by ring
    _ = _ := by rw [show E*P^(d+1) = completionExponential (d+1) |(NumberField.discr K : ℝ)| s from
      conductor_pi_factor _ _ _]

 

theorem completedIdealClassXi_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    completedIdealClassXi σ hn w s = s*(s-1)*
      completionExponential (d+1) |(NumberField.discr K : ℝ)| s *
        Complex.Gamma (s/2)^(d+1)*idealClassDirichlet K w s := by
  apply halfPlane_eq_of_real_eq (completedIdealClassXi_entire σ hn w).differentiableOn
    _ (fun r hr => completedIdealClassXi_real_eq σ hn w hr) hs
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · exact ((differentiableAt_id.mul (differentiableAt_id.sub_const (1:ℂ))).mul
      ((completionExponential_hasDerivAt _ _ _).differentiableAt)).mul
        ((gammaHalf_hasDerivAt (by change 1 < z.re at hz; linarith : 0 < z.re)).differentiableAt.pow _)
  · exact (idealClassDirichlet_differentiableOn w).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

lemma idealThetaXi_zero_value {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    idealThetaXi σ hn I 0 =
      ((volume (orderedThetaLogDomain σ)).toReal : ℂ)*(((d+1 : ℕ) : ℂ)/2) := by
  simp [idealThetaXi, thetaMellinXi, measureReal_def]

lemma idealThetaXi_normalized_one_value {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((FractionalIdeal.absNorm I.val : ℝ) : ℂ) * idealThetaXi σ hn I 1 =
      Complex.exp ((-1/2 : ℂ)*(Real.log |(NumberField.discr K : ℝ)| : ℂ)) *
        (((volume (orderedThetaLogDomain σ)).toReal : ℂ)*(((d+1 : ℕ) : ℂ)/2)) := by
  have H := idealThetaXi_normalized_reflection_totallyReal σ hn I (1 : ℂ)
  norm_num only [Complex.cpow_one, sub_self, Complex.cpow_zero, one_mul] at H
  rw [H, idealThetaXi_zero_value]
  congr 2
  norm_num

lemma idealClassThetaXi_zero_of_sum_eq_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    idealClassThetaXi σ hn w 0 = 0 := by
  classical
  simp only [idealClassThetaXi, Complex.cpow_zero, one_mul, idealThetaXi_zero_value]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K))) w)
  rw [← Finset.sum_mul, hw', zero_mul]

lemma idealClassThetaXi_one_of_sum_eq_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    idealClassThetaXi σ hn w 1 = 0 := by
  classical
  simp only [idealClassThetaXi, Complex.cpow_one, idealThetaXi_normalized_one_value]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K))) w)
  rw [← Finset.sum_mul, hw', zero_mul]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma finite_group_character_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : ∑ g, χ g = 0 := by
  classical
  obtain ⟨g,hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra H
    push Not at H
    apply hχ
    ext g
    exact H g
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul, Equiv.coe_mulLeft] using
    (Equiv.sum_comp (Equiv.mulLeft g) (fun g => χ g))

 

def entireIdealClassL {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) : ℂ → ℂ :=
  dslope (dslope (completedIdealClassXi σ hn w) 0) 1

lemma entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ] at hf ⊢
  exact (Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ nhds a)).mpr hf

lemma entireIdealClassL_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) :
    Differentiable ℂ (entireIdealClassL σ hn w) :=
  entire_dslope (entire_dslope (completedIdealClassXi_entire σ hn w) 0) 1

lemma completedIdealClassXi_zero_of_sum_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    completedIdealClassXi σ hn w 0 = 0 := by
  simp only [completedIdealClassXi, idealClassThetaXi_zero_of_sum_eq_zero σ hn w hw, mul_zero]

lemma completedIdealClassXi_one_of_sum_eq_zero {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0) :
    completedIdealClassXi σ hn w 1 = 0 := by
  simp only [completedIdealClassXi, idealClassThetaXi_one_of_sum_eq_zero σ hn w hw, mul_zero]

 

theorem entireIdealClassL_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (w : ClassGroup (𝓞 K) → ℂ) (hw : ∑ c, w c = 0)
    {s : ℂ} (hs : 1 < s.re) :
    entireIdealClassL σ hn w s =
      completionExponential (d+1) |(NumberField.discr K : ℝ)| s *
        Complex.Gamma (s/2)^(d+1)*idealClassDirichlet K w s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by intro H; simp [H] at hs
  unfold entireIdealClassL
  rw [dslope_of_ne _ hs1, slope, dslope_of_ne _ hs0,
    dslope_of_ne _ (one_ne_zero : (1:ℂ) ≠ 0), slope, slope]
  rw [completedIdealClassXi_zero_of_sum_eq_zero σ hn w hw,
    completedIdealClassXi_one_of_sum_eq_zero σ hn w hw,
    completedIdealClassXi_eq σ hn w hs]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

 

theorem nonprincipalHeckeL_entire_and_eq {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (entireIdealClassL σ hn χ) ∧
      ∀ s : ℂ, 1 < s.re → entireIdealClassL σ hn χ s =
        completionExponential (d+1) |(NumberField.discr K : ℝ)| s *
          Complex.Gamma (s/2)^(d+1)*idealClassDirichlet K χ s :=
  ⟨entireIdealClassL_entire σ hn χ,
    fun _ hs => entireIdealClassL_eq σ hn χ (finite_group_character_sum_eq_zero χ hχ) hs⟩

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
