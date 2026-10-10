import Mathlib
import OAI.Geometry.SmoothYau.NodalMeasure.ExtrusionEquiv
import OAI.Geometry.SmoothYau.Spectrum.StdGaussianMapInnerUnit
import OAI.Geometry.SmoothYau.SphereMetric.UnitCorrelation

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma complex_stdGaussian_eq_map :
    stdGaussian ℂ = (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
      (fun x => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I) := by
  simpa [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Algebra.smul_def]
    using stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI

lemma complex_gaussian_pair :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 : ℂ)+(x.2 : ℂ)*Complex.I)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (stdGaussian ℂ) := by
  have hp := (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).symm
  have hm : MeasurePreserving (fun x : Fin 2 → ℝ => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) (stdGaussian ℂ) :=
    ⟨by fun_prop,complex_stdGaussian_eq_map.symm⟩
  exact hm.comp hp

lemma gaussian_complex_rotation (e : Circle) :
    MeasurePreserving (fun z : ℂ => (e : ℂ)*z) (stdGaussian ℂ) (stdGaussian ℂ) :=
  ⟨(rotation e).continuous.measurable,stdGaussian_map (rotation e)⟩

lemma gaussian_complex_conj :
    MeasurePreserving (starRingEnd ℂ) (stdGaussian ℂ) (stdGaussian ℂ) :=
  ⟨Complex.continuous_conj.measurable,stdGaussian_map Complex.conjLIE⟩

lemma gaussian_complex_pi_rotation {ι : Type*} [Fintype ι] (e : ι → Circle) :
    MeasurePreserving (fun z : ι → ℂ => fun i => (e i : ℂ)*z i)
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) (Measure.pi (fun _ : ι => stdGaussian ℂ)) :=
  measurePreserving_pi _ _ (fun i => gaussian_complex_rotation (e i))

lemma gaussian_complex_from_real_parts {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun x : (ι ⊕ ι) → ℝ =>
      fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I)
      (Measure.pi (fun _ : ι ⊕ ι => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm
  have hc := gaussian_complex_conj.comp complex_gaussian_pair
  have hpi := measurePreserving_pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : ι => stdGaussian ℂ) (fun _ => hc)
  convert hpi.comp (hpair.comp hsplit) using 1
  ext x i
  simp [Function.comp_def,MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.arrowProdEquivProdArrow, Complex.conj_ofReal,sub_eq_add_neg]

def selectedCoefficientOrder : (Fin 3 ⊕ Fin 3) ≃ (Fin 2 ⊕ (Fin 1 ⊕ Fin 3)) where
  toFun := Sum.elim
    (fun i => ![Sum.inr (Sum.inl 0),Sum.inl 0,Sum.inr (Sum.inr 0)] i)
    (fun i => ![Sum.inr (Sum.inr 1),Sum.inr (Sum.inr 2),Sum.inl 1] i)
  invFun := Sum.elim
    (fun i => ![Sum.inl 1,Sum.inr 2] i)
    (Sum.elim (fun _ => Sum.inl 0) (fun i => ![Sum.inl 2,Sum.inr 0,Sum.inr 1] i))
  left_inv := by intro i; rcases i with i|i <;> fin_cases i <;> rfl
  right_inv := by
    intro i; rcases i with i|i
    · fin_cases i <;> rfl
    · rcases i with i|i <;> fin_cases i <;> rfl

def selectedComplexCoefficients (v : (Fin 2 → ℝ) × ((Fin 1 ⊕ Fin 3) → ℝ)) : Fin 3 → ℂ :=
  ![(v.2 (.inl 0) : ℂ)-(v.2 (.inr 1) : ℂ)*Complex.I,
    (v.1 0 : ℂ)-(v.2 (.inr 2) : ℂ)*Complex.I,
    (v.2 (.inr 0) : ℂ)-(v.1 1 : ℂ)*Complex.I]

lemma selectedComplexCoefficients_law :
    MeasurePreserving selectedComplexCoefficients
      ((Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin 1 ⊕ Fin 3 => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin 2 ⊕ (Fin 1 ⊕ Fin 3) => gaussianReal 0 1)
  have hreorder := measurePreserving_piCongrLeft
    (fun _ : Fin 3 ⊕ Fin 3 => gaussianReal 0 1) selectedCoefficientOrder.symm
  have h := gaussian_complex_from_real_parts.comp (hreorder.comp hsplit)
  convert h using 1
  ext v i
  fin_cases i <;> rfl


end

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_opposite_eq (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hρ : |⟪a, b⟫| < 1) (m₁ m₂ : ℝ) :
    (stdGaussian E) {x | (m₁ + ⟪a, x⟫) * (m₂ + ⟪b, x⟫) < 0} =
      gaussianPairOppositeProbability (⟪a, b⟫, m₁, m₂) := by
  let ρ := ⟪a, b⟫
  let s := Real.sqrt (1 - ρ ^ 2)
  let c := s⁻¹ • (b - ρ • a)
  obtain ⟨hc, hac, hbc⟩ := correlated_pair_orthogonal a b ha hb hρ
  change ‖c‖ = 1 at hc
  change ⟪a, c⟫ = 0 at hac
  change b = ρ • a + s • c at hbc
  let S : Set (ℝ × ℝ) := {z | (m₁ + z.1) * (m₂ + ρ * z.1 + s * z.2) < 0}
  have hS : MeasurableSet S :=
    measurableSet_lt (by fun_prop) measurable_const
  let F : E → ℝ × ℝ := fun x => (⟪a, x⟫, ⟪c, x⟫)
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hset : {x | (m₁ + ⟪a, x⟫) * (m₂ + ⟪b, x⟫) < 0} = F ⁻¹' S := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, F, S]
    rw [hbc]
    simp only [inner_add_left, real_inner_smul_left, add_assoc]
  rw [hset, ← Measure.map_apply hF hS]
  change ((stdGaussian E).map (fun x => (⟪a, x⟫, ⟪c, x⟫))) S = _
  rw [stdGaussian_map_orthonormal_pair a c ha hc hac,
    ← (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).map_eq,
    Measure.map_apply (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurable hS]
  rfl

theorem gaussian_wave_opposite_uniform (α β M : ℝ) (hα : -1 < α) (hαβ : α ≤ β)
    (hβ : β < 1) (hM : 0 ≤ M) :
    ∃ q : ℝ, 0 < q ∧ ∀ (a b : E) (m₁ m₂ : ℝ),
      ‖a‖ = 1 → ‖b‖ = 1 → α ≤ ⟪a, b⟫ → ⟪a, b⟫ ≤ β →
      |m₁| ≤ M → |m₂| ≤ M →
      ENNReal.ofReal q ≤ (stdGaussian E)
        {x | (m₁ + ⟪a, x⟫) * (m₂ + ⟪b, x⟫) < 0} := by
  obtain ⟨q, hq, h⟩ := gaussian_opposite_uniform α β M hα hαβ hβ hM
  refine ⟨q, hq, ?_⟩
  intro a b m₁ m₂ ha hb hlo hhi hm₁ hm₂
  rw [stdGaussian_opposite_eq a b ha hb (abs_lt.mpr ⟨hα.trans_le hlo, hhi.trans_lt hβ⟩)]
  exact h (⟪a, b⟫, m₁, m₂) hlo hhi hm₁ hm₂


end


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
variable {I : Type*} [Fintype I]

def complexGaussianRealValue (z : I → ℂ) (γ : I → ℂ) : ℝ :=
  ∑ i, (γ i*z i).re

lemma complexGaussianRealValue_real_parts (z : I → ℂ) (x : (I ⊕ I) → ℝ) :
    complexGaussianRealValue z (fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) =
      ⟪complexValueVector z,WithLp.toLp 2 x⟫ := by
  simp only [complexGaussianRealValue,PiLp.inner_apply,complexValueVector,
    Fintype.sum_sum_type, RCLike.inner_apply]
  simp only [Sum.elim_inl,Sum.elim_inr,starRingEnd_apply,star_trivial]
  simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,
    Complex.I_im,mul_zero,sub_zero,Complex.sub_im,Complex.mul_im,mul_one,
    add_zero,zero_sub,neg_mul,sub_neg_eq_add, Finset.sum_add_distrib]

lemma complex_gaussian_standardized_sign_law (z w : I → ℂ)
    (hz : complexValueVector z ≠ 0) (hw : complexValueVector w ≠ 0)
    (m₁ m₂ : ℝ) (hρ : |unitCorrelation (complexValueVector z) (complexValueVector w)| < 1) :
    (Measure.pi (fun _ : I => stdGaussian ℂ))
      {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0} =
      gaussianPairOppositeProbability (unitCorrelation (complexValueVector z) (complexValueVector w),
        m₁/‖complexValueVector z‖,m₂/‖complexValueVector w‖) := by
  let a := complexValueVector z
  let b := complexValueVector w
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖b‖ := norm_pos_iff.mpr hw
  let S : Set (I → ℂ) :=
    {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    dsimp [complexGaussianRealValue]; fun_prop
  rw [←gaussian_complex_from_real_parts.map_eq,Measure.map_apply
    gaussian_complex_from_real_parts.measurable hS]
  let T : Set (EuclideanSpace ℝ (I ⊕ I)) :=
    {x | (m₁/‖a‖+⟪‖a‖⁻¹ • a,x⟫)*(m₂/‖b‖+⟪‖b‖⁻¹ • b,x⟫) < 0}
  have hset : (fun x : (I ⊕ I) → ℝ => fun i =>
      (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) ⁻¹' S =
        (WithLp.toLp 2) ⁻¹' T := by
    ext x
    simp only [S,T,Set.mem_preimage,Set.mem_ofPred_eq,complexGaussianRealValue_real_parts,
      real_inner_smul_left]
    change (m₁+⟪a,WithLp.toLp 2 x⟫)*(m₂+⟪b,WithLp.toLp 2 x⟫) < 0 ↔ _
    rw [show m₁/‖a‖+‖a‖⁻¹*⟪a,WithLp.toLp 2 x⟫ =
      (m₁+⟪a,WithLp.toLp 2 x⟫)/‖a‖ by ring,
      show m₂/‖b‖+‖b‖⁻¹*⟪b,WithLp.toLp 2 x⟫ =
      (m₂+⟪b,WithLp.toLp 2 x⟫)/‖b‖ by ring,div_mul_div_comm]
    rw [div_lt_iff₀ (mul_pos ha hb),zero_mul]
  change (Measure.pi (fun _ : I ⊕ I => gaussianReal 0 1))
      ((fun x => fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I) ⁻¹' S) = _
  rw [hset,←Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    (show MeasurableSet T by
      apply measurableSet_lt _ measurable_const
      fun_prop),map_pi_eq_stdGaussian]
  exact stdGaussian_opposite_eq _ _ (norm_normalize_vector a hz) (norm_normalize_vector b hw) hρ (m₁/‖a‖) (m₂/‖b‖)

theorem complex_gaussian_sign_uniform (α β M : ℝ) (hα : -1 < α) (hαβ : α ≤ β)
    (hβ : β < 1) (hM : 0 ≤ M) :
    ∃ q > 0, ∀ (I : Type) [Fintype I] (z w : I → ℂ) (m₁ m₂ : ℝ),
      complexValueVector z ≠ 0 → complexValueVector w ≠ 0 →
      α ≤ unitCorrelation (complexValueVector z) (complexValueVector w) →
      unitCorrelation (complexValueVector z) (complexValueVector w) ≤ β →
      |m₁/‖complexValueVector z‖| ≤ M → |m₂/‖complexValueVector w‖| ≤ M →
      ENNReal.ofReal q ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m₁+complexGaussianRealValue z γ)*(m₂+complexGaussianRealValue w γ) < 0} := by
  obtain ⟨q,hq,hprob⟩ := gaussian_opposite_uniform α β M hα hαβ hβ hM
  refine ⟨q,hq,?_⟩
  intro I _ z w m₁ m₂ hz hw hlo hhi hm₁ hm₂
  rw [complex_gaussian_standardized_sign_law z w hz hw m₁ m₂
    (abs_lt.mpr ⟨hα.trans_le hlo,hhi.trans_lt hβ⟩)]
  exact hprob _ hlo hhi hm₁ hm₂


end YauCounterexamples
end

end OAI
