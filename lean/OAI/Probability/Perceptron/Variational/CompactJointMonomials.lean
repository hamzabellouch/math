import Mathlib
import OAI.Probability.Perceptron.Interpolation.GibbsOverlapArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def compactJointMonomial (p d : ℕ) : CompactJointOverlap →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x : CompactJointOverlap => (x.2:ℝ)^d*(x.1:ℝ)^p,by fun_prop⟩

@[simp] lemma compactJointMonomial_apply (p d : ℕ) (x : CompactJointOverlap) :
    compactJointMonomial p d x = (x.2:ℝ)^d*(x.1:ℝ)^p := rfl

lemma compactJointMonomial_zero : compactJointMonomial 0 0 = 1 := by ext x; simp

lemma compactJointMonomial_add (p d p' d' : ℕ) :
    compactJointMonomial (p+p') (d+d') = compactJointMonomial p d * compactJointMonomial p' d' := by
  ext x
  simp only [compactJointMonomial_apply,BoundedContinuousFunction.mul_apply,pow_add]
  ring

lemma compactJointMonomial_separates (x y : CompactJointOverlap) (h : x≠y) :
    ∃ p d, compactJointMonomial p d x ≠ compactJointMonomial p d y := by
  by_contra hn
  push Not at hn
  apply h
  apply Prod.ext <;> apply Subtype.ext
  · simpa using hn 1 0
  · simpa using hn 0 1

lemma compactJointMonomial_abs_le (p d : ℕ) (x : CompactJointOverlap) :
    |compactJointMonomial p d x|≤1 := by
  rw [compactJointMonomial_apply,abs_mul,abs_pow,abs_pow,abs_of_nonneg x.2.property.1]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ x.2.property.1 x.2.property.2)).trans
    (pow_le_one₀ (abs_nonneg _) (abs_le.mpr x.1.property))

lemma compactJoint_monomials_determine (P Q : Measure CompactJointOverlap)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ p d, (∫ x, compactJointMonomial p d x ∂P) = ∫ x, compactJointMonomial p d x ∂Q) : P=Q := by
  apply measure_eq_of_additive_test_family (fun a : ℕ×ℕ => compactJointMonomial a.1 a.2)
    compactJointMonomial_zero (fun a b => compactJointMonomial_add _ _ _ _)
  · intro x y hxy
    obtain ⟨p,d,hpd⟩ := compactJointMonomial_separates x y hxy
    exact ⟨(p,d),hpd⟩
  · exact fun a => h a.1 a.2

lemma sourceJointOverlap_symm {N k : ℕ} (x y : NormalizedSpin N×IndexedLeaf k) :
    sourceJointOverlap x y = sourceJointOverlap y x := by
  apply Prod.ext <;> apply Subtype.ext
  · exact real_inner_comm _ _
  · simp only [sourceJointOverlap,indexedCommonDepth_comm k y.2 x.2]

lemma sourceGibbsArray_eq (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (z : Fin k → ℝ) (t : ℝ≥0) :
    sourceGibbsArrayLaw n k f p d h u z t =
      gibbsOverlapArrayLaw (sourceFullSpinLeafKernel n k)
        ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
        (sourceCouplingHamiltonian n k f p d h u)
        (sourceCouplingHamiltonian_measurable n k f p d h u)
        sourceJointOverlap (sourceJointOverlap_measurable (n+1) k) := rfl

lemma source_compact_gg_defect (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0≤h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0)
    (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    compactGGDefect (sourceGibbsArrayLaw n k f p d h u z t) r i G (compactJointMonomial (p j) (d j)) =
      -kernelGGDefect (sourceFullSpinLeafKernel n k)
        ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
        (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
        (((k:ℝ)/(k+1:ℕ))^(d j)) r i
        (fun x => G (fun a b => sourceJointOverlap (x a) (x b))) := by
  rw [sourceGibbsArray_eq]
  have he := sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t
  have hexp : ∀ᵐ a ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw,
      Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
        (sourceFullSpinLeafKernel n k a) := by
    filter_upwards [he] with a ha
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  apply compactGGDefect_gibbsOverlapArray _ _ _ _ _ _ hexp r i G (compactJointMonomial (p j) (d j))
  · exact sourceJointMonomial_diagonal p d j
  · intro x y
    rw [sourceJointOverlap_symm x y]

end SphericalPerceptronFreeEnergy

end

end OAI
