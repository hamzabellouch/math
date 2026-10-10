import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinHessianFormula

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tailZero_parameterAxis (n : ℕ) (j : Fin (n+1)) :
    TailZero n j (parameterAxis n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [TailZero,Fin.lastCases_last]
    · simp only [TailZero,Fin.lastCases_castSucc,parameterAxis]
      exact ⟨trivial,ih j⟩

theorem hierarchyLevel_rootGradient (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (j : Fin (n+1)) :
    rootGradient n (hierarchyLevel n m f j)=
      hierarchyMomentLevel n m f (rootGradient n f) j := by
  funext z
  exact hierarchyLevel_gradient n m f hf j (parameterAxis n) z (tailZero_parameterAxis n j)

theorem hierarchyPressure_rootHessian_overlap_sum (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      1-∑ j, hierarchyAtom n m 1 j*(∫ z,
        (hierarchyMomentLevel n m f (rootGradient n f) j z)^2 ∂hierarchyPathLaw n m f x) := by
  have hg := rootGradient_continuous n hf
  have hb (z) : ‖rootGradient n f z‖≤1 := (h.bounds z).1
  have hM := hierarchyMomentLevel_bounded_continuous n m f (rootGradient n f) hf hg zero_le_one hb
  have hint (j : Fin (n+1)) : Integrable (fun z => hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z))
      (hierarchyPathLaw n m f x) := by
    apply Integrable.const_mul
    apply hierarchyPathLaw_integrable n m f _ hf ((hM j).1.mul hg) (C:=1)
    intro z
    simpa only [Pi.mul_apply,norm_mul,one_mul] using mul_le_mul ((hM j).2 z) (hb z) (norm_nonneg _) zero_le_one
  have Hpair : rootPair n m f=fun z => ∑ j, hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z) := by
    funext z
    have Hp := fderiv_hierarchyPenalty_apply n m 1 f hf z (parameterAxis n)
    change rootGradient n (hierarchyPenalty n m 1 f) z=
      ∑ j, hierarchyAtom n m 1 j*rootGradient n (hierarchyLevel n m f j) z at Hp
    rw [rootPair,Hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hierarchyLevel_rootGradient n m hf]
    ring
  rw [hierarchyPressure_rootHessian_spin_formula n m hm hmono hf h he x,Hpair,
    integral_finsetSum _ (fun j _ => hint j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,hierarchyPathLaw_prefix_mul n m f (rootGradient n f)
    (rootGradient n f) hf hg hg zero_le_one zero_le_one hb hb j x]
  simp only [pow_two]

end SK.Analytic

end
end

end OAI
