import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPoisson
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.LiteralWeakHessian
import OAI.Geometry.PrescribedRicci.TameApproximation
import OAI.Geometry.PrescribedRicci.FiniteCofactor

namespace OAI

/-! Finite Cofactor Patch. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction ComplexOrder MatrixOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def cofactorLocal (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (i j : BasisIndex d) (u : D.localizers.Sobolev ((k:ℝ)+2)) : L2 (EC d) :=
  schwartzCoord (k:ℝ) ((D.patch p).coefficient i j) +
    D.completedLocalize (k:ℝ) (D.patch p).index (cutoffGlobal (D.patch p).index (D.cutoff p))
      (cutoffGlobal_support _ _)
      (D.cofactorScalar k hk p (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) u -
       D.cofactorScalar k hk p (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) 0)

lemma cofactorLocal_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (i j : BasisIndex d) : Continuous (D.cofactorLocal k hk p i j) := by
  exact continuous_const.add ((D.completedLocalize _ _ _ _).continuous.comp
    ((D.cofactorScalar_continuous k hk p _).sub continuous_const))

lemma cofactorLocal_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (i j : BasisIndex d) :
    D.cofactorLocal k hk p i j 0 = schwartzCoord (k:ℝ) ((D.patch p).coefficient i j) := by
  simp [cofactorLocal]

def cofactorBCF (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) (p : ι)
    (u : D.localizers.Sobolev ((k:ℝ)+2)) : BasisIndex d → BasisIndex d → EC d →ᵇ ℂ :=
  fun i j => strongEmbedding (k:ℝ) hs (D.cofactorLocal k hk p i j u)

lemma cofactorBCF_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) (p : ι) :
    Continuous (D.cofactorBCF k hk hs p) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (strongEmbedding _ hs).continuous.comp (D.cofactorLocal_continuous k hk p i j)

lemma cofactorBCF_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) (p : ι) :
    D.cofactorBCF k hk hs p 0 = coefficientBCF (D.patch p).coefficient := by
  funext i j
  rw [cofactorBCF,D.cofactorLocal_zero,strongEmbedding_schwartz]
  rfl

lemma cofactorBCF_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k)
    (hk₂ : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ))
    (hl₂ : (Module.finrank ℝ (EC d):ℝ) < 2*(l:ℝ)) (p : ι)
    (u : D.localizers.Sobolev ((k:ℝ)+2)) :
    D.cofactorBCF l hl hl₂ p (D.localizers.lower ((k:ℝ)+2) ((l:ℝ)+2) u) =
      D.cofactorBCF k hk hk₂ p u := by
  funext i j
  ext y
  simp only [cofactorBCF,cofactorLocal,map_add,BoundedContinuousFunction.add_apply,
    strongEmbedding_schwartz]
  rw [D.completedLocalize_strong l hl₂,D.completedLocalize_strong k hk₂]
  split_ifs
  · simp only [map_sub,BoundedContinuousFunction.sub_apply]
    rw [D.cofactorScalar_strong_lower k l hk hl hlk]
    have hh := D.cofactorScalar_strong_lower k l hk hl hlk p
      (rankTwo (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j)) 0
      ((A.euclideanChart (D.patch p).index).symm y)
    rw [map_zero] at hh
    rw [hh]
  · rfl

def CofactorSmall (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ))
    (u : D.localizers.Sobolev ((k:ℝ)+2)) : Prop :=
  ∀ p, perturbationBound (stdOrthonormalBasis ℝ (EC d)) (D.cofactorBCF k hk hs p u) *
    ellipticBound (g.matrix (D.patch p).index (coordinateEquiv d (D.patch p).center))
      (g.positive _ _ (by simpa using (D.patch p).mem_target)) < 1

lemma cofactor_small_nhds (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.Sobolev ((k:ℝ)+2)), D.CofactorSmall k hk hs u := by
  apply eventually_all.mpr
  intro p
  have hc := ((continuous_perturbationBound (stdOrthonormalBasis ℝ (EC d))).comp
    (D.cofactorBCF_continuous k hk hs p)).mul_const
      (ellipticBound (g.matrix (D.patch p).index (coordinateEquiv d (D.patch p).center))
        (g.positive _ _ (by simpa using (D.patch p).mem_target)))
  apply hc.continuousAt (gt_mem_nhds ?_)
  simp only [Function.comp_apply]
  rw [D.cofactorBCF_zero]
  exact (D.patch p).small

 

lemma cofactor_small_of_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k)
    (hk₂ : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ))
    (hl₂ : (Module.finrank ℝ (EC d):ℝ) < 2*(l:ℝ))
    (u : D.localizers.Sobolev ((k:ℝ)+2))
    (hu : D.CofactorSmall l hl hl₂ (D.localizers.lower ((k:ℝ)+2) ((l:ℝ)+2) u)) :
    D.CofactorSmall k hk hk₂ u := by
  intro p
  have hh := hu p
  rw [D.cofactorBCF_lower k l hk hl hlk hk₂ hl₂] at hh
  exact hh

end GluingData
end GlobalElliptic

end
end

end OAI
