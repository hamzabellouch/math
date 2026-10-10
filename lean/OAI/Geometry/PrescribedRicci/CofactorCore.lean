import Mathlib
import OAI.Geometry.PrescribedRicci.FiniteCofactor
import OAI.Geometry.PrescribedRicci.FiniteCofactorPatch

namespace OAI

/-! Cofactor Core. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def cofactorComplexCore (p : ι) (B : Bilin (EC d)) (f : Smooth A) : Smooth A :=
  ⟨fun x => D.inverseDet p x * NonlinearHessian.detDifferential
      (fun i j => D.metricEntry p i j x + D.localizedHessian p i j f x) (cofactorMatrix B),
    fun q => by
      apply (D.inverseDet p).smooth q |>.mul
      apply ContDiffOn.clm_apply
      · apply ((NonlinearHessian.determinant_contDiff d).fderiv_right (m:=∞) (by simp)).comp_contDiffOn
        apply contDiffOn_pi.mpr
        intro i
        apply contDiffOn_pi.mpr
        intro j
        exact ((D.metricEntry p i j).smooth q).add ((D.localizedHessian p i j f).smooth q)
      · exact contDiffOn_const⟩

def cofactorScalarCore (p : ι) (B : Bilin (EC d)) (f : Smooth A) : Smooth A :=
  Smooth.realify (D.cofactorComplexCore p B f)

lemma cofactorScalarCore_apply (p : ι) (B : Bilin (EC d)) (f : Smooth A) (x : X) :
    D.cofactorScalarCore p B f x =
      ((D.inverseDet p x * NonlinearHessian.detDifferential
        (fun i j => D.metricEntry p i j x + D.localizedHessian p i j f x) (cofactorMatrix B)).re : ℂ) := by
  exact Smooth.realify_apply _ x

lemma cofactorScalar_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (B : Bilin (EC d)) (f : Smooth A) :
    D.cofactorScalar k hk p B (D.localizers.embed ((k:ℝ)+2) f) =
      D.localizers.embed (k:ℝ) (D.cofactorScalarCore p B f) := by
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    have hh : (Module.finrank ℝ (EC d):ℝ) < (k:ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  apply D.localizers.strong_injective (k:ℝ) hs
  ext x
  rw [D.cofactorScalar_strong,D.localizers.strong_embed _ hs]
  simp_rw [D.completedHessian_embed,D.localizers.strong_embed _ hs]
  exact (D.cofactorScalarCore_apply p B f x).symm

def cofactorLocalCore (p : ι) (i j : BasisIndex d) (f : Smooth A) : 𝓢(EC d,ℂ) :=
  (D.patch p).coefficient i j +
    localize A (D.patch p).index (cutoffGlobal (D.patch p).index (D.cutoff p))
      (cutoffGlobal_support _ _)
      (D.cofactorScalarCore p (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) f -
       D.cofactorScalarCore p (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) 0)

lemma cofactorLocal_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (i j : BasisIndex d) (f : Smooth A) :
    D.cofactorLocal k hk p i j (D.localizers.embed ((k:ℝ)+2) f) =
      schwartzCoord (k:ℝ) (D.cofactorLocalCore p i j f) := by
  rw [cofactorLocal,D.cofactorScalar_embed]
  have h0 := D.cofactorScalar_embed k hk p
    (rankTwo (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j)) 0
  rw [map_zero] at h0
  rw [h0,← map_sub,D.completedLocalize_embed,← schwartzCoord_add]
  rfl

lemma cofactorBCF_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ)) (p : ι) (f : Smooth A) :
    D.cofactorBCF k hk hs p (D.localizers.embed ((k:ℝ)+2) f) =
      coefficientBCF (D.cofactorLocalCore p · · f) := by
  funext i j
  rw [cofactorBCF,D.cofactorLocal_embed,strongEmbedding_schwartz]
  rfl

lemma cofactorScalarCore_zero_source (p : ι) (B : Bilin (EC d)) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.cofactorScalarCore p B 0 x =
      (traceBilin (g.matrix (D.patch p).index (A.chart (D.patch p).index x)) B : ℂ) := by
  let k := Module.finrank ℝ (EC d)+1
  have hk : Module.finrank ℝ (EC d) < k := by omega
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    dsimp [k]
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (EC d))]
  have hh := D.cofactorScalar_zero_source k hk p B hx
  have he := D.cofactorScalar_embed k hk p B 0
  rw [map_zero] at he
  rw [he,D.localizers.strong_embed _ hs] at hh
  exact hh

lemma cofactorLocalCore_source (p : ι) (i j : BasisIndex d) (f : Smooth A) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    extendedCoefficient (D.patch p).matrix (coefficientBCF (D.cofactorLocalCore p · · f)) i j
      (A.euclideanChart (D.patch p).index x) =
      D.cofactorScalarCore p (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
        (stdOrthonormalBasis ℝ (EC d) j)) f x := by
  have hs := D.patch_source p hx
  have hy := (A.euclideanChart (D.patch p).index).mapsTo hs
  have he := (A.euclideanChart (D.patch p).index).left_inv hs
  change (traceBilin (D.patch p).matrix (rankTwo _ _) : ℂ) +
    D.cofactorLocalCore p i j f (A.euclideanChart (D.patch p).index x) = _
  rw [cofactorLocalCore,_root_.add_apply,localize_apply,localizeFun_apply A _ _ hy,he]
  have hc : cutoffGlobal (D.patch p).index (D.cutoff p) x = 1 := by
    change (if x ∈ (A.euclideanChart (D.patch p).index).source then _ else _) = _
    rw [ite_eq_left hs,D.cutoff_one p x hx]
  rw [hc,one_mul]
  change _ + ((D.patch p).coefficient i j (A.euclideanChart (D.patch p).index x) +
    (D.cofactorScalarCore p _ f x-D.cofactorScalarCore p _ 0 x)) = _
  rw [← add_assoc]
  have hp := (D.patch p).equals (A.euclideanChart (D.patch p).index x)
    (D.support_patch p hx).2 i j
  change (traceBilin (D.patch p).matrix (rankTwo _ _) : ℂ) +
    (D.patch p).coefficient i j (A.euclideanChart (D.patch p).index x) = _ at hp
  rw [hp,D.cofactorScalarCore_zero_source p _ hx]
  simp only [ComplexAtlas.euclideanChart_apply,ContinuousLinearEquiv.apply_symm_apply]
  ring

end GluingData
end GlobalElliptic

end
end

end OAI
