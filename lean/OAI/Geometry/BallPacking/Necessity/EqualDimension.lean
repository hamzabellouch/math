import Mathlib
import OAI.Geometry.BallPacking.Necessity.FiniteReduction

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
local instance equalDimensionCompactNormedAddCommGroup (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance equalDimensionCompactNormedSpace (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 

theorem AffineLineCurve.exists_equal_dimension_reduction {n : ℕ}
    {η : Phase n → Phase n →L[ℝ] Phase n →L[ℝ] ℝ} {J : Phase n → End n}
    (hB : ∀ x, CompatibleWith (η x) (standardJ n))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    ∃ S : ℝ, 0 < S ∧ ∀ R : ℝ, S ≤ R →
      ∃ (F : CompactHolderSpace (Phase n) R → CompactHolderSpace (Phase n) R)
        (pkg : (fderiv ℝ F 0).FredholmPackage)
        (φ : pkg.decDom.X₀ → pkg.decDom.X₁)
        (κ : pkg.decDom.X₀ → pkg.decCodom.X₀),
        Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ ∧
        ContDiffAt ℝ ∞ F 0 ∧ F 0=0 ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0=0 ∧ ContDiffAt ℝ ∞ κ 0 ∧ κ 0=0 ∧
        (∀ᶠ g : CompactHolderSpace (Phase n) R in 𝓝 0,
          (∀ z, crOperator J (fun w => u w+framedMarkedVariation J u R g w) z=0) ↔
            ∃ k : pkg.decDom.X₀, g=(k : CompactHolderSpace (Phase n) R)+
              (φ k : CompactHolderSpace (Phase n) R) ∧ κ k=0) := by
  obtain ⟨S,hS,hM,hSection⟩ := hu.exists_nonlinear_fredholm_section hB hJc hJ hc
  refine ⟨S,hS,?_⟩
  intro R hR
  obtain ⟨F,hF,hF0,hFred,hFe,hDF⟩ := hSection R hR
  obtain ⟨pkg⟩ := hFred.nonempty_fredholmPackage
  obtain ⟨φ,κ,hφ,hφ0,hκ,hκ0,_,hred⟩ := fredholm_local_finite_reduction hF hF0 pkg
  have hdim := normalized_section_package_finrank hB hJc hJ hc hu.1 hu.isProperMap
    (fun z hz => hM z (lt_of_le_of_lt hR hz)) hDF pkg
  refine ⟨F,pkg,φ,κ,hdim,hF,hF0,hφ,hφ0,hκ,hκ0,?_⟩
  filter_upwards [hFe,hred] with g hg hgr
  exact (local_section_zero_iff hB hJc hg).symm.trans hgr

end HigherDimensionalBallPacking.Rigidity

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
local instance actualEqualDimensionCompactNormedAddCommGroup (n : ℕ) (R : ℝ) : NormedAddCommGroup
    (HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R) := inferInstance
local instance actualEqualDimensionCompactNormedSpace (n : ℕ) (R : ℝ) : NormedSpace ℝ
    (HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R) := inferInstance

theorem Compatible.compatibleWith_stdOmega {n : ℕ} {J : End n} (hJ : Compatible J) :
    HigherDimensionalBallPacking.Rigidity.CompatibleWith (stdOmega n) J := by
  simpa only [HigherDimensionalBallPacking.Rigidity.CompatibleWith,stdOmega_apply,Compatible] using hJ

 

theorem actual_affine_line_equal_dimension_reduction {n : ℕ} {J : Phase n → End n}
    (hJ : ContDiff ℝ ∞ J) (hJc : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    ∃ S : ℝ, 0 < S ∧ ∀ R : ℝ, S ≤ R →
      ∃ (F : HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R →
          HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R)
        (pkg : (fderiv ℝ F 0).FredholmPackage)
        (φ : pkg.decDom.X₀ → pkg.decDom.X₁)
        (κ : pkg.decDom.X₀ → pkg.decCodom.X₀),
        Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ ∧
        ContDiffAt ℝ ∞ F 0 ∧ F 0=0 ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0=0 ∧ ContDiffAt ℝ ∞ κ 0 ∧ κ 0=0 ∧
        (∀ᶠ g : HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R in 𝓝 0,
          (∀ z, HigherDimensionalBallPacking.Rigidity.crOperator J
            (fun w => u w+HigherDimensionalBallPacking.Rigidity.framedMarkedVariation J u R g w) z=0) ↔
            ∃ k : pkg.decDom.X₀,
              g=(k : HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R)+
                (φ k : HigherDimensionalBallPacking.Rigidity.CompactHolderSpace (Phase n) R) ∧ κ k=0) := by
  have hu' : HigherDimensionalBallPacking.Rigidity.AffineLineCurve J p q u := hu
  exact hu'.exists_equal_dimension_reduction (η := fun _ => stdOmega n)
    (fun _ => (compatible_standardJ n).compatibleWith_stdOmega)
    (fun x => (hJc x).compatibleWith_stdOmega) hJ hc

end HigherDimensionalBallPacking.Rigidity

end

end OAI
