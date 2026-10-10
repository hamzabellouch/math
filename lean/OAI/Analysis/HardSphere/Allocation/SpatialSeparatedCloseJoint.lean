import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.SpatialCloseScale
import OAI.Analysis.HardSphere.Geometry.FinsetEraseRecursion2

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

theorem spatial_separated_close_joint : ∃ C c G : ℝ, 0<C ∧ 0<c ∧ 0<G ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r b D h : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r → 0<b → 0<h →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 → (C+1)*D≤c/b^3*(h/4) →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))), φ.rOut≤1 →
      ((32/spatialCloseScale D b)*φ.rOut)^2≤h/4 →
    ∀ (A : Finset (Torus L)), (∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w) →
      ‖(mollifiedCloseJoint L (spatialCloseScale D b) φ h A).onScalar g.1‖^2≤
        (G/(h*(spatialCloseScale D b)^2)/((D*r)*D))^A.card := by
  obtain ⟨C,c,hC,hc,hform⟩ := spatial_localized_form
  obtain ⟨M,hM,hderiv⟩ := PeriodicCutoff.exists_transition_bound
  let G : ℝ := 8192*M^2
  have hG : 0<G := by dsimp [G]; positivity
  refine ⟨C,c,G,hC,hc,hG,?_⟩
  intro n K _ L hL r b D h hDeq hD hα hr hb hh hs1 hsL hsmall hcoef g hg φ hφ hφe
  let s : ℝ := spatialCloseScale D b
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs : 0<s := spatialCloseScale_pos hDpos hb
  have hs' : s≤1 := by dsimp [s]; linarith only [hs1]
  let q : ℝ := G/(h*s^2)/((D*r)*D)
  have hq : 0≤q := by dsimp [q]; positivity
  have hγ : 0<(D*r)*D := by positivity
  let P : Finset (Torus L) → Prop := fun A ↦ ∀ v∈A, ∀ w∈A, v≠w → 20≤torusDistance L v w
  have hP (A : Finset (Torus L)) (v : Torus L) (hA : P A) : P (A.erase v) := by
    intro x hx y hy hxy
    exact hA x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
  apply finset_erase_recursion_on (fun A ↦ ‖(mollifiedCloseJoint L s φ h A).onScalar g.1‖^2) P hP q hq
  · rw [mollifiedCloseJoint_empty_onScalar,hg.2.2.1]
    norm_num
  · intro A hA _hAnonempty
    let f := mollifiedCloseJoint L s φ h A
    let u := f.onJet g
    have hu : u∈dirichletDomain n L r := f.onJet_mem_domain hg.1
    have hsupport := close_support_integral A hc hb hcoef f g.1
      (mollifiedCloseJoint_nonzero_count L hs hs' hh φ hφe A hA)
    have hformA := hform n K L hL r b D hDeq hD hα hr hb hs1 hsL hsmall g hg A u hu
    have hm := hg.smooth_multiplier_identity f (mollifiedCloseJoint_real L s φ h A)
    have hbnd := SmoothMultiplier.gradient_norm_le A f
      (fun v ↦ mollifiedCloseJoint L s φ h (A.erase v)) (G/(h*s^2))
      (mollifiedCloseJoint_gradient L hs hs1 hh hM.le hderiv φ hφ A hA) g.1
    have hpen : ((D*r)*D)*((A.card:ℝ)*‖f.onScalar g.1‖^2)≤
        (G/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2 := by
      calc
        _ = (D*r)*(D*(A.card:ℝ)*‖f.onScalar g.1‖^2) := by ring
        _ ≤ (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
            c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g.1) X‖^2) :=
          mul_le_mul_of_nonneg_left hsupport (by positivity)
        _ ≤ energy u-energy g*‖u.1‖^2 := hformA
        _ = ∑ p : Direction n, ‖f.derivativeScalar p g.1‖^2 := hm
        _ ≤ _ := hbnd
    have hdiv := (le_div_iff₀ hγ).mpr (by simpa only [mul_comm ((D*r)*D)] using hpen)
    have he : ((G/(h*s^2))*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2)/((D*r)*D)=
        q*∑ v∈A, ‖(mollifiedCloseJoint L s φ h (A.erase v)).onScalar g.1‖^2 := by
      dsimp [q]
      ring
    simpa only [he] using hdiv

end HardSphere

end

end OAI
