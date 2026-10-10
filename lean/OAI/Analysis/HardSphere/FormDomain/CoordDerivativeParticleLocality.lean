import Mathlib
import OAI.Analysis.HardSphere.Geometry.MollifiedCloseCountMultiplier

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
open scoped Topology

attribute [local irreducible] torusDistance

lemma coordDerivative_zero_of_particle_locality {n : ℕ} (L : Length) (f : Configuration n L→ℂ)
    (hf : Differentiable ℝ (fun x : LiftedConfiguration n ↦ f (project n L x)))
    (v : Torus L) (r : ℝ)
    (hloc : ∀ (X Y : Configuration n L) (k : Fin n), (∀ i, i≠k → X i=Y i) → r≤torusDistance L (X k) v →
      r≤torusDistance L (Y k) v → f X=f Y)
    (p : Direction n) (X : Configuration n L) (hfar : r<torusDistance L (X p.1) v) :
    coordDerivative n L f p X=0 := by
  let w : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 1)
  let Y : ℝ → Configuration n L := fun t ↦ project n L (representative n L X+t • w)
  have hY0 : Y 0=X := by simp only [Y,zero_smul,add_zero,project_representative]
  have hY : Continuous Y := by
    apply (continuous_project n L).comp
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hdcont : Continuous (fun t : ℝ ↦ torusDistance L (Y t p.1) v) :=
    (torusDistance_continuous_pair L).comp (((continuous_apply p.1).comp hY).prodMk continuous_const)
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), r<torusDistance L (Y t p.1) v :=
    hdcont.continuousAt.eventually_const_lt (by simpa only [hY0] using hfar)
  have hrest (t : ℝ) (i : Fin n) (hi : i≠p.1) : X i=Y t i := by
    have he : Y t i=project n L (representative n L X) i := by
      ext j
      simp only [Y,project,Pi.add_apply,Pi.smul_apply,w,Pi.single_eq_of_ne hi,Pi.zero_apply,
        smul_zero,add_zero]
    rw [he,project_representative]
  have heq : (fun t : ℝ ↦ f (Y t))=ᶠ[𝓝 (0:ℝ)] (fun _ ↦ f X) := by
    filter_upwards [hevent] with t ht
    exact (hloc X (Y t) p.1 (hrest t) hfar.le ht.le).symm
  have hz : HasDerivAt (fun t : ℝ ↦ f (Y t)) 0 0 :=
    (hasDerivAt_const 0 (f X)).congr_of_eventuallyEq heq
  have hline := (hasFDerivAt_const (𝕜:=ℝ) (representative n L X) (0:ℝ)).add
    ((hasFDerivAt_id (𝕜:=ℝ) (0:ℝ)).smul_const w)
  have hf0 : HasFDerivAt (fun x : LiftedConfiguration n ↦ f (project n L x))
      (fderiv ℝ (fun x : LiftedConfiguration n ↦ f (project n L x)) (representative n L X))
      (representative n L X+(0:ℝ) • w) := by
    simpa only [zero_smul,add_zero] using (hf (representative n L X)).hasFDerivAt
  have hd := (hf0.comp 0 hline).hasDerivAt
  have he := hd.unique hz
  simpa only [coordDerivative,w,ContinuousLinearMap.comp_apply,add_apply,zero_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul,zero_add] using he

variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseCountMultiplier_partial_zero (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (p : Direction n) (X : Configuration n L) (hfar : 8<torusDistance L (X p.1) v) :
    coordDerivative n L (mollifiedCloseCountMultiplier L s v φ).toFun p X=0 := by
  apply coordDerivative_zero_of_particle_locality L _
    ((mollifiedCloseCountMultiplier L s v φ).smooth.differentiable (by simp)) v 8 _ p X hfar
  intro X Y k hr hx hy
  simp only [mollifiedCloseCountMultiplier_apply,
    mollifiedCloseCount_away_eq L hs hs1 v φ hφ X Y k hr hx hy]

lemma mollifiedCloseCutoff_partial_zero (L : Length) {s : ℝ} (hs : 0<s) (hs1 : 2*s≤1)
    (v : Torus L) (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : φ.rOut≤1)
    (h : ℝ) (p : Direction n) (X : Configuration n L) (hfar : 8<torusDistance L (X p.1) v) :
    coordDerivative n L (mollifiedCloseCutoff L s v φ h).toFun p X=0 := by
  rw [mollifiedCloseCutoff_partial,mollifiedCloseCountMultiplier_partial_zero L hs hs1 v φ hφ p X hfar,mul_zero]

end HardSphere

end

end OAI
