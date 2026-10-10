import Mathlib
import OAI.Analysis.HardSphere.Geometry.PartitionErrorIntegral

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

lemma selectedEnergy_add_compl {n : ℕ} {L : Length} (p : Fin n → Prop) [DecidablePred p] (u : Jet n L) :
    selectedEnergy p u+selectedEnergy (fun i ↦ ¬p i) u=energy u := by
  rw [selectedEnergy,selectedEnergy,energy,Fintype.sum_prod_type]
  exact Fintype.sum_subtype_add_sum_subtype p (fun i ↦ ∑ j : Fin 3, ‖u.2 (i,j)‖^2)

lemma complement_removed_card {n : ℕ} (σ : Fin n → Bool) :
    ((n-Fintype.card {i : Fin n // ¬σ i=true} : ℕ):ℝ)=∑ i : Fin n, if σ i then (1:ℝ) else 0 := by
  have hc : Fintype.card {i : Fin n // σ i=true}≤n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun i : {i : Fin n // σ i=true} ↦ i.val) Subtype.val_injective
  rw [Fintype.card_subtype_compl,Fintype.card_fin,Nat.sub_sub_self hc,Fintype.card_subtype]
  symm
  simpa only [Finset.mem_univ,ite_true] using
    (Finset.sum_boole (R:=ℝ) (fun i : Fin n ↦ σ i=true) (Finset.univ : Finset (Fin n)))

theorem productPartition_spectral_localization : ∃ C : ℝ, 0<C ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (a c : SmoothMultiplier 1 L),
      (∀ X, conj (a.toFun X)=a.toFun X) → (∀ X, conj (c.toFun X)=c.toFun X) →
      (∀ x : Torus L, a.orbital x*a.orbital x+c.orbital x*c.orbital x=1) →
    ∀ (u : Jet n L), u∈dirichletDomain n L r →
      (∑ σ : Fin n → Bool, selectedEnergy (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u))
        -C*(n:ℝ)*r/L.val^3*(∫ X, (∑ i : Fin n, ‖a.orbital (X i)‖^2)*‖u.1 X‖^2)
        -(∫ X, (∑ i : Fin n, ∑ j : Fin 3,
          (‖coordDerivative 1 L a.toFun (0,j) (fun _ ↦ X i)‖^2+
           ‖coordDerivative 1 L c.toFun (0,j) (fun _ ↦ X i)‖^2))*‖u.1 X‖^2)
        ≤energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hrem⟩ := selected_ground_removal
  refine ⟨C,hC,?_⟩
  intro n L r hr hs g hg a c ha hc hp u hu
  let K := C*(n:ℝ)*r/L.val^3
  have hσ (σ : Fin n → Bool) :
      selectedEnergy (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u)+
      energy g*‖(productPartition n L a c σ).onScalar u.1‖^2-
      K*((∑ i : Fin n, if σ i then (1:ℝ) else 0)*‖(productPartition n L a c σ).onScalar u.1‖^2)
        ≤energy ((productPartition n L a c σ).onJet u) := by
    have hh := hrem n L r hr hs g hg (fun i ↦ ¬σ i=true)
      ((productPartition n L a c σ).onJet u) ((productPartition n L a c σ).onJet_mem_domain hu)
    rw [complement_removed_card] at hh
    have he := selectedEnergy_add_compl (fun i ↦ σ i=true) ((productPartition n L a c σ).onJet u)
    change (energy g-C*(∑ i : Fin n, if σ i then (1:ℝ) else 0)*(n:ℝ)*r/L.val^3)*
      ‖(productPartition n L a c σ).onScalar u.1‖^2≤_ at hh
    have heq : C*(∑ i : Fin n, if σ i then (1:ℝ) else 0)*(n:ℝ)*r/L.val^3=
        K*(∑ i : Fin n, if σ i then (1:ℝ) else 0) := by dsimp [K]; ring
    rw [heq,sub_mul] at hh
    linarith only [hh,he]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool))) (fun σ _ ↦ hσ σ)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  rw [productPartition_norm_partition a c ha hc hp,productPartition_removal_cost a c ha hc hp,
    productPartition_ims a c ha hc hp] at hsum
  dsimp [K] at hsum
  linarith only [hsum]

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

abbrev SpatialLift := Fin 3 → ℝ

def spatialProject (L : Length) (x : SpatialLift) : Torus L := fun j ↦ (x j : AddCircle L.val)

lemma continuous_spatialProject (L : Length) : Continuous (spatialProject L) :=
  continuous_pi (fun j ↦ (AddCircle.continuous_mk' L.val).comp (continuous_apply j))

lemma spatialProject_sub (L : Length) (x y : SpatialLift) :
    spatialProject L (x-y)=spatialProject L x-spatialProject L y := by
  ext j
  exact QuotientAddGroup.mk_sub (AddSubgroup.zmultiples L.val) (x j) (y j)

lemma lipschitz_spatialProject (L : Length) : LipschitzWith 1 (spatialProject L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0≤dist x y)).mpr
  intro j
  calc
    dist ((x j : ℝ) : AddCircle L.val) ((y j : ℝ) : AddCircle L.val)
      = ‖((x j-y j : ℝ) : AddCircle L.val)‖ := by rw [dist_eq_norm,QuotientAddGroup.mk_sub]
    _ ≤ ‖x j-y j‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ dist x y := by rw [←dist_eq_norm]; exact dist_le_pi_dist x y j

def torusMollify (L : Length) (φ : ContDiffBump (0 : SpatialLift)) (f : Torus L → ℝ) (x : Torus L) : ℝ :=
  ∫ y : SpatialLift, φ.normed volume y*f (x-spatialProject L y)

lemma torusMollify_lift (L : Length) (φ : ContDiffBump (0 : SpatialLift)) (f : Torus L → ℝ) :
    (fun x : SpatialLift ↦ torusMollify L φ f (spatialProject L x))=
      φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun x ↦ f (spatialProject L x)) := by
  funext x
  simp only [torusMollify,convolution,lsmul_apply,smul_eq_mul,spatialProject_sub]

lemma torusMollify_integrable (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) (x : Torus L) :
    Integrable (fun y : SpatialLift ↦ φ.normed volume y*f (x-spatialProject L y)) volume :=
  (φ.continuous_normed.mul (hf.comp (continuous_const.sub (continuous_spatialProject L)))).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

lemma torusMollify_smooth (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun x : SpatialLift ↦ torusMollify L φ f (spatialProject L x)) := by
  rw [torusMollify_lift]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (hf.comp (continuous_spatialProject L)).locallyIntegrable

lemma torusMollify_lipschitz (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (torusMollify L φ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,torusMollify,torusMollify,← integral_sub
    (torusMollify_integrable L φ f hf.continuous x) (torusMollify_integrable L φ f hf.continuous y)]
  calc
    _ ≤ ∫ z : SpatialLift, φ.normed volume z*((C:ℝ)*dist x y) := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall ?_)
      intro z
      rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [←dist_eq_norm,dist_sub_right] using hf.dist_le_mul
        (x-spatialProject L z) (y-spatialProject L z)
    _ = (C:ℝ)*dist x y := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma torusMollify_approximation (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    {f : Torus L → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) (x : Torus L) :
    dist (torusMollify L φ f x) (f x) ≤ (C:ℝ)*φ.rOut := by
  obtain ⟨z,hz⟩ : ∃ z : SpatialLift, spatialProject L z=x := by
    refine ⟨fun j ↦ ((AddCircle.equivIco L.val 0) (x j)).val,?_⟩
    ext j
    exact AddCircle.coe_equivIco
  rw [← hz,show torusMollify L φ f (spatialProject L z)=
    (φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun y ↦ f (spatialProject L y))) z from congrFun (torusMollify_lift L φ f) z]
  apply φ.dist_normed_convolution_le (hf.continuous.comp (continuous_spatialProject L)).aestronglyMeasurable
  intro y hy
  have hh : dist (f (spatialProject L y)) (f (spatialProject L z)) ≤ (C:ℝ)*dist y z := by
    simpa only [mul_one,Function.comp_apply] using (hf.comp (lipschitz_spatialProject L)).dist_le_mul y z
  exact hh.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le C.coe_nonneg)

def mollifiedSpatialMultiplier (L : Length) (φ : ContDiffBump (0 : SpatialLift))
    (f : Torus L → ℝ) (hf : Continuous f) : SmoothMultiplier 1 L :=
  SmoothMultiplier.ofSmooth (fun X ↦ (torusMollify L φ f (X 0) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((torusMollify_smooth L φ f hf).comp (contDiff_apply ℝ SpatialLift 0)))

end HardSphere

end

end OAI
