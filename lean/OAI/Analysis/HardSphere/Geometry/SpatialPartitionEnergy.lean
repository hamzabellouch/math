import Mathlib
import OAI.Analysis.HardSphere.Geometry.SubcubeBase
import OAI.Analysis.HardSphere.Geometry.RadiusLaw

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
open scoped ENNReal

def spatialPartitionEnergy {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ) (u : Jet n L) : ℝ :=
  ∑ σ : Fin n → Bool, selectedEnergy (fun i ↦ σ i=true)
    ((productPartition n L (spatialInside L A H) (spatialOutside L A H) σ).onJet u)

lemma spatialPartitionEnergy_nonneg {n : ℕ} (L : Length) (A : Finset (Torus L)) (H : ℝ) (u : Jet n L) :
    0≤ spatialPartitionEnergy L A H u := by
  unfold spatialPartitionEnergy selectedEnergy
  exact Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

theorem spatial_spectral_average : ∃ C D : ℝ, 0<C ∧ 0<D ∧
    ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
    (∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw)≤
      ENNReal.ofReal (energy u-energy g*‖u.1‖^2+
        (C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2)) := by
  obtain ⟨K,hK,hloc⟩ := productPartition_spectral_localization
  obtain ⟨D,hD,herr⟩ := spatialEnergyError_configuration_average
  refine ⟨K*Real.exp 3,D,mul_pos hK (Real.exp_pos _),hD,?_⟩
  intro n L r hr hs g hg A hA u hu
  let R : ℝ → ℝ := fun H ↦ ∫ X, (∑ i : Fin n, ‖(spatialInside L A H).orbital (X i)‖^2)*‖u.1 X‖^2
  let E : ℝ → ℝ := fun H ↦ ∫ X, (∑ i : Fin n, spatialEnergyError L A H (X i))*‖u.1 X‖^2
  let c := K*(n:ℝ)*r/L.val^3
  let F : ℝ → ℝ := fun H ↦ energy u-energy g*‖u.1‖^2+c*R H+E H
  obtain ⟨hRi,hRb⟩ := spatialInside_configuration_average L A hA u.1
  obtain ⟨hEi,hEb⟩ := herr n L A hA u.1
  change Integrable R radiusLaw at hRi
  change Integrable E radiusLaw at hEi
  have hFi : Integrable F radiusLaw := ((integrable_const _).add (hRi.const_mul c)).add hEi
  have hpoint (H : ℝ) : spatialPartitionEnergy L A H u≤ F H := by
    have h := hloc n L r hr hs g hg (spatialInside L A H) (spatialOutside L A H)
      (spatialInside_real L A H) (spatialOutside_real L A H) (spatialPartition_unity L A H) u hu
    change spatialPartitionEnergy L A H u-c*R H-E H≤energy u-energy g*‖u.1‖^2 at h
    dsimp [F]
    linarith only [h]
  have hFn (H : ℝ) : 0≤F H := (spatialPartitionEnergy_nonneg L A H u).trans (hpoint H)
  calc
    _ ≤ ∫⁻ H, ENNReal.ofReal (F H) ∂radiusLaw :=
      lintegral_mono (fun H ↦ ENNReal.ofReal_le_ofReal (hpoint H))
    _ = ENNReal.ofReal (∫ H, F H ∂radiusLaw) :=
      (ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hFn)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      change (∫ H, energy u-energy g*‖u.1‖^2+c*R H+E H ∂radiusLaw)≤_
      have hCi : Integrable (fun _ : ℝ ↦ energy u-energy g*‖u.1‖^2) radiusLaw := integrable_const _
      have hCRi : Integrable (fun H ↦ energy u-energy g*‖u.1‖^2+c*R H) radiusLaw := hCi.add (hRi.const_mul c)
      rw [integral_add hCRi hEi,integral_add hCi (hRi.const_mul c),integral_const_mul,integral_const]
      simp only [probReal_univ,one_smul]
      have hc : 0≤c := div_nonneg (mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg _)) hr.le) (pow_nonneg L.property.le _)
      have hRb' := mul_le_mul_of_nonneg_left hRb hc
      change c*(∫ H,R H ∂radiusLaw)≤c*(Real.exp 3*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2)) at hRb'
      change (∫ H,E H ∂radiusLaw)≤D*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2) at hEb
      have he : c*(Real.exp 3*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2))+
          D*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2)=
          (K*Real.exp 3*(n:ℝ)*r/L.val^3+D)*(∫ X,weightedSiteCount L A X*‖u.1 X‖^2) := by dsimp [c]; ring
      linarith only [hRb',hEb,he]

end HardSphere

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def reindexPoint {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    (J → Point) →L[ℝ] (I → Point) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (e i))

lemma reindexPoint_apply {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (X : J → Point) (i : I) : reindexPoint e X i=X (e i) := rfl

lemma reindexPoint_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (j : J) (v : Point) : reindexPoint e (Pi.single j v)=Pi.single (e.symm j) v := by
  funext i
  by_cases hi : i=e.symm j
  · subst i
    simp [reindexPoint_apply]
  · have hj : e i≠j := by
      intro h
      apply hi
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
    simp [reindexPoint_apply,hi,hj]

lemma reindexPoint_preserving {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (μ : I → Measure Point) [∀i,SigmaFinite (μ i)] :
    MeasurePreserving (reindexPoint e) (Measure.pi (fun j ↦ μ (e.symm j))) (Measure.pi μ) := by
  convert measurePreserving_piCongrLeft μ e.symm using 1
  funext X i
  simp [reindexPoint_apply,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

def indexGradSq {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (I → Point) → E) (i : I) (X : I → Point) : ℝ :=
  ‖fderiv ℝ F X (Pi.single i axis0)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis1)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis2)‖^2

lemma indexGradSq_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (e : I ≃ J) (j : J) (X : J → Point) :
    indexGradSq (F ∘ reindexPoint e) j X=indexGradSq F (e.symm j) (reindexPoint e X) := by
  have hd := ((hF.differentiable (by norm_num) (reindexPoint e X)).hasFDerivAt).comp X
    (reindexPoint e).hasFDerivAt
  simp only [indexGradSq,hd.fderiv,ContinuousLinearMap.comp_apply,reindexPoint_single]

lemma continuous_indexGradSq {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (i : I) : Continuous (indexGradSq F i) := by
  have hd := hF.continuous_fderiv (by norm_num)
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma finite_cube_energy {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) ≤
        ∑ i, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
  let e := Fintype.equivFin I
  let T := reindexPoint e
  have h := smooth_cube_energy (hF.comp T.contDiff) hr hl b (F := F ∘ T) ?_
  rotate_left
  · intro X a c hac hd
    apply hz (T X) (e.symm a) (e.symm c) (fun h ↦ hac (e.symm.injective h))
    simpa only [T,reindexPoint_apply,Equiv.apply_symm_apply] using hd
  have hp := reindexPoint_preserving e (fun _ ↦ volume.restrict (cube b l))
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn : (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))=
      ∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)) :=
    hp.lintegral_comp hm
  rw [hn] at h
  have hd (j : Fin (Fintype.card I)) :
      particleGradSq (F ∘ T) j=indexGradSq F (e.symm j) ∘ T := by
    funext X
    exact indexGradSq_reindex hF e j X
  have hg (j : Fin (Fintype.card I)) :
      (∫⁻ X,ENNReal.ofReal (particleGradSq (F ∘ T) j X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))=
      ∫⁻ X,ENNReal.ofReal (indexGradSq F (e.symm j) X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)) := by
    rw [hd]
    exact hp.lintegral_comp (continuous_indexGradSq hF _).measurable.ennreal_ofReal
  simp_rw [hg] at h
  rw [e.symm.sum_comp (fun i ↦ ∫⁻ X,ENNReal.ofReal (indexGradSq F i X)
    ∂Measure.pi (fun _ ↦ volume.restrict (cube b l)))] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
