import Mathlib
import OAI.Analysis.HardSphere.Geometry.CoordinateLine
import OAI.Analysis.HardSphere.Geometry.SubcubeBase

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
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def pointFin : Point →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ))]

lemma pointFin_apply (x : Point) : pointFin x=![x.1,x.2.1,x.2.2] := by
  ext i
  fin_cases i <;> rfl

lemma pointFin_preserving (b h : ℝ) :
    MeasurePreserving pointFin (volume.restrict (cube (b,(b,b)) h))
      (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc b (b+h)))) := by
  rw [cube_volume]
  let μ := (volume : Measure ℝ).restrict (Icc b (b+h))
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 ↦ μ) 0).symm
  have hq := (MeasurePreserving.id μ).prod (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ μ)).symm
  convert hp.comp hq using 1
  funext x i
  fin_cases i <;> rfl

noncomputable def configurationFin (n : ℕ) : (Fin n → Point) →L[ℝ] (Fin n → Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ pointFin.comp (ContinuousLinearMap.proj i))

lemma configurationFin_apply {n : ℕ} (X : Fin n → Point) (i : Fin n) :
    configurationFin n X i=pointFin (X i) := rfl

lemma configurationFin_single {n : ℕ} (i : Fin n) (q : Fin 3) :
    configurationFin n (Pi.single i (![axis0,axis1,axis2] q))=Pi.single i (Pi.single q 1) := by
  funext k t
  by_cases hk : k=i
  · subst k
    fin_cases q <;> fin_cases t <;> simp [configurationFin_apply,pointFin_apply,axis0,axis1,axis2]
  · simp [configurationFin_apply,hk]

lemma configurationFin_preserving (n : ℕ) (b h : ℝ) :
    MeasurePreserving (configurationFin n)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube (b,(b,b)) h)))
      (Measure.pi (fun _ : Fin n ↦ Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc b (b+h))))) :=
  measurePreserving_pi _ _ (fun _ ↦ pointFin_preserving b h)

lemma sqRadius_eq_sum (x : Point) : sqRadius x=∑ j : Fin 3,(pointFin x j)^2 := by
  simp [sqRadius,pointFin_apply,Fin.sum_univ_succ,add_assoc]

end HardSphere.SphericalCoordinates

namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def cubeParameter (n : ℕ) (L : Length) (X : Fin n → Point) : Configuration n L :=
  project n L (configurationFin n X)

lemma cubeParameter_preserving (n : ℕ) (L : Length) :
    MeasurePreserving (cubeParameter n L)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube 0 L.val))) volume := by
  have hp := measurePreserving_pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc 0 L.val))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
    (f := fun _ x ↦ (x : AddCircle L.val)) (fun _ ↦ by
      simpa only [zero_add,restrict_Ioc_eq_restrict_Icc] using AddCircle.measurePreserving_mk L.val 0)
  have hq := measurePreserving_pi _ _ (fun _ : Fin n ↦ hp)
  have hs := configurationFin_preserving n 0 L.val
  simp only [zero_add] at hs
  exact hq.comp hs

lemma addCircle_dist_coe_sq_le (L : Length) (x y : ℝ) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)^2≤(x-y)^2 := by
  have hn : dist (x : AddCircle L.val) (y : AddCircle L.val)≤|x-y| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  have hh := (sq_le_sq₀ dist_nonneg (abs_nonneg (x-y))).mpr hn
  simpa only [sq_abs] using hh

lemma cubeParameter_distance {n : ℕ} (L : Length) (X : Fin n → Point) (i j : Fin n)
    {a : ℝ} (ha : 0≤a) (hd : sqRadius (X i-X j)≤a^2) :
    torusDistance L (cubeParameter n L X i) (cubeParameter n L X j)≤a := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨ha,le_trans ?_ hd⟩
  rw [sqRadius_eq_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [cubeParameter,project,configurationFin_apply,map_sub,Pi.sub_apply] using
    addCircle_dist_coe_sq_le L (pointFin (X i) q) (pointFin (X j) q)

lemma SmoothTest.cube_zero {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) (ha : 0≤a)
    (X : Fin n → Point) (i j : Fin n) (hij : i≠j) (hd : sqRadius (X i-X j)≤a^2) :
    f.toFun (cubeParameter n L X)=0 := by
  by_contra hz
  have h := f.support_allowed (subset_tsupport _ hz)
  have hdist := cubeParameter_distance L X i j ha hd
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge hdist) (h i j hlt)
  · have hs : torusDistance L (cubeParameter n L X j) (cubeParameter n L X i)=
        torusDistance L (cubeParameter n L X i) (cubeParameter n L X j) := by
      simp only [torusDistance,dist_comm]
    rw [← hs] at hdist
    exact (not_lt_of_ge hdist) (h j i hgt)

lemma SmoothTest.cube_smooth {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) :
    ContDiff ℝ 1 (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) :=
  (f.smooth.of_le (by simp)).comp (configurationFin n).contDiff

lemma SmoothTest.cube_derivative {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) (q : Fin 3) :
    fderiv ℝ (fun X : Fin n → Point ↦ f.toFun (cubeParameter n L X)) X
      (Pi.single i (![axis0,axis1,axis2] q))=
        coordDerivative n L f.toFun (i,q) (cubeParameter n L X) := by
  rw [cubeParameter,coordDerivative_project]
  have h := ((f.smooth.differentiable (by simp) (configurationFin n X)).hasFDerivAt).comp X
    (configurationFin n).hasFDerivAt
  rw [show (fun X ↦ f.toFun (cubeParameter n L X))=
    (fun Y ↦ f.toFun (project n L Y)) ∘ configurationFin n from rfl,h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,configurationFin_single]

lemma SmoothTest.cube_gradient {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (X : Fin n → Point) (i : Fin n) :
    particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X=
      ∑ q : Fin 3, ‖coordDerivative n L f.toFun (i,q) (cubeParameter n L X)‖^2 := by
  have h0 := f.cube_derivative X i 0
  have h1 := f.cube_derivative X i 1
  have h2 := f.cube_derivative X i 2
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis0)=_ at h0
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis1)=_ at h1
  change fderiv ℝ (fun X ↦ f.toFun (cubeParameter n L X)) X (Pi.single i axis2)=_ at h2
  simp only [particleGradSq,h0,h1,h2,Fin.sum_univ_succ,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
    Fin.sum_univ_zero,add_zero]
  ring

lemma smooth_norm_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) :
    ENNReal.ofReal (‖hf.toLp f‖^2)=∫⁻ x,ENNReal.ofReal (‖f x‖^2) ∂μ := by
  have he : ‖hf.toLp f‖^2=∫ x,‖f x‖^2 ∂μ := by
    rw [@norm_sq_eq_re_inner ℂ,L2.inner_def,← integral_re (L2.integrable_inner (hf.toLp f) (hf.toLp f))]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [hx,inner_self_eq_norm_sq_to_K,RCLike.re_ofReal_pow]
  rw [he,ofReal_integral_eq_lintegral_ofReal (hf.integrable_norm_pow (by decide : (2:ℕ)≠0))
    (Filter.Eventually.of_forall (fun x ↦ sq_nonneg ‖f x‖))]

lemma cube_energy_coefficient_nonneg (n : ℕ) {a l : ℝ} (ha : 0≤a) (hl : 0≤l) :
    0≤1/(64*Real.sqrt 3)*a/l^3*(n:ℝ)*((n:ℝ)-1) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : (0:ℝ)≤((n+1:ℕ):ℝ)-1 := by norm_num
    positivity

lemma SmoothTest.cube_gradient_lintegral {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (i : Fin n) :
    (∫⁻ X, ENNReal.ofReal (particleGradSq (fun X ↦ f.toFun (cubeParameter n L X)) i X)
      ∂Measure.pi (fun _ ↦ volume.restrict (cube 0 L.val)))=
        ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2) := by
  simp_rw [f.cube_gradient,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun q _ ↦ by
    exact (((f.continuous_partial (i,q)).measurable.comp (cubeParameter_preserving n L).measurable).norm.pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro q _
  rw [(cubeParameter_preserving n L).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖coordDerivative n L f.toFun (i,q) x‖^2))
    (((f.continuous_partial (i,q)).measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral (f.partial_memLp (i,q))]
  rfl

lemma SmoothTest.energy_lower {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) (ha : 0<a) :
    (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖f.jet.1‖^2≤energy f.jet := by
  have h := smooth_cube_energy f.cube_smooth ha L.property 0 (f.cube_zero ha.le)
  rw [(cubeParameter_preserving n L).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal (‖f.toFun x‖^2))
    ((f.continuous.measurable.norm.pow_const 2).ennreal_ofReal),← smooth_norm_lintegral f.memLp] at h
  simp_rw [f.cube_gradient_lintegral] at h
  rw [← ENNReal.ofReal_mul (cube_energy_coefficient_nonneg n ha.le L.property.le)] at h
  have he : (∑ i : Fin n, ∑ q : Fin 3, ENNReal.ofReal (‖f.jet.2 (i,q)‖^2))=
      ENNReal.ofReal (energy f.jet) := by
    rw [energy,Fintype.sum_prod_type,ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _)).symm
  rw [he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by unfold energy; positivity)).mp h

lemma dirichlet_energy_lower {n : ℕ} {L : Length} {a : ℝ} (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖u.1‖^2≤energy u := by
  have hc : IsClosed {u : Jet n L | (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1))*‖u.1‖^2≤energy u} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_fst.norm.pow 2)
    · exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact f.energy_lower ha) hu

lemma IsGroundVector.energy_lower {n : ℕ} {L : Length} {a : ℝ} {u : Jet n L}
    (hu : IsGroundVector n L a u) (ha : 0<a) :
    1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ)*((n:ℝ)-1)≤energy u := by
  have h := dirichlet_energy_lower ha u hu.1
  simpa only [hu.2.2.1,one_pow,mul_one] using h

lemma IsGroundVector.energy_per_particle_lower {n : ℕ} {L : Length} {a : ℝ} {u : Jet n L}
    (hu : IsGroundVector n L a u) (ha : 0<a) (hn : 2≤n) :
    (1/(128*Real.sqrt 3))*(a*((n:ℝ)/L.val^3))≤energy u/(n:ℝ) := by
  have h := hu.energy_lower ha
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  apply (le_div_iff₀ hnp).mpr
  apply le_trans _ h
  have he : (1/(128*Real.sqrt 3))*(a*((n:ℝ)/L.val^3))*(n:ℝ)=
      (1/(64*Real.sqrt 3)*a/L.val^3*(n:ℝ))*((n:ℝ)/2) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left (by linarith)
  have hl := L.property
  positivity

end HardSphere

end

end OAI
