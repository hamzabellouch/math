import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityDisintegration

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma countableGaussian_prefix_preserving (n : ℕ) :
    MeasurePreserving (fun g=>WithLp.toLp 2 (gaussianCoordinatePrefix n g))
      countableGaussianLaw (stdGaussian (Spin n)) :=
  (show MeasurePreserving (WithLp.toLp 2 : (Fin n→ℝ)→Spin n)
      (Measure.pi fun _=>gaussianReal 0 1) (stdGaussian (Spin n)) from
        ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩).comp
    (gaussianCoordinatePrefix_measurePreserving n)

lemma countableGaussian_prefix_norm (n : ℕ) (g : ℕ→ℝ) :
    ‖WithLp.toLp 2 (gaussianCoordinatePrefix n g)‖^2=∑ i∈Finset.range n,(g i)^2 := by
  simp only [EuclideanSpace.norm_sq_eq,gaussianCoordinatePrefix,Real.norm_eq_abs,sq_abs]
  exact Fin.sum_univ_eq_sum_range (fun i=>(g i)^2) n

def cavitySphereLaw (n L : ℕ) : ProbabilityMeasure (Spin L) := by
  let : IsProbabilityMeasure (unitSphereLaw (n+1+L)) := by
    have he : n+1+L=(n+L)+1 := by omega
    rw [he]
    infer_instance
  exact ⟨(unitSphereLaw (n+1+L)).map (fun u=>Real.sqrt (n+1+L:ℕ) •
    (gaussianBlockSplit (n+1) L u.val).2), inferInstance⟩

def cavityCoupledBlock (n L : ℕ) (p : (ℕ→ℝ)×Spin L) : Spin L :=
  cavityCoupledScale n L p.1 p.2 •p.2

lemma cavityCoupledBlock_measurable (n L : ℕ) : Measurable (cavityCoupledBlock n L) :=
  (cavityCoupledScale_measurable n L).smul measurable_snd

lemma cavitySphereLaw_coupled (n L : ℕ) :
    (cavitySphereLaw n L : Measure (Spin L))=
      (countableGaussianLaw.prod (stdGaussian (Spin L))).map (cavityCoupledBlock n L) := by
  have hp := (countableGaussian_prefix_preserving (n+1)).prod
    (MeasurePreserving.id (stdGaussian (Spin L)))
  have h := congrArg (fun μ : Measure (Spin (n+1)×Spin L)=>
    μ.map (fun p=>Real.sqrt (n+1+L:ℕ) •p.2)) (sphereBlock_gaussian_law n L)
  rw [Measure.map_map (by fun_prop) (show Measurable (fun u : Metric.sphere (0 : Spin (n+1+L)) 1 => gaussianBlockSplit (n+1) L u.val) from (gaussianBlockSplit_measurable (n+1) L).comp measurable_subtype_coe),
    Measure.map_map (by fun_prop) (cavityBlockNormalize_measurable _ _)] at h
  simp only [Function.comp_def] at h
  change (unitSphereLaw (n+1+L)).map _ = _
  rw [h,←hp.map_eq,Measure.map_map (by unfold cavityBlockNormalize; fun_prop) hp.measurable]
  congr 1
  funext p
  simp only [Function.comp_def,cavityBlockNormalize,cavityCoupledBlock,cavityCoupledScale,
    smul_smul,div_eq_mul_inv,Prod.map_fst,Prod.map_snd,id_eq]
  rw [countableGaussian_prefix_norm]

lemma cavityCoupledBlock_tendsto_ae (L : ℕ) :
    ∀ᵐ p ∂countableGaussianLaw.prod (stdGaussian (Spin L)),
      Tendsto (fun n=>cavityCoupledBlock n L p) atTop (𝓝 p.2) := by
  have hf : ∀ᵐ p ∂countableGaussianLaw.prod (stdGaussian (Spin L)),
      Tendsto (fun n : ℕ=>(∑ i∈Finset.range n,(p.1 i)^2)/(n:ℝ)) atTop (𝓝 1) :=
    (measurePreserving_fst (μ:=countableGaussianLaw) (ν:=stdGaussian (Spin L))).quasiMeasurePreserving.ae
      countableGaussian_square_strongLaw
  filter_upwards [hf] with p hp
  simpa only [one_smul,cavityCoupledBlock] using (cavityCoupledScale_tendsto L p.1 p.2 hp).smul
    (tendsto_const_nhds (x:=p.2))

def cavityGaussianLaw (L : ℕ) : ProbabilityMeasure (Spin L) := ⟨stdGaussian (Spin L),inferInstance⟩

theorem cavitySphereLaw_tendsto (L : ℕ) :
    Tendsto (fun n=>cavitySphereLaw n L) atTop (𝓝 (cavityGaussianLaw L)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have he n : (∫ z,F z ∂(cavitySphereLaw n L : Measure (Spin L)))=
      ∫ p,F (cavityCoupledBlock n L p) ∂countableGaussianLaw.prod (stdGaussian (Spin L)) := by
    rw [cavitySphereLaw_coupled,integral_map (cavityCoupledBlock_measurable n L).aemeasurable F.continuous.aestronglyMeasurable]
  have he0 : (∫ z,F z ∂(cavityGaussianLaw L : Measure (Spin L)))=
      ∫ p : (ℕ→ℝ)×Spin L,F p.2 ∂countableGaussianLaw.prod (stdGaussian (Spin L)) := by
    symm
    rw [←integral_map measurable_snd.aemeasurable F.continuous.aestronglyMeasurable,
      Measure.map_snd_prod,measure_univ,one_smul]
    rfl
  simp_rw [he,he0]
  apply tendsto_integral_of_dominated_convergence (fun _=>‖F‖)
    (fun n=>(F.measurable.comp (cavityCoupledBlock_measurable n L)).aestronglyMeasurable)
    (integrable_const ‖F‖)
  · intro n
    exact ae_of_all _ fun p=>F.norm_coe_le_norm _
  · filter_upwards [cavityCoupledBlock_tendsto_ae L] with p hp
    exact F.continuous.continuousAt.tendsto.comp hp

def cavityShell (L : ℕ) : Set (Spin L) := {z | (L:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤L+1}

lemma cavityShell_measurable (L : ℕ) : MeasurableSet (cavityShell L) := by
  exact (isClosed_Icc.preimage (show Continuous (fun z : Spin L=>‖z‖^2) from continuous_norm.pow 2)).measurableSet

lemma stdGaussian_sphere_null (k : ℕ) (r : ℝ) :
    stdGaussian (Spin (k+1)) (Metric.sphere 0 r)=0 := by
  rw [←canonicalRadialMass_eq_stdGaussian]
  exact withDensity_absolutelyContinuous _ _ (Measure.addHaar_sphere volume 0 r)

lemma cavityShell_frontier_null (k : ℕ) :
    stdGaussian (Spin (k+1)) (frontier (cavityShell (k+1)))=0 := by
  have hs : frontier (cavityShell (k+1)) ⊆
      Metric.sphere 0 (Real.sqrt (k+1:ℕ)) ∪ Metric.sphere 0 (Real.sqrt ((k+1:ℕ)+1)) := by
    intro z hz
    have h := (continuous_norm.pow 2).frontier_preimage_subset (Icc ((k+1:ℕ):ℝ) ((k+1:ℕ)+1)) hz
    rw [frontier_Icc (by linarith)] at h
    simp only [mem_preimage,mem_insert_iff,mem_singleton_iff,Pi.pow_apply] at h
    rcases h with h|h
    · left
      simp only [Metric.mem_sphere,dist_zero_right,←h,Real.sqrt_sq (norm_nonneg z)]
    · right
      simp only [Metric.mem_sphere,dist_zero_right,←h,Real.sqrt_sq (norm_nonneg z)]
  apply measure_mono_null hs
  rw [measure_union_null (stdGaussian_sphere_null k _) (stdGaussian_sphere_null k _)]

lemma stdGaussian_open_pos (k : ℕ) {U : Set (Spin (k+1))} (ho : IsOpen U) (hn : U.Nonempty) :
    0<stdGaussian (Spin (k+1)) U := by
  have ha : (volume : Measure (Spin (k+1))) ≪ stdGaussian (Spin (k+1)) := by
    rw [←canonicalRadialMass_eq_stdGaussian]
    apply withDensity_absolutelyContinuous' (canonicalRadialDensity_continuous k 1).measurable.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x=>ne_of_gt (ENNReal.ofReal_pos.mpr (canonicalRadialDensity_pos k 1 x))
  exact pos_iff_ne_zero.mpr (fun h=>ne_of_gt (ho.measure_pos volume hn) (ha h))

def cavityShellMass (k : ℕ) : ℝ := (stdGaussian (Spin (k+1))).real (cavityShell (k+1))

lemma cavityShellMass_pos (k : ℕ) : 0<cavityShellMass k := by
  have hu : ({z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} : Set (Spin (k+1))).Nonempty := by
    let z : Spin (k+1) := EuclideanSpace.single 0 (Real.sqrt ((k+1:ℕ)+(1/2:ℝ)))
    have hz : ‖z‖^2=(k+1:ℕ)+(1/2:ℝ) := by
      simp only [z,PiLp.norm_single,Real.norm_eq_abs,sq_abs]
      exact Real.sq_sqrt (by positivity)
    exact ⟨z,by change (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1; rw [hz]; constructor <;> linarith⟩
  have ho : IsOpen {z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} :=
    (isOpen_lt continuous_const (continuous_norm.pow 2)).inter (isOpen_lt (continuous_norm.pow 2) continuous_const)
  have hp := (stdGaussian_open_pos k ho hu).trans_le (measure_mono (show
    {z : Spin (k+1) | (k+1:ℕ)<‖z‖^2 ∧ ‖z‖^2<(k+1:ℕ)+1} ⊆ cavityShell (k+1) from fun z hz=>⟨hz.1.le,hz.2.le⟩))
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

lemma cavityShellMass_le_one (k : ℕ) : cavityShellMass k≤1 := by
  exact measureReal_le_one

lemma cavitySphereLaw_shell_tendsto (k : ℕ) :
    Tendsto (fun n=>(cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1))) atTop (𝓝 (cavityShellMass k)) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (cavitySphereLaw_tendsto (k+1)) (cavityShell_frontier_null k))

lemma cavitySphereLaw_shell_log_tendsto (k : ℕ) :
    Tendsto (fun n=>Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))) atTop (𝓝 (Real.log (cavityShellMass k))) :=
  (cavitySphereLaw_shell_tendsto k).log (cavityShellMass_pos k).ne'

end SphericalPerceptronFreeEnergy
end

end OAI
