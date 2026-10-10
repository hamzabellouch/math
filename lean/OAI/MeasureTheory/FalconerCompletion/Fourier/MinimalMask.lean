import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.EndpointMask
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarKernelRegionPartition
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid
import OAI.MeasureTheory.FalconerCompletion.Recursion.ExistsFarSeparationPower2

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal
variable {d n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState d)

noncomputable def minimalMask (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ b ∈ policyDescriptorList (adjustedProfile (d := d) e.mass e.N) e.N e.q e.a e.t,
    actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b z.1 (radialVector z.1 z.2) *
    actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J e.i b z.2 (radialVector z.1 z.2)

lemma measurable_minimalMask : Measurable e.minimalMask := by
  apply Finset.measurable_prod
  intro b hb
  exact ((actualEndpointMask_measurable _ _ _ _ _ _ _ _).comp
    (measurable_fst.prodMk measurable_radialVector)).mul
    ((actualEndpointMask_measurable _ _ _ _ _ _ _ _).comp
      (measurable_snd.prodMk measurable_radialVector))

lemma minimalMask_bounds (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    0≤e.minimalMask z ∧ e.minimalMask z≤1 := by
  have hr : ‖radialVector z.1 z.2‖≤1 := by
    by_cases hz : z.1=z.2
    · simp [radialVector,hz]
    · exact (norm_radialVector hz).le
  have hn (b : PolicyDescriptor) := actualEndpointMask_bounds e.ρ e.mass e.N e.sig e.C e.J e.i b
  constructor
  · exact Finset.prod_nonneg (fun b _ => mul_nonneg (hn b z.1 hr).1 (hn b z.2 hr).1)
  · exact Finset.prod_le_one₀ (fun b _ => mul_nonneg (hn b z.1 hr).1 (hn b z.2 hr).1)
      (fun b _ => (mul_le_of_le_one_left (hn b z.2 hr).1 (hn b z.1 hr).2).trans
        (hn b z.2 hr).2)

lemma minimalMask_eq_one {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)}
    (hx : z.1∈treeCell e.X) (hy : z.2∈treeCell e.Y) (hg : z∈e.good) :
    e.minimalMask z=1 := by
  have hc (x : EuclideanSpace ℝ (Fin d)) (P : CellPath d) (hx : x∈treeCell P) (b : PolicyDescriptor) :
      ∃ Q∈dyadicPaths (descriptorAnchor b), x∈treeCell Q := by
    have hr : x∈treeCell [] := by simpa only [List.take_zero] using treeCell_subset_take P 0 hx
    rw [← treeCell_cover_root (descriptorAnchor b)] at hr
    obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hr
    exact ⟨Q,hQ,hxQ⟩
  apply Finset.prod_eq_one
  intro b hb
  rw [actualEndpointMask_one _ _ _ _ _ _ _ _ (hc _ _ hx b) ((hg b hb).1),
    actualEndpointMask_one _ _ _ _ _ _ _ _ (hc _ _ hy b) ((hg b hb).2),mul_one]

noncomputable def spatialWeight (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (dist z.1 z.2*(2:ℝ)^e.a)^(-((d:ℝ)-1)/2)*e.minimalMask z

lemma measurable_spatialWeight : Measurable e.spatialWeight := by
  exact (((continuous_fst.dist continuous_snd).measurable.mul_const _).pow_const _).mul
    e.measurable_minimalMask

lemma spatialWeight_nonneg (z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    0≤e.spatialWeight z := mul_nonneg (Real.rpow_nonneg (mul_nonneg dist_nonneg (by positivity)) _)
      (e.minimalMask_bounds z).1

lemma ae_cellPair_mem [SFinite e.ρ] : ∀ᵐ z ∂e.cellPair, z.1∈treeCell e.X ∧ z.2∈treeCell e.Y :=
  (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (measurableSet_treeCell e.X))).and
    (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (measurableSet_treeCell e.Y)))

noncomputable def weightedPair : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  e.cellPair.withDensity (fun z => ENNReal.ofReal (e.levelMass^(-2:ℤ)*e.spatialWeight z))
noncomputable def weightedDistance : Measure ℝ := Measure.map (fun z => dist z.1 z.2) e.weightedPair

lemma weightedDistance_fourier (r : ℝ) :
    charFun e.weightedDistance r = (e.levelMass^(-2:ℤ):ℝ) •
      ∫ z, (e.spatialWeight z:ℂ)*Complex.exp ((r*dist z.1 z.2:ℝ)*Complex.I) ∂e.cellPair := by
  rw [charFun_apply_real,weightedDistance,integral_map (by fun_prop) (by fun_prop)]
  have hw : Measurable (fun z => ENNReal.ofReal (e.levelMass^(-2:ℤ)*e.spatialWeight z)) :=
    (measurable_const.mul e.measurable_spatialWeight).ennreal_ofReal
  rw [weightedPair,integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (e.spatialWeight_nonneg z))]
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring

end PositiveDistanceState
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma separated_distance_ratio {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)))
    {z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))}
    (hx : z.1∈treeCell e.X) (hy : z.2∈treeCell e.Y) :
    1≤dist z.1 z.2*(2:ℝ)^e.a ∧ dist z.1 z.2*(2:ℝ)^e.a≤8*K := by
  have hx' : z.1∈Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.X j:ℤ)) := by
    change z.1∈Attempt4FullFar.ambientGridCell e.X.length (fun j => (pathIndex e.X j:ℤ)) at hx
    rwa [hX] at hx
  have hy' : z.2∈Attempt4FullFar.ambientGridCell e.a (fun j => (pathIndex e.Y j:ℤ)) := by
    change z.2∈Attempt4FullFar.ambientGridCell e.Y.length (fun j => (pathIndex e.Y j:ℤ)) at hy
    rwa [hY] at hy
  have hK' : 32*((↑(n+1):ℝ)+1)≤K := by push_cast; linarith
  have hh := farSeparatedGridND_all_lengths hK' hs hx' hy'
  have hp : 0<(2:ℝ)^e.a := by positivity
  have hlo : K/16≤dist z.1 z.2*(2:ℝ)^e.a :=
    (div_le_iff₀ hp).mp (by simpa only [div_div] using hh.1)
  exact ⟨by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith,
    (le_div_iff₀ hp).mp hh.2⟩

lemma spatialWeight_bounds [SFinite e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    ∀ᵐ z ∂e.cellPair, (0≤e.spatialWeight z ∧ e.spatialWeight z≤1) ∧
      (z∈e.good → (8*K)^(-(n:ℝ)/2)≤e.spatialWeight z) := by
  filter_upwards [e.ae_cellPair_mem] with z hz
  have hr := e.separated_distance_ratio hK hX hY hs hz.1 hz.2
  have hn : -((↑(n+1):ℝ)-1)/2=-(n:ℝ)/2 := by push_cast; ring
  have hnonpos : -(n:ℝ)/2≤0 := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  refine ⟨⟨e.spatialWeight_nonneg z,?_⟩,?_⟩
  · unfold spatialWeight
    rw [hn]
    exact (mul_le_of_le_one_left (e.minimalMask_bounds z).1
      (Real.rpow_le_one_of_one_le_of_nonpos hr.1 hnonpos)).trans (e.minimalMask_bounds z).2
  · intro hg
    rw [spatialWeight,e.minimalMask_eq_one hz.1 hz.2 hg,hn,mul_one]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hr.1) hr.2 hnonpos

lemma weightedPair_le [SFinite e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    e.weightedPair≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) • e.cellPair := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [e.spatialWeight_bounds hK hX hY hs] with z hz
  exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity) hz.1.2)

lemma weightedPair_isFinite [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    IsFiniteMeasure e.weightedPair := by
  constructor
  apply (Measure.le_iff.mp (e.weightedPair_le hK hX hY hs) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

lemma weightedDistance_isFinite [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    IsFiniteMeasure e.weightedDistance := by
  let := e.weightedPair_isFinite hK hX hY hs
  unfold weightedDistance
  infer_instance

lemma weightedPair_lower [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    ENNReal.ofReal (e.levelMass^(-2:ℤ)*(8*K)^(-(n:ℝ)/2)) • e.pair≤e.weightedPair := by
  rw [pair,← withDensity_const,← withDensity_indicator e.measurable_good]
  apply withDensity_mono
  filter_upwards [e.spatialWeight_bounds hK hX hY hs] with z hz
  by_cases hg : z∈e.good
  · rw [Set.indicator_of_mem hg]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hz.2 hg) (by positivity))
  · rw [Set.indicator_of_notMem hg]
    exact zero_le

lemma weightedDistance_lower [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    ENNReal.ofReal (e.levelMass^(-2:ℤ)*(8*K)^(-(n:ℝ)/2)) • e.distance≤e.weightedDistance := by
  have hh := Measure.map_mono (e.weightedPair_lower hK hX hY hs)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_smul _ (continuous_fst.dist continuous_snd).measurable.aemeasurable] at hh
  simpa only [distance,weightedDistance] using hh

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace PlanarFalconer
open Set MeasureTheory

lemma finite_measure_distance_collision_fourier_wide : ∃ C : ℝ, 0<C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (A L : ℝ), 0<A → 1≤L →
      A*(μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2|≤100*L/A} ≤
        (L*C)*∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  obtain ⟨C,hC,hfourier⟩ := finite_measure_distance_collision_fourier
  refine ⟨C,hC,?_⟩
  intro μ hμ A L hA hL
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hsmall := hfourier μ (A/L) (div_pos hA hLp)
  have he : 100/(A/L)=100*L/A := by field_simp
  rw [he] at hsmall
  have hAL : A/L≤A := div_le_self hA.le hL
  have hicc : Icc (-(A/L)) (A/L)⊆Icc (-A) A := fun _ hx => ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hip : Integrable (fun r => ‖charFun μ r‖^2) (volume.restrict (Icc (-A) A)) := by
    simpa only [one_mul] using charFun_sq_integrable_finite μ (volume.restrict (Icc (-A) A)) 1
  have hinc := integral_mono_measure (Measure.restrict_mono hicc le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hip
  calc
    _ = L*((A/L)*(μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2|≤100*L/A}) := by field_simp
    _ ≤ L*(C*∫ r in Icc (-(A/L)) (A/L), ‖charFun μ r‖^2) := mul_le_mul_of_nonneg_left hsmall hLp.le
    _ ≤ L*(C*∫ r in Icc (-A) A, ‖charFun μ r‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinc hC.le) hLp.le
    _ = _ := by ring
end PlanarFalconer
end GraphLiteralSupport
end
end

end OAI
