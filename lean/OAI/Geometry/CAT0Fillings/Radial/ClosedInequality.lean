import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Fillings.Attainment
import OAI.Geometry.CAT0Fillings.Minimizers.SpatialVariation
import OAI.Geometry.CAT0Fillings.Sobolev.Completion
import OAI.Geometry.CAT0Fillings.Calculus.Atlas

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem radial_inequality_of_extremal (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (q : ChartGeometry hT.1) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hm : 0 < mass T)
    (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      c*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    c*p*(mass T)^(p-1)*q.radialVariation o g ≤ q.sweptMass o g := by
  obtain ⟨seg,hends,hseg,hcomp⟩ := hX
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      c*((mass T)^p-(q.spatialMass o g t)^p) ≤ t*q.sweptMass o g := by
    have htg (y : X) : 1-t*g y ∈ Icc (0:ℝ) 1 := by
      have hy := hg0 y
      have hy' := hg1 y
      constructor
      · have hh := mul_le_mul_of_nonneg_left hy' ht.1
        nlinarith [ht.2]
      · exact sub_le_self _ (mul_nonneg ht.1 hy)
    obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
    let B := pushCurrent (fun y => seg o y (1-t*g y)) T
    have hBi : IsIntegral (k+1) B := integral_push hT hf
    have hBz : boundarySucc B = 0 := pushCurrent_cycle hz hf
    have hg' : LipschitzWith (Real.nnabs t*K) (fun y => t*g y) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq,←mul_sub,abs_mul,NNReal.coe_mul,Real.coe_nnabs]
      exact (mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (abs_nonneg t)).trans_eq (mul_assoc _ _ _).symm
    have hg'0 : ∀ y, 0 ≤ t*g y := fun y => mul_nonneg ht.1 (hg0 y)
    have hg'1 : ∀ y, t*g y ≤ 1 := fun y => by
      exact (mul_le_mul_of_nonneg_left (hg1 y) ht.1).trans (by simpa using ht.2)
    obtain ⟨S,hS,hSb,hSm⟩ := exists_swept_current hT hz q seg hseg hcomp
      (fun o y => (hends o y).2) o hg' hg'0 hg'1
    have hNS : IsIntegral (k+2) (0-S) := (isIntegral_zero (X := X) (k+2)).sub hS
    have hbNS : boundarySucc (0-S) = T-B := by
      have hzero : boundarySucc (0 : Functional X (k+2)) = 0 := by
        funext b π; simp [boundarySucc]
      rw [boundarySucc_sub,hzero,hSb]
      dsimp only [B]
      abel
    calc
      c*((mass T)^p-(q.spatialMass o g t)^p) ≤ c*((mass T)^p-(mass B)^p) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply sub_le_sub_left
        exact Real.rpow_le_rpow (mass_nonneg B) (q.spatial_push_mass_le seg hseg hcomp o hg ht htg) hp
      _ ≤ fillingVolume (T-B) := hext B hBi hBz
      _ ≤ mass (0-S) := fillingVolume_le hNS hbNS
      _ = mass S := by simp only [zero_sub,mass_neg]
      _ ≤ q.sweptMass o (fun y => t*g y) := hSm
      _ = t*q.sweptMass o g := q.sweptMass_const_mul o g t
  let F : ℝ → ℝ := fun t => c*((mass T)^p-(q.spatialMass o g t)^p)-t*q.sweptMass o g
  have hF0 : F 0 = 0 := by simp only [F,q.spatialMass_zero,sub_self,mul_zero,zero_mul]
  have hFder : HasDerivWithinAt F
      (c*p*(mass T)^(p-1)*q.radialVariation o g-q.sweptMass o g) (Ici 0) 0 := by
    have hh := (q.spatialMass_first_variation o hg).2.rpow_const (p := p)
      (Or.inl (by rw [q.spatialMass_zero]; exact hm.ne'))
    have hd := (((hasDerivWithinAt_const (0:ℝ) (Ici 0) ((mass T)^p)).sub hh).const_mul c).sub
      ((hasDerivWithinAt_id (0:ℝ) (Ici 0)).mul_const (q.sweptMass o g))
    convert! hd using 1
    rw [q.spatialMass_zero]; ring
  have hlim : Tendsto (slope F 0) (𝓝[>] (0:ℝ))
      (𝓝 (c*p*(mass T)^(p-1)*q.radialVariation o g-q.sweptMass o g)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hFder.Ioi_of_Ici
  have hnonpos : ∀ᶠ t in 𝓝[>] (0:ℝ), slope F 0 t ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with t ht ht1
    rw [slope_def_field,hF0,sub_zero,sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound t ⟨ht.le,ht1.le⟩)) ht.le
  have hh := le_of_tendsto hlim hnonpos
  exact sub_nonpos.mp hh

end CAT0Fillings
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def radialA (o : X) (w : ℕ × Euc (k+1)) : ℝ :=
  (k+1:ℝ)*(1-dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2))
noncomputable def radialB (o : X) (w : ℕ × Euc (k+1)) : Euc (k+1) :=
  dist o (q.atlasParam w) • q.gradient (LipschitzWith.dist_right o) w
omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma radius_bound [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (o x : X) : dist o x ≤ Metric.diam (univ : Set X) :=
  Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)
lemma memLp_radialA (o : X) : MemLp (q.radialA o) 2 q.atlasMeasure := by
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  have hd := (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))).norm
  apply MemLp.of_bound (aestronglyMeasurable_const.mul
    (aestronglyMeasurable_const.sub (hr.mul (Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub (hd.pow 2))))))
    ((k+1:ℝ)*(1+Metric.diam (univ : Set X)))
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  have hs : Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    nlinarith [sq_nonneg ‖q.gradient (LipschitzWith.dist_right o) w‖]
  have hh := mul_le_mul (radius_bound o (q.atlasParam w)) hs (Real.sqrt_nonneg _)
    (Metric.diam_nonneg (s := (univ : Set X)))
  change ‖(k+1:ℝ)*(1-dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2))‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ k+1 by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (abs_sub (1:ℝ) _).trans
  rw [abs_one,abs_of_nonneg (mul_nonneg dist_nonneg (Real.sqrt_nonneg _))]
  linarith

lemma memLp_radialB (o : X) : MemLp (q.radialB o) 2 q.atlasMeasure := by
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  apply MemLp.of_bound (hr.smul (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))))
    (Metric.diam (univ : Set X))
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  change ‖dist o (q.atlasParam w) • q.gradient (LipschitzWith.dist_right o) w‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  exact (mul_le_mul_of_nonneg_left hw dist_nonneg).trans (by simpa using radius_bound o (q.atlasParam w))

noncomputable def radialDefect (o : X) (P : q.Sobolev) : ℝ :=
  inner ℝ ((q.memLp_radialA o).toLp (q.radialA o))
    (Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P)) +
  inner ℝ ((q.memLp_radialB o).toLp (q.radialB o)) (q.closedGradient P)
lemma continuous_radialDefect (o : X) : Continuous (q.radialDefect o) := by
  apply Continuous.add
  · exact continuous_const.inner ((Lp.isometry_compMeasurePreserving q.atlas_preserving).continuous.comp q.inclusion.continuous)
  · exact continuous_const.inner q.closedGradient.continuous

lemma radialDefect_eq_integral (o : X) (P : q.Sobolev) :
    q.radialDefect o P = ∫ w, q.radialA o w*q.inclusion P (q.atlasParam w)+
      inner ℝ (q.radialB o w) (q.closedGradient P w) ∂q.atlasMeasure := by
  unfold radialDefect
  rw [L2.inner_def,L2.inner_def,←integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [(q.memLp_radialA o).coeFn_toLp,(q.memLp_radialB o).coeFn_toLp,
    Lp.coeFn_compMeasurePreserving (q.inclusion P) q.atlas_preserving] with w ha hb hp
  rw [ha,hb,hp,Function.comp_apply]
  simp only [RCLike.inner_apply,conj_trivial,mul_comm]
end CAT0Fillings.ChartGeometry
end

end OAI
