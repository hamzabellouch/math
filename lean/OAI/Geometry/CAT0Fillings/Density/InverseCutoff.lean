import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.MeasurableBound
import OAI.Geometry.CAT0Fillings.Swept.Current

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

noncomputable def inverseSquareCutoff (ε r : ℝ) : ℝ := ε^2/(max ε r)^2

lemma inverseSquareCutoff_nonneg {ε : ℝ} (r : ℝ) : 0 ≤ inverseSquareCutoff ε r :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma inverseSquareCutoff_le_one {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    inverseSquareCutoff ε r ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (hε.trans_le (le_max_left ..)))).mpr
  exact sq_le_sq₀ hε.le (hε.le.trans (le_max_left ..)) |>.mpr (le_max_left ..)

lemma inverseSquareCutoff_eq_one {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ ε) :
    inverseSquareCutoff ε r = 1 := by
  simp only [inverseSquareCutoff,max_eq_left hr]
  exact div_self (pow_ne_zero _ hε.ne')

lemma hasDerivAt_inverse_square {ε r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => ε^2/t^2) (-2*ε^2/r^3) r := by
  have h := (hasDerivAt_const r (ε^2)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero _ hr)
  have hh : ((0:ℝ)*r^2-ε^2*(2*r^(2-1)*1))/(r^2)^2 = -2*ε^2/r^3 := by
    field_simp
    ring
  norm_num only [Pi.div_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat] at h
  rw [hh] at h
  exact h

lemma inverseSquareCutoff_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2/ε)) (inverseSquareCutoff ε) := by
  have hd : LipschitzOnWith (Real.toNNReal (2/ε)) (fun r : ℝ => ε^2/r^2) (Ici ε) := by
    apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (hasDerivAt_inverse_square (hε.trans_le hr).ne').hasDerivWithinAt)
    intro r hr
    have hr0 : 0 < r := hε.trans_le hr
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm,Real.norm_eq_abs,Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2/ε),
      abs_div,abs_mul,abs_of_nonneg (sq_nonneg ε),abs_pow,abs_of_pos hr0]
    norm_num
    apply (div_le_div_iff₀ (pow_pos hr0 _) hε).mpr
    have hh : ε^3 ≤ r^3 := pow_le_pow_left₀ hε.le hr 3
    nlinarith
  have hm : LipschitzWith 1 (fun r : ℝ => max ε r) := by
    simpa using (LipschitzWith.const ε).max (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  apply LipschitzWith.of_dist_le_mul
  intro r s
  exact (hd.dist_le_mul _ (show ε ≤ max ε r from le_max_left _ _) _ (show ε ≤ max ε s from le_max_left _ _)).trans
    (by simpa only [NNReal.coe_one,one_mul] using
      mul_le_mul_of_nonneg_left (hm.dist_le_mul r s) (NNReal.coe_nonneg _))

lemma hasDerivAt_inverseSquareCutoff_lt {ε r : ℝ} (hε : 0 < ε) (hr : r < ε) :
    HasDerivAt (inverseSquareCutoff ε) 0 r := by
  apply (hasDerivAt_const r (1:ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hr] with s hs
  exact inverseSquareCutoff_eq_one hε hs.le

lemma hasDerivAt_inverseSquareCutoff_gt {ε r : ℝ} (hε : 0 < ε) (hr : ε < r) :
    HasDerivAt (inverseSquareCutoff ε) (-2*ε^2/r^3) r := by
  apply (hasDerivAt_inverse_square (hε.trans hr).ne').congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with s hs
  simp only [inverseSquareCutoff,max_eq_right hs.le]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma fderivWithin_scalar_comp {f : X → ℝ} {ψ : ℝ → ℝ} {a : ℝ}
    {z : Euc k} (hz : z ∈ C.domain) (hu : UniqueDiffWithinAt ℝ C.domain z)
    (hf : DifferentiableWithinAt ℝ (C.scalar f) C.domain z)
    (hψ : HasDerivAt ψ a (C.scalar f z)) :
    fderivWithin ℝ (C.scalar (ψ ∘ f)) C.domain z =
      a • fderivWithin ℝ (C.scalar f) C.domain z := by
  apply HasFDerivWithinAt.fderivWithin _ hu
  apply (hψ.comp_hasFDerivWithinAt z hf.hasFDerivWithinAt).congr
  · intro x hx
    simp only [C.scalar_eq hx,Function.comp_apply]
  · simp only [C.scalar_eq hz,Function.comp_apply]
end IntegerChart

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma weighted_density_integrable_borel (i : ℕ) {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    Integrable (fun z => q.density i z*w ((q.chart i).paramExtended z))
      (volume.restrict (q.chart i).domain) :=
  integrable_weighted_comp _ (q.chart i).measurable_paramExtended (q.density_integrable i) hw hb

lemma integral_massMeasure_borel {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    (∫ x, w x ∂MassMeasure.currentMassMeasure hT) = ∑' i, ∫ z,
      q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain := by
  have hi : Integrable w (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨B,hB⟩ := hb
    exact Integrable.of_bound hw.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  rw [q.measure_eq] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
    (q.density_integrable i)
    (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw

lemma weighted_density_summable_borel {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    Summable (fun i => ∫ z, q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) := by
  have hi : Integrable w (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨B,hB⟩ := hb
    exact Integrable.of_bound hw.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  rw [q.measure_eq] at hi
  apply (hasSum_integral_measure hi).summable.congr
  intro i
  exact integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
    (q.density_integrable i)
    (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw

noncomputable def radialNormSq (o : X) (i : ℕ) (z : Euc k) : ℝ :=
  let α := differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z)
  α ⬝ᵥ (q.gram i z)⁻¹.mulVec α

lemma ae_radialNormSq_bounds (o : X) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.radialNormSq o i z ∧ q.radialNormSq o i z ≤ 1 := by
  filter_upwards [q.differential i,
    (q.chart i).ae_scalar_row_quadratic_bound (q.field i) (q.differential i)
      (LipschitzWith.dist_right o)] with z hp hb
  let G := q.gram i z
  let α := differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z)
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hp.2.2 hp.2.1
  have hn : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  refine ⟨hn,?_⟩
  have hh := hb (G⁻¹.mulVec α)
  have he : G.mulVec (G⁻¹.mulVec α) = α := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
      Matrix.one_mulVec]
  change (α ⬝ᵥ G⁻¹.mulVec α)^2 ≤ (1:ℝ)^2*(G⁻¹.mulVec α ⬝ᵥ G.mulVec (G⁻¹.mulVec α)) at hh
  rw [he,dotProduct_comm (G⁻¹.mulVec α) α] at hh
  change α ⬝ᵥ G⁻¹.mulVec α ≤ 1
  nlinarith

lemma aestronglyMeasurable_radialNormSq (o : X) (i : ℕ) :
    AEStronglyMeasurable (q.radialNormSq o i) (volume.restrict (q.chart i).domain) := by
  let C := q.chart i
  let : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _
  let : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  have hPm : Measurable (q.gram i) := by
    have hh : Measurable (fun z a b => q.gram i z a b) :=
      measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
        measurable_polarizationMatrix (q.field i) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
          (q.measurable i) a b
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (borel _) _
    rw [show borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi from BorelSpace.measurable_eq.symm]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro a
    simp only [differentialRow]
    fun_prop
  have hc : Continuous (fun v : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
      v.1 ⬝ᵥ v.2.mulVec v.1) := by fun_prop
  have hm := hc.measurable.comp (hRd.prodMk (measurable_matrix_inverse _ hPm))
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR] with z hz
  change fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z = _ at hz
  simp only [radialNormSq,hz,Function.comp_apply]

end ChartGeometry
end CAT0Fillings
end

end OAI
