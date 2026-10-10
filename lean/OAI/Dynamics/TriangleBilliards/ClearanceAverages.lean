import OAI.Dynamics.TriangleBilliards.LongTrajectories

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal Topology ComplexConjugate
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Finset Set
open scoped Topology BigOperators
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
noncomputable section
open Filter Set
open scoped Topology
noncomputable section

namespace TriangularBilliards
open Analysis Filter

def clearanceAverage (Q : Triangle) (L ε T : ℝ) (u : DoubleL2 Q) : DoubleL2 Q :=
  (geodesicHilbertFlow Q).negativeAverage T
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)

lemma clearanceAverage_bounded (Q : Triangle) {L ε T H : ℝ} (hT : 0 < T)
    (hH : 0 ≤ H) {u : DoubleL2 Q} (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∀ᵐ z ∂doubleMeasure Q, ‖clearanceAverage Q L ε T u z‖ ≤ H := by
  apply (geodesicHilbertFlow Q).negativeAverage_mem_convex
    (convex_ae_bounded H) (isClosed_ae_bounded H) hT
  intro t _
  have hb := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_ae_bounded (goodMesh_measurable Q L ε T) hH hu)
  filter_upwards [hb,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hz he
  simpa only [he] using hz

lemma clearanceAverage_zero (Q : Triangle) {L ε T : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (u : DoubleL2 Q) :
    ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L * ε) → clearanceAverage Q L ε T u z = 0 := by
  apply (geodesicHilbertFlow Q).negativeAverage_mem_convex
    (convex_ae_zero_on _) (isClosed_ae_zero_on _) hT
  intro t ht
  have hc := doubleFlow_cocycle Q (-t) t
  have he := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_coe (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)
  filter_upwards [hc,he,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hc he hz
  intro hunsafe
  rw [hz,he]
  apply indicator_of_notMem
  intro hgood
  have hsafe := goodMesh_clearance hε hgood (t := -t) (by constructor <;> linarith [ht.1,ht.2])
  simp only [neg_add_cancel, doubleFlow_zero,Function.comp_apply] at hc
  rw [← hc] at hsafe
  exact (not_lt_of_ge hunsafe) hsafe

lemma clearanceAverage_estimates (Q : Triangle) {L ε T H : ℝ} (hT : 0 < T)
    (hH : 0 ≤ H) {u : DoubleL2 Q} (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H)
    (hinv : ∀ t, (geodesicHilbertFlow Q).act t u = u) :
    ‖clearanceAverage Q L ε T u - u‖ ≤
      H * (doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal ^ (1/2 : ℝ) ∧
    ∃ a : DoubleL2 Q, (geodesicHilbertFlow Q).HasGenerator (clearanceAverage Q L ε T u) a ∧
      ‖a‖ ≤ 2 * ‖u‖ / T := by
  let v := restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u
  constructor
  · apply ((geodesicHilbertFlow Q).negativeAverage_dist_invariant hinv hT v).trans
    rw [show v = restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u from rfl,
      restrictL2_sub_self,norm_neg]
    exact restrictL2_norm_of_bounded _ (goodMesh_measurable Q L ε T).compl (measure_ne_top _ _) hH hu
  · refine ⟨(T⁻¹ : ℝ) • (v - (geodesicHilbertFlow Q).act (-T) v),
      (geodesicHilbertFlow Q).negativeAverage_generator T v, ?_⟩
    apply ((geodesicHilbertFlow Q).negativeAverage_generator_norm hT v).trans
    gcongr
    exact restrictL2_norm _ _ _

end TriangularBilliards
namespace TriangularBilliards
open Analysis Filter Set
open scoped Topology

lemma restricted_clearance_zero_time (Q : Triangle) {L ε T t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc (-T) 0) (u : DoubleL2 Q) :
    ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L * ε) →
      (geodesicHilbertFlow Q).act t
        (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u) z = 0 := by
  have hc := doubleFlow_cocycle Q (-t) t
  have he := (measurePreserving_doubleFlow Q t).quasiMeasurePreserving.ae
    (restrictL2_coe (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)
  filter_upwards [hc,he,geodesic_koopman_ae Q t
    (restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u)] with z hc he hz
  intro hunsafe
  rw [hz,he]
  apply indicator_of_notMem
  intro hgood
  have hsafe := goodMesh_clearance hε hgood (t := -t) (by constructor <;> linarith [ht.1,ht.2])
  simp only [neg_add_cancel, doubleFlow_zero,Function.comp_apply] at hc
  rw [← hc] at hsafe
  exact (not_lt_of_ge hunsafe) hsafe

lemma clearanceAverage_generator_supported (Q : Triangle) {L ε T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H) {u : DoubleL2 Q}
    (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) :
    ∃ p : DoubleL2 Q,
      (geodesicHilbertFlow Q).HasGenerator (clearanceAverage Q L ε T u) p ∧
      (∀ᵐ z ∂doubleMeasure Q, ‖p z‖ ≤ 2*H/T) ∧
      (∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q (L*ε) → p z = 0) := by
  let v := restrictL2 (goodMesh Q L ε T) (goodMesh_measurable Q L ε T) u
  let w := (geodesicHilbertFlow Q).act (-T) v
  let p := (T⁻¹ : ℝ) • (v-w)
  refine ⟨p,(geodesicHilbertFlow Q).negativeAverage_generator T v,?_,?_⟩
  · have hv := restrictL2_ae_bounded (goodMesh_measurable Q L ε T) hH hu
    have hw := (measurePreserving_doubleFlow Q (-T)).quasiMeasurePreserving.ae hv
    filter_upwards [hv,hw,geodesic_koopman_ae Q (-T) v,
      Lp.coeFn_sub v w,Lp.coeFn_smul (T⁻¹ : ℝ) (v-w)] with z hv hw hc hd he
    change ‖p z‖ ≤ _
    change ((T⁻¹ : ℝ) • (v-w)) z = _ at he
    rw [he, Pi.smul_apply,hd,Pi.sub_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)]
    calc
      _ ≤ T⁻¹ * (‖v z‖+‖w z‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hT.le)
      _ ≤ T⁻¹ * (H+H) := by gcongr; simpa only [w,hc] using hw
      _ = _ := by ring
  · have hv := restricted_clearance_zero_time Q (L := L) (T := T) hε (t := 0) (by constructor <;> linarith) u
    have hw := restricted_clearance_zero_time Q (L := L) (T := T) hε (t := -T) (by constructor <;> linarith) u
    simp only [(geodesicHilbertFlow Q).zero] at hv
    filter_upwards [hv,hw,Lp.coeFn_sub v w,Lp.coeFn_smul (T⁻¹ : ℝ) (v-w)] with z hv hw hd he
    intro hz
    change ((T⁻¹ : ℝ) • (v-w)) z = 0
    rw [he,Pi.smul_apply,hd,Pi.sub_apply,hv hz,hw hz,sub_self,smul_zero]

/-- Choose a genuinely measurable everywhere bounded, spatially supported
representative; no pointwise assertion about an arbitrary Lp representative
is used. -/
lemma exists_bounded_supported_representative (Q : Triangle) {u : DoubleL2 Q} {H A : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H)
    (hs : ∀ᵐ z ∂doubleMeasure Q, z ∈ unsafeSet Q A → u z = 0) :
    ∃ f : DoublePhase → ℂ, StronglyMeasurable f ∧
      (∀ z, ‖f z‖ ≤ H) ∧ SpatiallyZero Q A f ∧ f =ᵐ[doubleMeasure Q] u := by
  classical
  let E := {z : DoublePhase | ‖u z‖ ≤ H ∧ A < Q.clearance z.1.1}
  have hE : MeasurableSet E :=
    (measurableSet_le (Lp.stronglyMeasurable u).measurable.norm measurable_const).inter
      (measurableSet_lt measurable_const (Q.clearance_lipschitz.continuous.measurable.comp measurable_fst.fst))
  refine ⟨E.indicator u,(Lp.stronglyMeasurable u).indicator hE,?_,?_,?_⟩
  · intro z
    by_cases hz : z ∈ E
    · simpa only [indicator_of_mem hz] using hz.1
    · simpa only [indicator_of_notMem hz,norm_zero] using hH
  · intro y _ hy v b
    exact indicator_of_notMem (by intro h; exact (not_lt_of_ge hy.le) h.2) _
  · filter_upwards [hu,hs] with z hz hzs
    by_cases hc : A < Q.clearance z.1.1
    · exact indicator_of_mem (show z ∈ E from ⟨hz,hc⟩) _
    · rw [indicator_of_notMem (by intro h; exact hc h.2)]
      exact (hzs (le_of_not_gt hc)).symm

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter Set
open scoped Topology

lemma doubleL2_norm_le_of_ae_bound (Q : Triangle) {u : DoubleL2 Q} {H : ℝ}
    (hH : 0 ≤ H) (hu : ∀ᵐ z ∂doubleMeasure Q, ‖u z‖ ≤ H) : ‖u‖ ≤ H := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hH hu

lemma reflectedSmoothingY_norm_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : DoublePhase → ℂ} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ z, ‖f z‖ ≤ H) (z : DoublePhase) :
    ‖reflectedSmoothingY Q ε f z‖ ≤ 4*derivativeMass*H/ε := by
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by
    rw [norm_transverseVelocity,mul_one]
    exact reflectedSmoothingGradient_norm_bound Q hε hH hf z)

lemma scaled_smoothingY_norm_tendsto (Q : Triangle) (u : DoubleL2 Q)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ε n * ‖(reflectedSmoothingY_memLp Q (hε n)
      (Lp.stronglyMeasurable u) (Lp.memLp u)).toLp _‖) atTop (𝓝 0) := by
  have he' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hε⟩
  have hlim := (scaled_gradient_lpNorm_tendsto Q (Lp.stronglyMeasurable u) (Lp.memLp u)).comp he'
  apply squeeze_zero (fun n => mul_nonneg (hε n).le (norm_nonneg _)) _ hlim
  intro n
  have hg := (reflectedSmoothingGradient_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)).const_smul (ε n)
  have hy := (reflectedSmoothingY_memLp Q (hε n) (Lp.stronglyMeasurable u) (Lp.memLp u)).const_smul (ε n)
  have hmono : eLpNorm (ε n • reflectedSmoothingY Q (ε n) u) 2 (doubleMeasure Q) ≤
      eLpNorm (ε n • reflectedSmoothingGradient Q (ε n) u) 2 (doubleMeasure Q) := by
    apply eLpNorm_mono_ae hy.aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.smul_apply,norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (ContinuousLinearMap.le_opNorm _ _).trans_eq (by rw [norm_transverseVelocity,mul_one])
  have hb := ENNReal.toReal_mono hg.eLpNorm_ne_top hmono
  rw [toReal_eLpNorm, toReal_eLpNorm, lpNorm_const_smul] at hb
  rw [Lp.norm_toLp, toReal_eLpNorm]
  simpa only [coe_nnnorm,Real.norm_eq_abs,abs_of_pos (hε n),Function.comp_def] using hb

lemma badMesh_real_bound (Q : Triangle) {L ε T : ℝ}
    (hL : 0 ≤ L+1) (hε : 0 < ε) (hT : 0 ≤ T) :
    (doubleMeasure Q (goodMesh Q L ε T)ᶜ).toReal ≤
      ((volume Q.table).toReal)⁻¹ * (3*(L+1)^2*Real.pi) * (T*ε+2*ε^2) := by
  have hfin : (Nat.ceil (T/ε)+1 : ℕ) * ((volume Q.table)⁻¹ *
      (3*(ENNReal.ofReal ((L+1)*ε))^2 * (NNReal.pi : ℝ≥0∞))) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr Q.area_pos.ne') (by finiteness))
  have hb := ENNReal.toReal_mono hfin (badMesh_measure_bound Q L ε T)
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (mul_nonneg hL hε.le),
    ENNReal.coe_toReal,NNReal.coe_real_pi,Nat.cast_add,Nat.cast_one] at hb
  have hceil : (Nat.ceil (T/ε) : ℝ)+1 ≤ T/ε+2 := by
    linarith [Nat.ceil_lt_add_one (div_nonneg hT hε.le)]
  apply hb.trans
  calc
    _ ≤ (T/ε+2) * (((volume Q.table).toReal)⁻¹ * (3*((L+1)*ε)^2*Real.pi)) := by
      gcongr
      rw [ENNReal.toReal_add (by simp) (by simp),ENNReal.toReal_natCast,ENNReal.toReal_one]
      exact hceil
    _ = _ := by field_simp

end TriangularBilliards

namespace TriangularBilliards
open Analysis SpatialSmoothing Filter Set
open scoped Topology ContDiff ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Quantitative global energy for a supported mollifier with a nonzero
transport source. All graphs are the actual specular generators. -/
lemma supported_source_CR (Q : Triangle) {ε R A T H : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hH : 0 ≤ H)
    (hR : Q.safetyFactor*ε < R) (hsmall : 2*R*Q.coordinateBound < 1)
    (hA : 2*R+2*ε ≤ A)
    {f p : DoublePhase → ℂ} (hfm : StronglyMeasurable f) (hpm : StronglyMeasurable p)
    (hf : MemLp f 2 (doubleMeasure Q)) (hp : MemLp p 2 (doubleMeasure Q))
    (hfp : (geodesicHilbertFlow Q).HasGenerator (hf.toLp f) (hp.toLp p))
    (hfb : ∀ z, ‖f z‖ ≤ H) (hpb : ∀ z, ‖p z‖ ≤ 2*H/T)
    (hfs : SpatiallyZero Q A f) (hps : SpatiallyZero Q A p) (j : ℤ)
    {U B : DoubleL2 Q} (hUB : (geodesicHilbertFlow Q).HasGenerator U B)
    (hB : (angularCircleAction Q).projection (j-1) B = B) :
    let hw := supportedSmoothing_memLp Q hε R hfm hfb
    ∃ a b : DoubleL2 Q,
      RotationalCR (geodesicHilbertFlow Q) (transverseHilbertFlow Q) (angularCircleAction Q)
        ((angularCircleAction Q).projection j (hw.toLp _)) a b ∧
      ‖a‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖b‖^2 ≤ 32*derivativeMass*H^2/(T*ε) ∧
      ‖inner ℂ B b‖ ≤ 4*‖B‖*H/T + H/T *
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ := by
  dsimp only
  have hDnonneg := derivativeMass_nonneg
  have hRp : 0 < R := (mul_pos Q.safetyFactor_pos hε).trans hR
  have hA' : 2*R+ε ≤ A := by linarith
  let w := supportedSmoothing Q ε R f
  have hd := supportedSmoothing_contDiff Q hε R hfm hfb
  obtain ⟨C,hC⟩ := supportedSmoothing_fderiv_bound Q hε hRp hfm hfb
  obtain ⟨D,hD⟩ := supportedSmoothing_second_bound Q hε hRp hfm hfb
  have hm := (supportedSmoothing_stronglyMeasurable Q ε R hfm).measurable
  have hd' := fun v b => (hd v b).differentiable (by simp)
  let hx := xDerivative_memLp_of_gradient_bound Q hm hd' hC
  let hy := yDerivative_memLp_of_gradient_bound Q hm hd' hC
  let hw := supportedSmoothing_memLp Q hε R hfm hfb
  have hs := supportedSmoothing_seam Q hε hR hsmall f
  let a := (1/2 : ℂ) • (hx.toLp _ - Complex.I • hy.toLp _)
  let b := (1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _)
  have hab : a+b = hx.toLp _ := by dsimp [a,b]; module
  have hdab : a-b = (-Complex.I) • hy.toLp _ := by dsimp [a,b]; module
  have hcr := seam_rotationalCR hs hd' hC hw hx hy
  have hn (k : ℤ) : ‖(angularCircleAction Q).projection (k+2) a‖ =
      ‖(angularCircleAction Q).projection k b‖ := by
    have hh := seam_projected_CR_norms_of_bounded_jets hs hm hd hC hD hw (k+1)
    simpa only [show k+1+1=k+2 by omega,add_sub_cancel_right] using hh
  have henergy := (angularCircleAction Q).localized_CR_energy a b j
    (ContinuousLinearMap.id ℂ _) (fun _ _ => rfl) (fun _ _ => rfl) rfl hn
  change ‖(angularCircleAction Q).projection (j+1) a‖^2 ≤ ‖a+b‖ * ‖a-b‖ at henergy
  rw [hab,hdab,norm_smul,norm_neg,Complex.norm_I,one_mul] at henergy
  have hxg := seam_geodesic_generator hs hd' hC hw hx
  have hxg' := supportedSmoothing_generator_commutes Q hε hR hsmall hA
    hfm hpm hf hp hfp hfb hpb hfs hps
  have hex := (geodesicHilbertFlow Q).generator_unique hxg hxg'
  have hyg := seam_transverse_generator hs hd' hC hw hy
  have hyg' := supportedSmoothing_transverse_generator Q hε hR hsmall hA' hfm hfb hf hfs
  have hey := (transverseHilbertFlow Q).generator_unique hyg hyg'
  have hxn : ‖hx.toLp _‖ ≤ 8*H/T := by
    rw [hex]
    apply (doubleL2_norm_le_of_ae_bound Q (H := 4*(2*H/T)) (by positivity) _).trans_eq (by ring)
    filter_upwards [(supportedSmoothing_memLp Q hε R hpm hpb).coeFn_toLp] with z hz
    rw [hz]
    exact supportedSmoothing_norm_bound Q hε R (by positivity) hpb z
  have hyn : ‖hy.toLp _‖ ≤ 4*derivativeMass*H/ε := by
    rw [hey]
    apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [(reflectedSmoothingY_memLp Q hε hfm hf).coeFn_toLp] with z hz
    rw [hz]
    exact reflectedSmoothingY_norm_bound Q hε hH hfb z
  have hbound : ‖(angularCircleAction Q).projection (j+1) a‖^2 ≤
      32*derivativeMass*H^2/(T*ε) := by
    apply henergy.trans
    calc
      _ ≤ (8*H/T)*(4*derivativeMass*H/ε) := mul_le_mul hxn hyn (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have heq := hn (j-1)
  rw [show j-1+2=j+1 by omega] at heq
  refine ⟨_,_,hcr.projection_covariant j,hbound,heq ▸ hbound,?_⟩
  have hyinner := clearance_smoothing_pairing Q hε hR hsmall hA hfm hpm hf hp hfp hfb hpb hfs hps hUB
  have hpbound : ‖hp.toLp p‖ ≤ 2*H/T := by
    apply doubleL2_norm_le_of_ae_bound Q (by positivity)
    filter_upwards [hp.coeFn_toLp] with z hz
    rw [hz]; exact hpb z
  have hyb : ‖inner ℂ B (hy.toLp _)‖ ≤
      ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ * (2*H/T) := by
    rw [hey,hyinner]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hpbound (norm_nonneg _))
  rw [← (angularCircleAction Q).projection_adjoint, hB]
  change ‖inner ℂ B ((1/2 : ℂ) • (hx.toLp _ + Complex.I • hy.toLp _))‖ ≤ _
  rw [inner_smul_right,inner_add_right,inner_smul_right,norm_mul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  calc
    _ ≤ (1/2 : ℝ) * (‖inner ℂ B (hx.toLp _)‖ + ‖Complex.I * inner ℂ B (hy.toLp _)‖) := by gcongr; exact norm_add_le _ _
    _ ≤ (1/2 : ℝ) * (‖B‖*(8*H/T) +
        ‖(reflectedSmoothingY_memLp Q hε (Lp.stronglyMeasurable U) (Lp.memLp U)).toLp _‖ * (2*H/T)) := by
      rw [norm_mul,Complex.norm_I,one_mul]
      gcongr
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))
    _ = _ := by ring

end TriangularBilliards

end
end
end
end
end
end
end
end
end
end

end OAI
