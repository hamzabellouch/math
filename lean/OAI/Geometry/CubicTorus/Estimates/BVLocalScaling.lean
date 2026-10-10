import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVBlowupNormalMeasure

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem line_invariant_local_product {B : Set Cover} (hB : MeasurableSet B)
    {n : Cover} (hn : ‖n‖ = 1)
    (htrans : ∀ t : ℝ, |t| ≤ 1/4 → ∀ᵐ x ∂(volume : Measure Cover),
      x ∈ Metric.ball (0 : Cover) (1/4) → (x+t • n ∈ B ↔ x ∈ B)) :
    ∃ C : Set (Fin 2 → ℝ), MeasurableSet C ∧
      ∀ᵐ z : ℝ × (Fin 2 → ℝ) ∂volume,
        |z.1| < 1/16 → ‖normalProductChart n (0,z.2)‖ < 1/16 →
          (normalProductChart n z ∈ B ↔ z.2 ∈ C) := by
  have hm : MeasurableSet {z : Cover × ℝ | |z.2| ≤ 1/4 →
      z.1 ∈ Metric.ball (0 : Cover) (1/4) → (z.1+z.2 • n ∈ B ↔ z.1 ∈ B)} := by
    exact (measurableSet_le measurable_snd.abs measurable_const).imp
      ((Metric.isOpen_ball.measurableSet.preimage measurable_fst).imp
        ((hB.preimage (measurable_fst.add (measurable_snd.smul_const n))).iff
          (hB.preimage measurable_fst)))
  have hx : ∀ᵐ x ∂(volume : Measure Cover), ∀ᵐ t ∂(volume : Measure ℝ),
      |t| ≤ 1/4 → x ∈ Metric.ball (0 : Cover) (1/4) → (x+t • n ∈ B ↔ x ∈ B) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply ae_of_all
    intro t
    by_cases ht : |t| ≤ 1/4
    · exact (htrans t ht).mono (fun x hh _ ↦ hh)
    · exact ae_of_all _ (fun _ hh ↦ (ht hh).elim)
  have hz := (normalProductChart_measurePreserving n).quasiMeasurePreserving.ae hx
  have hsplit := Measure.ae_ae_of_ae_prod hz
  have hrel : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ y : Fin 2 → ℝ ∂volume,
      ∀ᵐ t ∂(volume : Measure ℝ), |s| < 1/16 →
        ‖normalProductChart n (0,y)‖ < 1/16 → |t| < 1/16 →
          (normalProductChart n (t,y) ∈ B ↔ normalProductChart n (s,y) ∈ B) := by
    filter_upwards [hsplit] with s hs
    filter_upwards [hs] with y hy
    have ht := (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae hy
    filter_upwards [ht] with t hh hs0 hy0 ht0
    have hts : |t+-s| ≤ 1/4 := (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
    have hxb : normalProductChart n (s,y) ∈ Metric.ball (0 : Cover) (1/4) := by
      rw [Metric.mem_ball,dist_zero_right,normalProductChart_decompose hn]
      exact (norm_add_le _ _).trans_lt (by rw [norm_smul,Real.norm_eq_abs,hn,mul_one]; linarith)
    have heq : normalProductChart n (s,y)+(t+-s) • n = normalProductChart n (t,y) := by
      rw [normalProductChart_decompose hn s y,normalProductChart_decompose hn t y]
      module
    simpa only [heq] using hh hts hxb
  have hpos : (volume : Measure ℝ) (Ioo (-(1/16 : ℝ)) (1/16)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hrel)
  have hs0 : |s| < 1/16 := abs_lt.mpr hsI
  let C : Set (Fin 2 → ℝ) := {y | normalProductChart n (s,y) ∈ B}
  have hC : MeasurableSet C := hB.preimage
    ((normalProductChart n).measurable.comp (measurable_const.prodMk measurable_id))
  refine ⟨C,hC,?_⟩
  have hm' : MeasurableSet {z : (Fin 2 → ℝ) × ℝ | |z.2| < 1/16 →
      ‖normalProductChart n (0,z.1)‖ < 1/16 →
        (normalProductChart n (z.2,z.1) ∈ B ↔ z.1 ∈ C)} := by
    exact (measurableSet_lt measurable_snd.abs measurable_const).imp
      ((measurableSet_lt (((normalProductChart n).measurable.comp
        (measurable_const.prodMk measurable_fst)).norm) measurable_const).imp
        ((hB.preimage ((normalProductChart n).measurable.comp measurable_swap)).iff
          (hC.preimage measurable_fst)))
  apply (Measure.ae_prod_iff_ae_ae (hm'.preimage measurable_swap)).mpr
  apply (Measure.ae_ae_comm hm').mp
  filter_upwards [hs] with y hy
  filter_upwards [hy] with t ht ht0 hy0
  exact ht hs0 hy0 ht0

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def affineCoverRegion (A : Set Cover) (c : Cover) (r : ℝ) : Set Cover :=
  {x | r⁻¹ • (x-c) ∈ A}

lemma measurableSet_affineCoverRegion {A : Set Cover} (hA : MeasurableSet A) (c : Cover) (r : ℝ) :
    MeasurableSet (affineCoverRegion A c r) := hA.preimage (by fun_prop)

lemma divergence_affine_pullback {F : Cover → Cover} (hF : Differentiable ℝ F)
    (c : Cover) (r : ℝ) (x : Cover) :
    divergence (fun y : Cover ↦ F (r • y+c)) x = r*divergence F (r • x+c) := by
  have hd := (hF (r • x+c)).hasFDerivAt.comp x (((hasFDerivAt_id x).const_smul r).add_const c)
  change HasFDerivAt (fun y : Cover ↦ F (r • y+c)) _ x at hd
  simp only [divergence,hd.fderiv,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,PiLp.smul_apply,
    smul_eq_mul,Finset.mul_sum]

lemma tsupport_affine_pullback {F : Cover → Cover} (c : Cover) {r : ℝ} (hr : 0 < r)
    {b : ℝ} (hs : tsupport F ⊆ Metric.closedBall c (r*b)) :
    tsupport (fun y : Cover ↦ F (r • y+c)) ⊆ Metric.closedBall (0 : Cover) b := by
  intro x hx
  have hh := hs (tsupport_comp_subset_preimage F
    (by fun_prop : Continuous (fun y : Cover ↦ r • y+c)) hx)
  have hh' : r*‖x‖ ≤ r*b := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_right,norm_smul,
      Real.norm_of_nonneg hr.le] using hh
  simpa only [Metric.mem_closedBall,dist_zero_right] using (mul_le_mul_iff_right₀ hr).mp hh'

lemma integral_divergence_affineCoverRegion {A : Set Cover} (hA : MeasurableSet A)
    (c : Cover) {r : ℝ} (hr : 0 < r) {F : Cover → Cover} (hF : Differentiable ℝ F) :
    (∫ x in affineCoverRegion A c r, divergence F x) =
      r^2*(∫ x in A, divergence (fun y : Cover ↦ F (r • y+c)) x) := by
  have hAr := measurableSet_affineCoverRegion hA c r
  have he := integral_cover_affine_scaling
    ((affineCoverRegion A c r).indicator (divergence F)) c hr
  have hind : (fun y : Cover ↦ (affineCoverRegion A c r).indicator (divergence F) (r • y+c)) =
      A.indicator (fun y ↦ divergence F (r • y+c)) := by
    funext y
    have hm : r • y+c ∈ affineCoverRegion A c r ↔ y ∈ A := by
      simp only [affineCoverRegion,mem_ofPred_eq,add_sub_cancel_right,smul_smul,
        inv_mul_cancel₀ hr.ne',one_smul]
    by_cases hy : y ∈ A <;> simp [hm,hy]
  rw [integral_indicator hAr,hind,integral_indicator hA] at he
  rw [he]
  simp_rw [divergence_affine_pullback hF c r]
  rw [integral_const_mul]
  ring

theorem affineCoverRegion_flux_le {A : Set Cover} (hA : MeasurableSet A)
    {L b : ℝ} (hL0 : 0 ≤ L)
    (hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (c : Cover) {r : ℝ} (hr : 0 < r) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : tsupport F ⊆ Metric.closedBall c (r*b))
    (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in affineCoverRegion A c r, divergence F x) ≤ r^2*L := by
  rw [integral_divergence_affineCoverRegion hA c hr (hF.differentiable (by simp))]
  have hFs := tsupport_affine_pullback c hr hs
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  exact integral_divergence_le_coverLocalPerimeter hL hL0
    (hF.comp ((contDiff_id.const_smul r).add contDiff_const))
    ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hFs)
    hFs (fun x ↦ hb _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def torusCoverRegion (A : Set Cover) : Set Torus := {z | representative z ∈ A}

lemma measurableSet_torusCoverRegion {A : Set Cover} (hA : MeasurableSet A) :
    MeasurableSet (torusCoverRegion A) := hA.preimage measurable_representative

lemma characteristic_torusCoverRegion {x : Cover} (hx : x ∈ fundamentalCube) (A : Set Cover) :
    characteristic (torusCoverRegion A) (quotientMap x) = A.indicator (fun _ ↦ (1 : ℝ)) x := by
  have hm : quotientMap x ∈ torusCoverRegion A ↔ x ∈ A := by
    change representative (quotientMap x) ∈ A ↔ x ∈ A
    rw [representative_quotientMap_of_mem hx]
  by_cases ha : x ∈ A <;> simp [characteristic,Set.indicator,hm,ha]

lemma interior_cutoff_flux_eq_set {A : Set Cover} (hA : MeasurableSet A)
    {w : Cover → ℝ} (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (X : Cover → Cover) :
    (∫ x in fundamentalCube, characteristic (torusCoverRegion A) (quotientMap x) *
      divergence (fun y ↦ latticePeriodize w y • X y) x) =
      ∫ x in A, divergence (fun y ↦ w y • X y) x := by
  rw [← integral_indicator measurableSet_fundamentalCube,← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · rw [indicator_of_mem hx,characteristic_torusCoverRegion hx]
    have he := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩)).smul
      (EventuallyEq.rfl : X =ᶠ[𝓝 x] X)
    have hd := he.fderiv_eq (𝕜 := ℝ)
    have hdiv : divergence (fun y ↦ latticePeriodize w y • X y) x =
        divergence (fun y ↦ w y • X y) x := by simp only [divergence,hd]
    rw [hdiv]
    by_cases ha : x ∈ A <;> simp [Set.indicator,ha]
  · rw [indicator_of_notMem hx]
    have hsup : tsupport (fun y ↦ w y • X y) ⊆ tsupport w := tsupport_smul_subset_left w X
    have hdiv : divergence (fun y ↦ w y • X y) x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      exact hx (fun i ↦ ⟨(hs (hsup hh) i).1.le,(hs (hsup hh) i).2⟩)
    by_cases ha : x ∈ A <;> simp [Set.indicator,ha,hdiv]

lemma torus_affine_radial_flux_le {A : Set Cover} (hA : MeasurableSet A)
    {L b r ρ ε : ℝ} (hL0 : 0 ≤ L)
    (hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hρb : ρ ≤ r*b) (hρs : ρ < 1/4) (hε : 0 < ε)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x in fundamentalCube,
      characteristic (torusCoverRegion (affineCoverRegion A cubeCenter r)) (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) ε y • X y) x) ≤ r^2*L := by
  rw [← radialDensityWeight_periodize hρ hρs hε,
    interior_cutoff_flux_eq_set (measurableSet_affineCoverRegion hA _ _)
      (radialDensityWeight_hasCompactSupport hρ hε)
      (radialDensityWeight_cell_support hρ (by linarith) hε)]
  apply affineCoverRegion_flux_le hA hL0 hL cubeCenter hr
    ((radialDensityWeight_contDiff _ _ _).smul hX.1)
  · exact (tsupport_smul_subset_left _ _).trans
      ((radialDensityWeight_tsupport hρ hε).trans (Metric.closedBall_subset_closedBall hρb))
  · intro x
    change ‖radialDensityWeight cubeCenter ρ ε x • X x‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact (mul_le_of_le_one_right (radialDensityWeight_nonneg _ _ _ _) (hX.2.2 x)).trans
      (radialDensityWeight_le_one _ _ _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma torus_affine_symmDiff_support {A B : Set Cover} {a r : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hs : r*a ≤ 1/4)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    torusCoverRegion (affineCoverRegion A cubeCenter r) ∆
      torusCoverRegion (affineCoverRegion B cubeCenter r) ⊆
        sublevelRegion radialSquared ((r*a)^2) := by
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le ha) hs]
  intro z hz
  have hm : r⁻¹ • (representative z-cubeCenter) ∈ A ∆ B := hz
  have hh := hAB hm
  have hh' : ‖representative z-cubeCenter‖/r < a := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hh
  change dist (representative z) cubeCenter < r*a
  rw [dist_eq_norm]
  simpa only [mul_comm] using (div_lt_iff₀ hr).mp hh'

lemma torus_affine_symmDiff_volume {E : Set Torus} (hE : MeasurableSet E)
    {A : Set Cover} (hA : MeasurableSet A) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hs : r*b ≤ 1/4) :
    sublevelVolume (E ∆ torusCoverRegion (affineCoverRegion A cubeCenter r))
      radialSquared ((r*b)^2) =
      r^3*(∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E cubeCenter r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) := by
  let F := torusCoverRegion (affineCoverRegion A cubeCenter r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hc : Metric.ball cubeCenter (r*b) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior (by linarith))
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le hb) hs,cubeBall_eq_metricBall,
    ← setIntegral_characteristic (hE.symmDiff hF) _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball (characteristic (E ∆ F)) (measurable_characteristic (hE.symmDiff hF))
      cubeCenter (r*b) hc,
    integral_ball_affine_scaling _ cubeCenter hr b]
  congr 1
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x hx
  have hxb : cubeCenter+r • x ∈ Metric.ball cubeCenter (r*b) := by
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,
      Real.norm_of_nonneg hr.le] using (mul_lt_mul_of_pos_left (show ‖x‖ < b by simpa only [Metric.mem_ball,dist_zero_right] using hx) hr)
  have hxc : cubeCenter+r • x ∈ fundamentalCube := fun j ↦ ⟨(hc hxb j).1.le,(hc hxb j).2⟩
  dsimp only
  rw [characteristic_symmDiff_eq_abs]
  dsimp only [F]
  rw [characteristic_torusCoverRegion hxc]
  have hm : cubeCenter+r • x ∈ affineCoverRegion A cubeCenter r ↔ x ∈ A := by
    simp only [affineCoverRegion,Set.mem_ofPred_eq,add_sub_cancel_left,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  change |blowupCharacteristic E cubeCenter r x-_| = _
  by_cases ha : x ∈ A <;> simp [Set.indicator,hm,ha]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_local_flux_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (F : Set Torus), MeasurableSet F →
      ∀ (q : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) q →
      (∀ n x, q (x+latticeVector n) = q x) →
      ∀ K M t d L : ℝ, (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      (∀ x, q x < t → ‖gradient q x‖ ≤ M) →
      HasDerivAt (sublevelVolume (E ∆ F) q) d t →
      sublevelVolume (E ∆ F) q t < η →
      (∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
        (∫ x in fundamentalCube, characteristic F (quotientMap x)*
          divergence (fun y ↦ sublevelCutoff q t (1/((i : ℝ)+1)) y • X y) x) ≤ L) →
      (μ : Measure NormalBundle).real {z | q z.1 < t} ≤ L+K*M*d+C*sublevelVolume (E ∆ F) q t := by
  obtain ⟨η,C,hη,hC,hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η,C,hη,hC,?_⟩
  intro F hF q hq hp K M t d L hK hg hd ht hloc
  obtain ⟨hG,hbound⟩ := perimeter_glued_local_flux_le hE hF hμ hq hp hK hg hd
    (tendsto_const_nhds (f := atTop) (x := L)) hloc
  have he : regionDistance E (gluedRegion E F (sublevelRegion q t)) =
      sublevelVolume (E ∆ F) q t := regionDistance_gluedRegion hE.nullMeasurableSet
        hF.nullMeasurableSet (measurableSet_sublevelRegion hq.continuous.measurable _).nullMeasurableSet
  have hh := hc _ hG (he ▸ ht)
  rw [he] at hh
  rw [hμ.1] at hbound
  linarith

theorem isMinimizerAt_local_flux_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ F G : Set Torus,
      MeasurableSet F → MeasurableSet G → ∀ a b B T K L : ℝ,
      0 < a → a < b → b < 1/4 → 0 ≤ L → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ G ⊆ sublevelRegion radialSquared (a^2) →
      sublevelVolume (E ∆ G) radialSquared (b^2) < B →
      sublevelVolume (E ∆ F) radialSquared (b^2) < T →
      (∀ ρ ∈ Ioo a b, ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
        (∫ x in fundamentalCube, characteristic F (quotientMap x)*
          divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L) →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) a) ≤
        L+2*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro F G hF hG a b B T K L ha hab hbs hL hT hK hFG heG heF hloc
  let m := sublevelVolume (E ∆ G) radialSquared
  have hm : Monotone m := sublevelVolume_mono _ _
  have hab2 : a^2 < b^2 := by nlinarith
  have hB : 0 < B := (show 0 ≤ m (b^2) from measureReal_nonneg).trans_lt heG
  have hdpos : 0 < b^2-a^2 := sub_pos.mpr hab2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hdpos.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm hab2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hdF : HasDerivAt (sublevelVolume (E ∆ F) radialSquared) (deriv m t) t := by
    exact hasDerivAt_sublevelVolume_of_interior_change
      radialSquared_contDiff.continuous.measurable ht.1
      (by simpa only [symmDiff_comm] using hFG) hd.hasDerivAt
  have hFt : sublevelVolume (E ∆ F) radialSquared t < T :=
    (sublevelVolume_mono _ _ ht.2.le).trans_lt heF
  have hh := hcomp F hF radialSquared radialSquared_contDiff radialSquared_periodic
    K (2*ρ) (ρ^2) (deriv m t) L hK (norm_gradient_radialSquared hρ0.le (hρb.trans hbs).le)
    (hρsq ▸ hdF) (by rw [hρsq]; exact hFt.trans hT) (hloc ρ ⟨hρa,hρb⟩)
  rw [normalMeasure_radial_sublevel μ hρ0.le (hρb.trans hbs).le] at hh
  have hmono : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) a) ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) ρ) :=
    measureReal_mono (Metric.ball_subset_ball hρa.le)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : K*(2*ρ)*deriv m t ≤ K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : K*(2*ρ)*(B/(b^2-a^2)) ≤ K*(2*b)*(B/(b^2-a^2)) := by gcongr
  have hct : C*sublevelVolume (E ∆ F) radialSquared (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left (by rw [hρsq]; exact hFt.le) hC
  have heq : K*(2*b)*(B/(b^2-a^2)) = 2*K*b*B/(b^2-a^2) := by ring
  rw [heq] at hd2
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma torus_affine_radial_flux_le {A : Set Cover} (hA : MeasurableSet A)
    {L b r ρ ε : ℝ} (hL0 : 0 ≤ L)
    (hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hρb : ρ ≤ r*b) (hρs : ρ < 1/4) (hε : 0 < ε)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x in fundamentalCube,
      characteristic (torusCoverRegion (affineCoverRegion A (c : Cover) r)) (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff (radialSquared c) (ρ^2) ε y • X y) x) ≤ r^2*L := by
  rw [← radialDensityWeight_periodize hρ hρs hε,
    interior_cutoff_flux_eq_set (measurableSet_affineCoverRegion hA _ _)
      (radialDensityWeight_hasCompactSupport hρ hε)
      (radialDensityWeight_cell_support hρ (by linarith) hε)]
  apply affineCoverRegion_flux_le hA hL0 hL (c : Cover) hr
    ((radialDensityWeight_contDiff _ _ _).smul hX.1)
  · exact (tsupport_smul_subset_left _ _).trans
      ((radialDensityWeight_tsupport hρ hε).trans (Metric.closedBall_subset_closedBall hρb))
  · intro x
    change ‖radialDensityWeight (c : Cover) ρ ε x • X x‖ ≤ 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact (mul_le_of_le_one_right (radialDensityWeight_nonneg _ _ _ _) (hX.2.2 x)).trans
      (radialDensityWeight_le_one _ _ _ _)

lemma torus_affine_symmDiff_support {A B : Set Cover} {a r : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hs : r*a ≤ 1/4)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    torusCoverRegion (affineCoverRegion A (c : Cover) r) ∆
      torusCoverRegion (affineCoverRegion B (c : Cover) r) ⊆
        sublevelRegion (radialSquared c) ((r*a)^2) := by
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le ha) hs]
  intro z hz
  have hm : r⁻¹ • (representative z-(c : Cover)) ∈ A ∆ B := hz
  have hh := hAB hm
  have hh' : ‖representative z-(c : Cover)‖/r < a := by
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hh
  change dist (representative z) (c : Cover) < r*a
  rw [dist_eq_norm]
  simpa only [mul_comm] using (div_lt_iff₀ hr).mp hh'

lemma torus_affine_symmDiff_volume {E : Set Torus} (hE : MeasurableSet E)
    {A : Set Cover} (hA : MeasurableSet A) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hs : r*b ≤ 1/4) :
    sublevelVolume (E ∆ torusCoverRegion (affineCoverRegion A (c : Cover) r))
      (radialSquared c) ((r*b)^2) =
      r^3*(∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E (c : Cover) r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) := by
  let F := torusCoverRegion (affineCoverRegion A (c : Cover) r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hc : Metric.ball (c : Cover) (r*b) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (closedBall_interior (by linarith))
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared (mul_nonneg hr.le hb) hs,cubeBall_eq_metricBall (by linarith),
    ← setIntegral_characteristic (hE.symmDiff hF) _ Metric.isOpen_ball.measurableSet,
    integral_quotient_ball (characteristic (E ∆ F)) (measurable_characteristic (hE.symmDiff hF))
      (c : Cover) (r*b) hc,
    integral_ball_affine_scaling _ (c : Cover) hr b]
  congr 1
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro x hx
  have hxb : (c : Cover)+r • x ∈ Metric.ball (c : Cover) (r*b) := by
    simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,
      Real.norm_of_nonneg hr.le] using (mul_lt_mul_of_pos_left (show ‖x‖ < b by simpa only [Metric.mem_ball,dist_zero_right] using hx) hr)
  have hxc : (c : Cover)+r • x ∈ fundamentalCube := fun j ↦ ⟨(hc hxb j).1.le,(hc hxb j).2⟩
  dsimp only
  rw [characteristic_symmDiff_eq_abs]
  dsimp only [F]
  rw [characteristic_torusCoverRegion hxc]
  have hm : (c : Cover)+r • x ∈ affineCoverRegion A (c : Cover) r ↔ x ∈ A := by
    simp only [affineCoverRegion,Set.mem_ofPred_eq,add_sub_cancel_left,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  change |blowupCharacteristic E (c : Cover) r x-_| = _
  by_cases ha : x ∈ A <;> simp [Set.indicator,hm,ha]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter

lemma normalMeasure_radial_sublevel {c : InteriorCenter} (μ : FiniteMeasure NormalBundle) {r : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1/4) :
    (μ : Measure NormalBundle).real {z | (radialSquared c) z.1 < r^2} =
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) r) := by
  rw [← cubeBall_eq_metricBall (by linarith : r ≤ 3/8), ← sublevelRegion_radialSquared hr hs]
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle)
    (sublevelRegion (radialSquared c) (r^2))).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable
    (measurableSet_sublevelRegion radialSquared_contDiff.continuous.measurable _)]
  congr 1
  ext z
  exact (mem_sublevelRegion_quotient radialSquared_periodic (r^2) z.1).symm

theorem isMinimizerAt_local_flux_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (F G : Set Torus),
      MeasurableSet F → MeasurableSet G → ∀ a b B T K L : ℝ,
      0 < a → a < b → b < 1/4 → 0 ≤ L → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ G ⊆ sublevelRegion (radialSquared c) (a^2) →
      sublevelVolume (E ∆ G) (radialSquared c) (b^2) < B →
      sublevelVolume (E ∆ F) (radialSquared c) (b^2) < T →
      (∀ ρ ∈ Ioo a b, ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
        (∫ x in fundamentalCube, characteristic F (quotientMap x)*
          divergence (fun y ↦ sublevelCutoff (radialSquared c) (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L) →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) a) ≤
        L+2*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro c F G hF hG a b B T K L ha hab hbs hL hT hK hFG heG heF hloc
  let m := sublevelVolume (E ∆ G) (radialSquared c)
  have hm : Monotone m := sublevelVolume_mono _ _
  have hab2 : a^2 < b^2 := by nlinarith
  have hB : 0 < B := (show 0 ≤ m (b^2) from measureReal_nonneg).trans_lt heG
  have hdpos : 0 < b^2-a^2 := sub_pos.mpr hab2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hdpos.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm hab2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hdF : HasDerivAt (sublevelVolume (E ∆ F) (radialSquared c)) (deriv m t) t := by
    exact hasDerivAt_sublevelVolume_of_interior_change
      (radialSquared_contDiff (c:=c)).continuous.measurable ht.1
      (by simpa only [symmDiff_comm] using hFG) hd.hasDerivAt
  have hFt : sublevelVolume (E ∆ F) (radialSquared c) t < T :=
    (sublevelVolume_mono _ _ ht.2.le).trans_lt heF
  have hh := hcomp F hF (radialSquared c) (radialSquared_contDiff (c:=c)) (radialSquared_periodic (c:=c))
    K (2*ρ) (ρ^2) (deriv m t) L hK (norm_gradient_radialSquared hρ0.le (hρb.trans hbs).le)
    (hρsq ▸ hdF) (by rw [hρsq]; exact hFt.trans hT) (hloc ρ ⟨hρa,hρb⟩)
  rw [normalMeasure_radial_sublevel μ hρ0.le (hρb.trans hbs).le] at hh
  have hmono : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) a) ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) ρ) :=
    measureReal_mono (Metric.ball_subset_ball hρa.le)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : K*(2*ρ)*deriv m t ≤ K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : K*(2*ρ)*(B/(b^2-a^2)) ≤ K*(2*b)*(B/(b^2-a^2)) := by gcongr
  have hct : C*sublevelVolume (E ∆ F) (radialSquared c) (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left (by rw [hρsq]; exact hFt.le) hC
  have heq : K*(2*b)*(B/(b^2-a^2)) = 2*K*b*B/(b^2-a^2) := by ring
  rw [heq] at hd2
  linarith

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_scaled_set_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (A B : Set Cover),
      MeasurableSet A → MeasurableSet B → ∀ a b L K r δ : ℝ,
      0 < a → a < b → 0 < r → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η → 0 ≤ L →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L →
      A ∆ B ⊆ Metric.ball (0 : Cover) a →
      (∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E (c : Cover) r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < δ →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) (r*a)) ≤
        r^2*(L+2*K*b*δ/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro c A B hA hB a b L K r δ ha hab hr hsmall hηr hL hK hper hAB herr
  let F := torusCoverRegion (affineCoverRegion B (c : Cover) r)
  let G := torusCoverRegion (affineCoverRegion A (c : Cover) r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hB _ _)
  have hG : MeasurableSet G := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hbpos : 0 < b := ha.trans hab
  have hra : 0 < r*a := mul_pos hr ha
  have hrab : r*a < r*b := mul_lt_mul_of_pos_left hab hr
  have hchange : F ∆ G ⊆ sublevelRegion (radialSquared c) ((r*a)^2) :=
    torus_affine_symmDiff_support hr ha.le (hrab.le.trans hsmall.le)
      (by simpa only [symmDiff_comm] using hAB)
  have hvol : sublevelVolume (E ∆ G) (radialSquared c) ((r*b)^2) < r^3*δ := by
    rw [torus_affine_symmDiff_volume hE hA hr (ha.trans hab).le hsmall.le]
    exact mul_lt_mul_of_pos_left herr (pow_pos hr 3)
  have htot : sublevelVolume (E ∆ F) (radialSquared c) ((r*b)^2) < (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hsmall.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hloc : ∀ ρ ∈ Ioo (r*a) (r*b), ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
      (∫ x in fundamentalCube, characteristic F (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff (radialSquared c) (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ r^2*L := by
    intro ρ hρ i X hX
    exact torus_affine_radial_flux_le hB hL hper hr (hra.trans hρ.1).le hρ.2.le
      (hρ.2.trans hsmall) (by positivity) hX
  have hh := hcomp c F G hF hG (r*a) (r*b) (r^3*δ) ((r*b)^3*(Real.pi*8/3)) K (r^2*L)
    hra hrab hsmall (mul_nonneg (sq_nonneg _) hL) hηr hK hchange hvol htot hloc
  apply hh.trans_eq
  have hd : b^2-a^2 ≠ 0 := by nlinarith
  field_simp

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma moving_blowup_flux_tendsto {E : Set Torus} (hE : MeasurableSet E)
    (c : ℕ → Cover) (r : ℕ → ℝ) {A : Set Cover} (hA : MeasurableSet A)
    {R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) R) :
    Tendsto (fun i ↦ ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x)
      l (𝓝 (∫ x in A, divergence F x)) := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hd : HasCompactSupport (divergence F) := hFs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  let k : Cover →ᵇ ℝ := ofCompactSupport _ (continuous_divergence hF) hd
  have ht := localL1_weighted_integral_tendsto
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv k
  have hz (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) R) : divergence F x = 0 :=
    divergence_of_notMem_tsupport (fun hh ↦ hx (hs hh))
  have heg (i) : (∫ x in Metric.closedBall (0 : Cover) R, blowupCharacteristic E (c i) (r i) x*k x) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])
  have hef : (∫ x in Metric.closedBall (0 : Cover) R, A.indicator (fun _ ↦ (1 : ℝ)) x*k x) =
      ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])]
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence F x) = _
    simp only [← indicator_mul_left,one_mul]
    exact integral_indicator hA
  simpa only [heg,hef] using ht

lemma blowup_flux_le_scaled_mass {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r a : ℝ} (hr : 0 < r) (ha : a ≤ 1)
    (hc : Metric.closedBall c r ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.ball (0 : Cover) a) (hb : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x, blowupCharacteristic E c r x*divergence F x) ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap c) (r*a))/r^2 := by
  have hs1 := hs.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ha))
  have he := normalMeasure_scaled_flux hE hμ hF hs1 c hr hc
  rw [show (fun x ↦ characteristic E (quotientMap (r • x+c))*divergence F x) =
      (fun x ↦ blowupCharacteristic E c r x*divergence F x) by funext x; simp only [blowupCharacteristic,add_comm c]] at he
  rw [← he]
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball c (r*a)}
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.preimage (by fun_prop)
  have hchart : Metric.ball c (r*a) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by nlinarith))).trans hc
  rw [← cellBallMass_eq_spatialNormalMeasure μ c (r*a) hchart]
  change _ ≤ (μ : Measure NormalBundle).real S
  let f : NormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F (r⁻¹ • ((z.1 : Cover)-c))⟫
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfi : Integrable f (μ : Measure NormalBundle) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (μ : Measure NormalBundle) := (integrable_const 1).indicator hS
  have hfbd (z : NormalBundle) : f z ≤ S.indicator (fun _ ↦ (1 : ℝ)) z := by
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
      exact (real_inner_le_norm _ _).trans (by rw [z.2.property,one_mul]; exact hb _)
    · rw [indicator_of_notMem hz]
      have hx : r⁻¹ • ((z.1 : Cover)-c) ∉ tsupport F := by
        intro hh
        have hnorm : ‖(z.1 : Cover)-c‖/r < a := by
          simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),div_eq_inv_mul] using hs hh
        exact hz (by change dist (z.1 : Cover) c < r*a; rw [dist_eq_norm]; nlinarith [(div_lt_iff₀ hr).mp hnorm])
      simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right,le_refl]
  have hh := integral_mono hfi hgi hfbd
  simpa only [integral_indicator hS,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_scaled_set_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ A B : Set Cover,
      MeasurableSet A → MeasurableSet B → ∀ a b L K r δ : ℝ,
      0 < a → a < b → 0 < r → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η → 0 ≤ L →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L →
      A ∆ B ⊆ Metric.ball (0 : Cover) a →
      (∫ x in Metric.ball (0 : Cover) b,
        |blowupCharacteristic E cubeCenter r x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < δ →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) (r*a)) ≤
        r^2*(L+2*K*b*δ/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_local_flux_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro A B hA hB a b L K r δ ha hab hr hsmall hηr hL hK hper hAB herr
  let F := torusCoverRegion (affineCoverRegion B cubeCenter r)
  let G := torusCoverRegion (affineCoverRegion A cubeCenter r)
  have hF : MeasurableSet F := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hB _ _)
  have hG : MeasurableSet G := measurableSet_torusCoverRegion (measurableSet_affineCoverRegion hA _ _)
  have hbpos : 0 < b := ha.trans hab
  have hra : 0 < r*a := mul_pos hr ha
  have hrab : r*a < r*b := mul_lt_mul_of_pos_left hab hr
  have hchange : F ∆ G ⊆ sublevelRegion radialSquared ((r*a)^2) :=
    torus_affine_symmDiff_support hr ha.le (hrab.le.trans hsmall.le)
      (by simpa only [symmDiff_comm] using hAB)
  have hvol : sublevelVolume (E ∆ G) radialSquared ((r*b)^2) < r^3*δ := by
    rw [torus_affine_symmDiff_volume hE hA hr (ha.trans hab).le hsmall.le]
    exact mul_lt_mul_of_pos_left herr (pow_pos hr 3)
  have htot : sublevelVolume (E ∆ F) radialSquared ((r*b)^2) < (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hsmall.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hloc : ∀ ρ ∈ Ioo (r*a) (r*b), ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
      (∫ x in fundamentalCube, characteristic F (quotientMap x)*
        divergence (fun y ↦ sublevelCutoff radialSquared (ρ^2) (1/((i : ℝ)+1)) y • X y) x) ≤ r^2*L := by
    intro ρ hρ i X hX
    exact torus_affine_radial_flux_le hB hL hper hr (hra.trans hρ.1).le hρ.2.le
      (hρ.2.trans hsmall) (by positivity) hX
  have hh := hcomp F G hF hG (r*a) (r*b) (r^3*δ) ((r*b)^3*(Real.pi*8/3)) K (r^2*L)
    hra hrab hsmall (mul_nonneg (sq_nonneg _) hL) hηr hK hchange hvol htot hloc
  apply hh.trans_eq
  have hd : b^2-a^2 ≠ 0 := by nlinarith
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma density_scaled_mass_tendsto {m : ℝ → ℝ} {θ : ℝ}
    (hθ : Tendsto (fun t ↦ m t/t^2) (𝓝[>] 0) (𝓝 θ))
    {l : Filter ℕ} (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r l (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i ↦ m (r i*a)/(r i)^2) l (𝓝 (θ*a^2)) := by
  have ht : Tendsto (fun i ↦ r i*a) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const a,
      Eventually.of_forall fun i ↦ mul_pos (hr i) ha⟩
  have hh := (hθ.comp ht).mul_const (a^2)
  convert hh using 1
  funext i
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',ha.ne']

lemma blowup_error_integrable {E : Set Torus} (hE : MeasurableSet E)
    {A : Set Cover} (hA : MeasurableSet A) (c : Cover) (r R : ℝ) :
    IntegrableOn (fun x ↦ |blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      (Metric.closedBall (0 : Cover) R) := by
  have hAi : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hA
  apply Integrable.of_bound (((measurable_blowupCharacteristic hE c r).sub hAi).abs.aestronglyMeasurable) 2
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_abs]
  have hB : |A.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
    by_cases hx : x ∈ A <;> simp [Set.indicator,hx]
  exact (abs_sub _ _).trans (by linarith [blowupCharacteristic_bound E c r x])

theorem isMinimizerAt_blowup_competitor_bound {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0))
    {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b ≤ R) (hL : 0 ≤ L)
    (hper : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) : θ*a^2 ≤ L := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_scaled_set_replacement hV hE hmin hμ
  obtain ⟨K,hKpos,hK⟩ := smoothTransition_exists_deriv_bound
  let D : ℕ → ℝ := fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
    |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|
  have hsmall : ∀ᶠ i in atTop, r i*b < 1/4 ∧ (r i*b)^3*(Real.pi*8/3) < η := by
    have hs1 : Tendsto (fun i ↦ r i*b) atTop (𝓝 0) := by simpa using hrlim.mul_const b
    have hs2 : Tendsto (fun i ↦ (r i*b)^3*(Real.pi*8/3)) atTop (𝓝 0) := by
      simpa using (hs1.pow 3).mul_const (Real.pi*8/3)
    exact (hs1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).and
      (hs2.eventually (gt_mem_nhds hη))
  have hineq : ∀ᶠ i in atTop,
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) (r i*a))/(r i)^2 ≤
        L+2*K*b*(D i+r i)/(b^2-a^2)+C*r i*b^3 := by
    filter_upwards [hsmall] with i hi
    have herr : (∫ x in Metric.ball (0 : Cover) b,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < D i+r i := by
      have hm := setIntegral_mono_set (blowup_error_integrable hE hA cubeCenter (r i) R)
        (ae_of_all _ fun x ↦ abs_nonneg _)
        ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)).eventuallyLE)
      dsimp only [D]
      exact lt_of_le_of_lt hm (lt_add_of_pos_right _ (hr i))
    have hh := hcomp A B hA hB a b L K (r i) (D i+r i) ha hab (hr i) hi.1 hi.2 hL hK hper hAB herr
    apply (div_le_iff₀ (sq_pos_of_pos (hr i))).mpr
    apply hh.trans_eq
    ring
  have hm := density_scaled_mass_tendsto hθ r hr hrlim ha
  have hlim : Tendsto (fun i ↦ L+2*K*b*(D i+r i)/(b^2-a^2)+C*r i*b^3) atTop (𝓝 L) := by
    have hh := ((tendsto_const_nhds (x := L)).add
      (((tendsto_const_nhds (x := 2*K*b)).mul (hconv.add hrlim)).div_const (b^2-a^2))).add
        (((tendsto_const_nhds (x := C)).mul hrlim).mul_const (b^3))
    simpa only [zero_add,mul_zero,zero_mul,zero_div,add_zero] using hh
  exact le_of_tendsto_of_tendsto hm hlim hineq

end CubicTorus

end
end

end

end OAI
