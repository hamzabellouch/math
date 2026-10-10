import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.Sphere
import OAI.Analysis.VlasovMaxwell.Geometry.CollisionLabels

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.receiver_integrable {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : Vec → G} (hg : IntegrableOn g (ball (F.flow z T).1 (T-s))) :
    IntegrableOn (fun w => (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) •
      g (receiverRadial F.flow z s w)) (receiverRadialDomain s T) := by
  have hd : ∀ w ∈ receiverRadialDomain s T,
      HasFDerivWithinAt (receiverRadial F.flow z s)
        (fderiv ℝ (receiverRadial F.flow z s) w) (receiverRadialDomain s T) w := by
    intro w hw
    exact (F.receiver_differential hs.1 z hw).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hi : IntegrableOn g (receiverRadial F.flow z s '' receiverRadialDomain s T) := by
    rw [F.receiver_image hs z]
    exact hg.congr_set_ae (sdiff_null_ae_eq_self (measure_singleton (F.flow z s).1))
  have hh := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (isOpen_receiverRadialDomain s T).measurableSet hd (F.receiver_injective hs z) g).mp hi
  apply hh.congr_fun _ (isOpen_receiverRadialDomain s T).measurableSet
  intro w hw
  dsimp only
  rw [F.receiver_jacobian hs.1 z hw]

lemma PhaseFlowOn.receiver_polar_integral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : Vec → G} (hg : IntegrableOn g (ball (F.flow z T).1 (T-s))) :
    ∫ y in ball (F.flow z T).1 (T-s), g y =
      ∫ n : Sphere, ∫ r in Ioo (0 : ℝ) (T-s),
        (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) •
          g ((F.flow z (s+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
  let H : Vec → G := (receiverRadialDomain s T).indicator
    (fun w => (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) • g (receiverRadial F.flow z s w))
  have hH : Integrable H := (integrable_indicator_iff (isOpen_receiverRadialDomain s T).measurableSet).mpr
    (F.receiver_integrable hs z hg)
  rw [F.receiver_integral hs z g,← integral_indicator (isOpen_receiverRadialDomain s T).measurableSet]
  change (∫ w, H w) = _
  rw [integral_polar hH]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  let k : ℝ → G := fun r => (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) • g ((F.flow z (s+r)).1-r • n.1)
  have hn : ‖n.1‖=1 := (mem_sphere_zero_iff_norm.mp n.2)
  have he : ∀ r ∈ Ioi (0 : ℝ), r^2 • H (r • n.1) = (Iio (T-s)).indicator k r := by
    intro r hr
    have hnorm : ‖r • n.1‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
    have hd : r • n.1 ∈ receiverRadialDomain s T ↔ r < T-s := by
      change 0 < ‖r • n.1‖ ∧ s+‖r • n.1‖ < T ↔ _
      rw [hnorm]
      constructor
      · intro h; linarith [h.2]
      · intro h; exact ⟨hr,by linarith⟩
    by_cases h : r < T-s
    · rw [show H (r • n.1) = _ from Set.indicator_of_mem (hd.mpr h) _,Set.indicator_of_mem (show r ∈ Iio (T-s) from h)]
      dsimp only [k,receiverRadial]
      have hnsmul : r⁻¹ • (r • n.1)=n.1 := by
        rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (show 0<r from hr)),one_smul]
      rw [hnorm,hnsmul,smul_smul]
    · rw [show H (r • n.1) = 0 from Set.indicator_of_notMem (fun hh => h (hd.mp hh)) _,smul_zero,
        Set.indicator_of_notMem (show r ∉ Iio (T-s) from h)]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Iio (T-s)).indicator k r := setIntegral_congr_fun measurableSet_Ioi he
    _ = ∫ r in Ioi (0 : ℝ) ∩ Iio (T-s), k r := setIntegral_indicator measurableSet_Iio
    _ = _ := by rfl

def labelOccupation (f₀ : Phase → ℝ) (H : Phase → Set ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (f₀ z) * volume (H z)

lemma PhaseFlowOn.label_occupation_rate_bound {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) (f₀ : Phase → ℝ) {H : Phase → Set ℝ} {c a b : ℝ}
    (hH : ∀ z, MeasurableSet (H z))
    (hsub : ∀ z, H z ⊆ branchDomain F.flow zX z T)
    (hder : ∀ z s, s ∈ H z → c ≤ branchRate F.flow zX z T s)
    (himage : ∀ z, branchTime F.flow zX z T '' H z ⊆ Icc a b) :
    ENNReal.ofReal c * labelOccupation f₀ H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f₀ z) := by
  have hnc : ∀ᵐ z ∂(volume : Measure Phase), z ∉ collisionLabels F.flow zX T :=
    (ae_iff.mpr (by simpa using F.collision_null zX))
  calc
    _ = ∫⁻ z, ENNReal.ofReal c * (ENNReal.ofReal (f₀ z) * volume (H z)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ∫⁻ z, ENNReal.ofReal (b-a) * ENNReal.ofReal (f₀ z) := by
      apply lintegral_mono_ae
      filter_upwards [hnc] with z hz
      have hne : ∀ s ∈ H z, (F.flow zX s).1 ≠ (F.flow z s).1 := by
        intro s hs he
        exact hz ⟨s,(hsub z hs).1,he.symm⟩
      have hb := F.branch_duration_bound zX z (hH z) (hsub z) hne (hder z) (himage z)
      calc
        _ = ENNReal.ofReal (f₀ z) * (ENNReal.ofReal c * volume (H z)) := by ac_rfl
        _ ≤ ENNReal.ofReal (f₀ z) * ENNReal.ofReal (b-a) := by gcongr
        _ = _ := mul_comm _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

def branchDirection (α : Phase → ℝ → Phase) (zX zY : Phase) (T s : ℝ) : Vec :=
  let t := branchTime α zX zY T s
  (t-s)⁻¹ • ((α zX t).1-(α zY s).1)

lemma PhaseFlowOn.branchDirection_norm {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    ‖branchDirection F.flow zX zY T s‖ = 1 := by
  have ht := (F.branch_time_mem zX zY hs hne).1
  have hr := (F.branch_spec zX zY hs).2
  dsimp only [branchDirection]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sub_pos.mpr ht)),← hr]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht))

lemma PhaseFlowOn.branchRate_pos {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) : 0 < branchRate F.flow zX zY T s := by
  have hn := F.branchDirection_norm zX zY hs hne
  have hpos (v : Vec) : 0 < 1-dot (branchDirection F.flow zX zY T s) (velocity v) := by
    have hd := dot_le_norm (branchDirection F.flow zX zY T s) (velocity v)
    rw [hn,one_mul] at hd
    linarith [norm_velocity_lt_one v]
  exact div_pos (hpos _) (hpos _)

lemma PhaseFlowOn.branchRate_lower_bound {E B : Field} {T s δ Δ : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
    (hsource : δ ≤ 1-dot (branchDirection F.flow zX zY T s) (velocity (F.flow zY s).2))
    (hreceiver : 1-dot (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2) ≤ Δ) :
    δ/Δ ≤ branchRate F.flow zX zY T s := by
  have hn := F.branchDirection_norm zX zY hs hne
  have hD : 0 < 1-dot (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2) := by
    have hd := dot_le_norm (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)
    rw [hn,one_mul] at hd
    linarith [norm_velocity_lt_one (F.flow zX (branchTime F.flow zX zY T s)).2]
  apply (div_le_div_iff₀ hΔ hD).mpr
  change δ * (1-dot (branchDirection F.flow zX zY T s)
    (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)) ≤
    (1-dot (branchDirection F.flow zX zY T s) (velocity (F.flow zY s).2))*Δ
  nlinarith

lemma PhaseFlowOn.label_occupation_angular_bound {E B : Field} {T δ Δ a b : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (f₀ : Phase → ℝ) {H : Phase → Set ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 < Δ) (hH : ∀ z, MeasurableSet (H z))
    (hsub : ∀ z, H z ⊆ branchDomain F.flow zX z T)
    (hsource : ∀ z s, s ∈ H z → δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
    (hreceiver : ∀ z s, s ∈ H z → 1-dot (branchDirection F.flow zX z T s)
      (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
    (himage : ∀ z, branchTime F.flow zX z T '' H z ⊆ Icc a b) :
    ENNReal.ofReal (δ/Δ) * labelOccupation f₀ H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f₀ z) := by
  have hnc : ∀ᵐ z ∂(volume : Measure Phase), z ∉ collisionLabels F.flow zX T :=
    (ae_iff.mpr (by simpa using F.collision_null zX))
  calc
    _ = ∫⁻ z, ENNReal.ofReal (δ/Δ) * (ENNReal.ofReal (f₀ z) * volume (H z)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ∫⁻ z, ENNReal.ofReal (b-a) * ENNReal.ofReal (f₀ z) := by
      apply lintegral_mono_ae
      filter_upwards [hnc] with z hz
      have hne : ∀ s ∈ H z, (F.flow zX s).1 ≠ (F.flow z s).1 := by
        intro s hs he
        exact hz ⟨s,(hsub z hs).1,he.symm⟩
      have hb := F.branch_duration_bound zX z (hH z) (hsub z) hne
        (fun s hs => F.branchRate_lower_bound zX z (hsub z hs) (hne s hs) hδ hΔ
          (hsource z s hs) (hreceiver z s hs)) (himage z)
      calc
        _ = ENNReal.ofReal (f₀ z) * (ENNReal.ofReal (δ/Δ) * volume (H z)) := by ac_rfl
        _ ≤ ENNReal.ofReal (f₀ z) * ENNReal.ofReal (b-a) := by gcongr
        _ = _ := mul_comm _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end RVM

end

end OAI
