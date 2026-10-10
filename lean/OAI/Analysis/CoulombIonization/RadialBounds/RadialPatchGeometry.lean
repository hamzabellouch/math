import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.TailParticleCount
import OAI.Analysis.CoulombIonization.Variational.FreshPatchBudget

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

def coreFirstRadialCut (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    Fin 2 → SmoothMultiplier spaceDirections :=
  ![radialOutside y ht hb,radialInside y ht hb]

lemma coreFirstRadialCut_partition (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) : ∑ a, (coreFirstRadialCut y ht hb a).value x^2 = 1 := by
  simpa only [Fin.sum_univ_two,coreFirstRadialCut,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,radialInside,radialOutside] using
    Real.sin_sq_add_cos_sq (radialPhase y t b x)

lemma coreFirstRadialCut_error (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    spatialErrorWeight (coreFirstRadialCut y ht hb) = spatialErrorWeight (radialCut y ht hb) := by
  funext x
  unfold spatialErrorWeight
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.sum_univ_two,coreFirstRadialCut,radialCut,Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact add_comm _ _

def radialPatchCore (y : Space) (t : ℝ) : Set Space := {x | t ≤ ‖x-y‖}

def radialPatchRetention (L : ℕ) (y : Space) (t b : ℝ) : OuterCutRetention L :=
  fun _ _ u => Finset.univ.filter (fun i => ‖u i-y‖ < t-7*b)

lemma radialPatchRetention_measurable (L : ℕ) (y : Space) (t b : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (i : Fin (cutOutNumber c)) :
    MeasurableSet {u | i ∈ radialPatchRetention L y t b c s u} := by
  simp only [radialPatchRetention,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (isOpen_lt (((continuous_apply i).sub continuous_const).norm) continuous_const).measurableSet

lemma coreFirstRadialCut_core_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (hx : x ∉ radialPatchCore y t) :
    (coreFirstRadialCut y ht hb 0).value x = 0 := by
  have hx' : ‖x-y‖ < t := lt_of_not_ge hx
  simp only [coreFirstRadialCut,Matrix.cons_val_zero,radialOutside,
    radialPhase_zero ht hb hx'.le,Real.sin_zero]

lemma coreFirstRadialCut_core_deriv_zero (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (hx : x ∉ radialPatchCore y t) (a : Fin 3) :
    lineDeriv ℝ (coreFirstRadialCut y ht hb 0).value x (spaceDirections a) = 0 := by
  have hx' : ‖x-y‖ < t := lt_of_not_ge hx
  change lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x _ = 0
  rw [radial_sin_derivative,radialPhase_derivative_zero_off_collar ht hb
    (fun h => (not_le.mpr hx') h.1),mul_zero]

lemma scaledRealPacket_tsupport {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) : tsupport (scaledRealPacket b g) ⊆ closedBall 0 b := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simpa only [mem_closedBall,dist_zero_right] using (scaledRealPacket_support hb hs hx).le

lemma radialPatch_packet_separation (y : Space) {t b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) :
    Disjoint (radialPatchCore y t)
      (packetRegion (scaledRealPacket b g) (closedBall y (t-4*b))) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩
  have hw' := scaledRealPacket_tsupport hb hgs hw
  simp only [mem_closedBall,dist_zero_right] at hw'
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh : ‖w+z-y‖ ≤ ‖w‖+‖z-y‖ := by
    simpa only [add_sub_assoc] using norm_add_le w (z-y)
  change t ≤ ‖w+z-y‖ at hx
  linarith

lemma radialPatch_core_distance (y : Space) {t b : ℝ} (hb : 0 < b)
    (a : Space) (ha : a ∈ radialPatchCore y t) (z : Space)
    (hz : z ∈ closedBall y (t-4*b)) : b ≤ ‖a-z‖ := by
  change t ≤ ‖a-y‖ at ha
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh := dist_triangle a z y
  simp only [dist_eq_norm] at hh
  linarith

lemma radialPatch_nuclear_distance {y : Space} {t b : ℝ} (hb : 0 < b)
    (hy : t ≤ ‖y‖) (z : Space) (hz : z ∈ closedBall y (t-4*b)) : b ≤ ‖z‖ := by
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh := norm_sub_norm_le y z
  rw [norm_sub_rev y z] at hh
  linarith

lemma sqrt_three_le_three : Real.sqrt 3 ≤ 3 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg (3:ℝ)]

lemma radialPatch_retained_margin {L : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : i ∈ radialPatchRetention L y t b c s u) :
    ‖u i-y‖+Real.sqrt 3*b ≤ t-4*b := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  linarith

lemma radialPatch_retained_nuclear {L : ℕ} {y : Space} {t b : ℝ} (hb : 0 < b)
    (hy : t ≤ ‖y‖) (c : Fin L → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) (i : Fin (cutOutNumber c))
    (hi : i ∈ radialPatchRetention L y t b c s u) : Real.sqrt 3*b ≤ ‖u i‖ := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  have hh := norm_sub_norm_le y (u i)
  rw [norm_sub_rev y (u i)] at hh
  linarith

lemma radialPatch_retained_core {L : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : i ∈ radialPatchRetention L y t b c s u)
    (a : Space) (ha : a ∈ radialPatchCore y t) : Real.sqrt 3*b ≤ ‖a-u i‖ := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  change t ≤ ‖a-y‖ at ha
  have hh := dist_triangle a (u i) y
  simp only [dist_eq_norm] at hh
  linarith

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

theorem radial_fresh_patch_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) :
    let ht : 0 ≤ t := le_of_lt (lt_trans (by positivity : (0:ℝ) < 7*b) htb)
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let S := radialPatchRetention L y t b
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (orderedCutForm p hp ψ c) s Z lam y (t-4*b) hb (S c s) u) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        b⁻¹^2*neumannRemainderConstant*(∑ c : Fin L → Fin 2,
          ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*formMass (orderedCutForm p hp ψ c))+
        (((2*Real.pi+1)/2)/b)*(∑ c : Fin L → Fin 2,
          (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c))+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
          conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (S c s) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass (orderedCutForm p hp ψ c) s Z lam y (t-4*b) u) := by
  dsimp only
  apply fresh_cut_patch_budget _ _ hψ y (by linarith) hZ hlam hg hcg hgn hr hgs hb
    (radialPatchCore y t)
  · exact coreFirstRadialCut_core_zero y _ hb
  · exact coreFirstRadialCut_core_deriv_zero y _ hb
  · exact radialPatch_packet_separation y hb hgs
  · exact radialPatch_nuclear_distance hb hy
  · exact radialPatch_core_distance y hb
  · exact radialPatchRetention_measurable L y t b
  · exact radialPatch_retained_margin y hb
  · exact radialPatch_retained_nuclear hb hy
  · exact radialPatch_retained_core y hb

lemma weightedParticleCount_const_mul {L : ℕ} (ψ : FormVector L) (c : ℝ) (w : Space → ℝ) :
    weightedParticleCount ψ (fun x => c*w x) = c*weightedParticleCount ψ w := by
  simp only [weightedParticleCount,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma radial_fresh_ims_bound {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    (1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight (coreFirstRadialCut y ht hb)) ≤
      (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2*
        weightedParticleCount ψ (fun x => if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then 1 else 0) := by
  classical
  rw [coreFirstRadialCut_error]
  have hm : Measurable (fun x : Space => if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then (1:ℝ) else 0) :=
    measurable_const.ite
      ((isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)).inter
        (isClosed_le ((continuous_id.sub continuous_const).norm) continuous_const)).measurableSet
      measurable_const
  have hi (s : Spins L) (i : Fin L) : Integrable (fun x : Configuration L =>
      (3*(Real.pi*smoothTransitionBound/b)^2)*
        (if t ≤ ‖x i-y‖ ∧ ‖x i-y‖ ≤ t+b then (1:ℝ) else 0)*‖ψ.value s x‖^2) := by
    have hi := weightedParticleCount_integrable hψ hm (B := 1)
      (fun x => by split_ifs <;> norm_num) s i
    convert hi.const_mul (3*(Real.pi*smoothTransitionBound/b)^2) using 1
    ext x
    ring
  have hh := weightedParticleCount_mono
    (fun s i => spatial_error_weight_integrable (radialCut y ht hb) hψ s i)
    hi (radialCut_error_bound y ht hb)
  rw [weightedParticleCount_const_mul] at hh
  nlinarith

end CoulombAtom

end

end OAI
