import OAI.MeasureTheory.Falconer.Angular.ControlledAngularGain
import OAI.MeasureTheory.Falconer.Estimates.PlanarLossBudget
import OAI.MeasureTheory.Falconer.Geometry.ActiveCoverScale
import OAI.MeasureTheory.Falconer.Slicing.GaussianMomentScale
import OAI.MeasureTheory.Falconer.Estimates.DyadicLossAbsorption
import OAI.MeasureTheory.Falconer.Angular.OriginalDirectionChart

namespace OAI

/-! # Uniform nonendpoint angular decay on a fixed original direction chart -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_chart_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C ρ : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hstable : (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2)
    (hchart : 4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  obtain ⟨η,δF,hη,hδF,hgain⟩ := controlled_dyadic_angular_gain hpublished hq hq' hqt ht hC
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t q
  let κ₀ := η/100
  let ε := κ₀/2
  let c := κ₀/2
  let M := (h+2:ℝ)*(2*ρ)+1
  let Z := M+1
  let V := (2*Z)^h
  let a₀ := 4+8*(h:ℝ)
  let D := 1+2*(1/4)+C*M
  let B₀ := (2:ℝ)^h*gaussianLocalBandConstant (h+1) ρ^h
  have hκ : 0 < κ₀ := by dsimp [κ₀]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hεκ : ε < κ₀ := by dsimp [ε]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 1 ≤ V := by
    apply one_le_pow₀
    change 1 ≤ 2*(M+1)
    linarith
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+1) hρ
    dsimp [B₀]
    positivity
  have hplan := eventually_gaussian_planar_loss_budget hη hV ha₀ (t-(h:ℝ))
    (q-(h:ℝ)) ((2*D)^h) (4*(1+2*(2:ℝ)^h+1))
  have hdepth := eventually_dyadic_loss_absorption hεκ Cm
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(κ₀-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop (1/B₀))
  obtain ⟨δ₁,hδ₁,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp
      (hplan.and (hdepth.and habs))
  refine ⟨ε,c,min δF (min δ₁ (min ρ 1)),hε,hc,
    lt_min hδF (lt_min hδ₁ (lt_min hρ (by norm_num))),?_⟩
  intro N κ _ _ μ ν _ _ w₀ E J a hδsmall hν hμ hμmass hνmass hμball hνball
    hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-κ₀)
  let L : ℝ := δ^(-ε)
  let Nc : ℝ := δ^(-q-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_left _ _)) |>.le
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_right _ _)) |>.le
  obtain ⟨hp,⟨_,hd⟩,ha⟩ := hready ⟨hδ,hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  rcases hp with ⟨_,hlarge,hH,hpcoef,hqcoef,hlow,hcoverScale⟩
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 0 < K := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := by linarith
  have hCmL : 0 ≤ Cm*L := mul_nonneg hCm.le hL0
  have hcard : ((N+1:ℕ):ℝ)*(Cm*L) ≤ K := by
    rw [dyadic_log_depth N] at hd
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hd
  have hCK : Cm*L ≤ K := by
    have hN : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left hCmL hN).trans hcard
  have hpair : ∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,Measure.quasiMeasurePreserving_snd.ae hν]
      with u hu hv
    exact sphere_chart_pair_inner_nonnegative u.1 u.2 w₀ (hu.trans hρhalf) (hv.trans hρhalf)
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+1) (by omega) (sphere_norm w₀)
  have hchartδ : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hδρ (by positivity : 0 ≤ 4*(h:ℝ))]
  have hbox : (1/4)*((h+2:ℝ)*(2*ρ)+1)+δ ≤ Z := by
    change (1/4)*M+δ ≤ M+1
    nlinarith
  have hactive : K^11*(Nc*(2*(δ+(2*(1/4))*δ+(C*δ)*M))^h) ≤ δ^(-(q-(h:ℝ))-η) := by
    have hh := gaussian_active_cover_scale h hδ hδ1 hεκ.le hD.le (le_refl Nc)
    have hr : δ+(2*(1/4))*δ+(C*δ)*M = D*δ := by dsimp [D]; ring
    rw [hr]
    exact hh.trans hcoverScale
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hg := hgain N κ μ ν w₀ B E J a ρ L L K (Cm*L) Nc Z a₀
    (hδsmall.trans_le (min_le_left _ _)) hρ.le hδρ hB hν hstable hchartδ hμ hμmass hνmass
    hL0 hL0 hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hZ hCP hCD hCM
    hcard hCK hlarge hbox ha₀ hH (le_refl a₀) hpcoef hqcoef hlow hactive
    hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+1) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^κ₀ := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ gaussianLocalBandConstant (h+1) ρ^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le κ₀),mul_assoc] using hr
  have habs' : (1/B₀)*δ^κ₀ ≤ δ^c := by
    have hh := rpow_absorb_constant (t := -κ₀) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^κ₀ := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs'

end Falconer

end OAI
