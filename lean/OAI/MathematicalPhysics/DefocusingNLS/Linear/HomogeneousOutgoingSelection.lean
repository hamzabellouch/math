import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRadialRows
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingDefectEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalColumnJets
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingPropagation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialRiccati
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogEquation

namespace OAI

/-! # Selection of the outgoing plane by the top radial derivative -/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "V₄" => V × V
local notation "End" => V →L[ℂ] V

theorem homogeneousPhysicalOutgoing_selection
    (νp νm eta : ℂ) (m n : ℕ) (Q : ℝ → ℂ) (Z Zp Zm : ℝ → V₄)
    (R₀ L c : ℝ) (hR₀ : 0 < R₀) (hL : Real.log R₀ ≤ L) (hc : 0 < c)
    (hν : νp.re = νm.re)
    (hbeta : -6 ≤ (n : ℝ) - (11 + νp.re))
    (hgap : 0 < ((n + 1 : ℕ) : ℝ) + n - (11 + νp.re))
    (hQ : ContinuousOn Q (Ici R₀))
    (hZ : ∀ r, R₀ ≤ r → HasDerivAt Z
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Z r)) r)
    (hZp : ∀ r, R₀ ≤ r → HasDerivAt Zp
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zp r)) r)
    (hZm : ∀ r, R₀ ≤ r → HasDerivAt Zm
      (spectralPhysicalCircularField νp νm eta m (Q r) r (Zm r)) r)
    (hU : ContDiffOn ℝ ∞ (fun r => spectralPhysicalValueMap (Z r)) (Ioi 0))
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖spectralPhysicalValueMap (Z r)‖ ≤ M)
    (hL2p : IntegrableOn (fun r => r ^ 11 *
      ‖(iteratedDeriv (n + 1) (fun s => spectralPhysicalValueMap (Z s)) r).1‖ ^ 2) (Ioi 0))
    (hL2m : IntegrableOn (fun r => r ^ 11 *
      ‖(iteratedDeriv (n + 1) (fun s => spectralPhysicalValueMap (Z s)) r).2‖ ^ 2) (Ioi 0))
    (hB : ContDiffOn ℝ ∞ homogeneousLogRadialDamping (Ioi L))
    (hC : ContDiffOn ℝ ∞
      (homogeneousLogRadialStiffness νp νm eta m (fun t => Q (Real.exp t))) (Ioi L))
    (hrow : ∀ᶠ t in atTop, ∀ w : V,
      c * Real.exp (2 * (n : ℝ) * t) * ‖w‖ ≤
      ‖(homogeneousEulerRows homogeneousLogRadialDamping
        (homogeneousLogRadialStiffness νp νm eta m (fun s => Q (Real.exp s)))
        (n + 1)).2 t w‖)
    (hrem : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in atTop,
      spectralValueDet (spectralPhysicalValueMap (Zp (Real.exp t)))
        (spectralPhysicalValueMap (Zm (Real.exp t))) ≠ 0 ∧
      ‖spectralTwoColumns
        (homogeneousEulerDeriv (fun s => spectralPhysicalValueMap (Zp (Real.exp s))) (n + 1) t)
        (homogeneousEulerDeriv (fun s => spectralPhysicalValueMap (Zm (Real.exp s))) (n + 1) t) *
        spectralValueInverse (spectralPhysicalValueMap (Zp (Real.exp t)))
          (spectralPhysicalValueMap (Zm (Real.exp t)))‖ ≤ K)
    (herr : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in atTop,
      ‖spectralJetRobin (Zp r) (Zm r) - r⁻¹ • homogeneousDiagonal νp νm‖ ≤ M / r ^ 3)
    (R : ℝ) (hR : R₀ ≤ R) :
    ∃ a : V, Z R = a.1 • Zp R + a.2 • Zm R := by
  let U := fun r => spectralPhysicalValueMap (Z r)
  let Vd := fun r => spectralPhysicalDerivativeMap (Z r)
  let A := fun r => spectralJetRobin (Zp r) (Zm r)
  let W := homogeneousRadialDefect A U Vd
  let logU := fun t => U (Real.exp t)
  let logV := fun t => Real.exp t • Vd (Real.exp t)
  let up := fun t => spectralPhysicalValueMap (Zp (Real.exp t))
  let um := fun t => spectralPhysicalValueMap (Zm (Real.exp t))
  let dp := fun t => Real.exp t • spectralPhysicalDerivativeMap (Zp (Real.exp t))
  let dm := fun t => Real.exp t • spectralPhysicalDerivativeMap (Zm (Real.exp t))
  let C := homogeneousLogRadialStiffness νp νm eta m (fun t => Q (Real.exp t))
  have hrad (t : ℝ) (ht : L < t) : R₀ ≤ Real.exp t := by
    rw [← Real.exp_log hR₀]
    exact Real.exp_le_exp.mpr (hL.trans ht.le)
  have hlogs (S : ℝ → V₄)
      (hS : ∀ r, R₀ ≤ r → HasDerivAt S
        (spectralPhysicalCircularField νp νm eta m (Q r) r (S r)) r)
      (t : ℝ) (ht : L < t) :=
    homogeneousPhysicalRadial_logEquation νp νm eta m Q
      (fun r => spectralPhysicalValueMap (S r))
      (fun r => spectralPhysicalDerivativeMap (S r)) t
      (homogeneousPhysicalState_pair_derivatives νp νm eta m _ S _ (hS _ (hrad t ht))).1
      (homogeneousPhysicalState_pair_derivatives νp νm eta m _ S _ (hS _ (hrad t ht))).2
  have hAscale (t : ℝ) : spectralRobinOperator (up t) (um t) (dp t) (dm t) =
      Real.exp t • A (Real.exp t) :=
    homogeneousRobin_smul_derivatives _ _ _ _ _
  obtain ⟨K, hK, hremK⟩ := hrem
  obtain ⟨M, hM, hMbound⟩ := hbounded
  let T := (homogeneousEulerRows homogeneousLogRadialDamping C (n + 1)).2
  let Rem := fun t => spectralTwoColumns (homogeneousEulerDeriv up (n + 1) t)
    (homogeneousEulerDeriv um (n + 1) t) * spectralValueInverse (up t) (um t)
  have hid : ∀ᶠ t in atTop, homogeneousEulerDeriv logU (n + 1) t =
      T t (Real.exp t • W (Real.exp t)) + Rem t (U (Real.exp t)) := by
    filter_upwards [hremK, eventually_gt_atTop L] with t ht hLt
    have hh := homogeneousEulerRows_defect_identity homogeneousLogRadialDamping C
      up um dp dm logU logV L hB hC
      (fun t ht => (hlogs Zp hZp t ht).1) (fun t ht => (hlogs Zm hZm t ht).1)
      (fun t ht => (hlogs Zp hZp t ht).2) (fun t ht => (hlogs Zm hZm t ht).2)
      (fun t ht => (hlogs Z hZ t ht).1) (fun t ht => (hlogs Z hZ t ht).2)
      (n + 1) t hLt ht.1
    have hw : logV t - spectralRobinOperator (up t) (um t) (dp t) (dm t) (logU t) =
        Real.exp t • W (Real.exp t) := by
      rw [hAscale]
      simp only [logV, logU, W, homogeneousRadialDefect, smul_apply, smul_sub]
    simpa only [hw] using hh
  have hcomp := homogeneousOutgoingRows_physical_comparison U W T Rem n c K M
    hU hc hK hM hMbound hrow (hremK.mono fun _ h => h.2) hid
  have hd : ∀ᶠ r in atTop, spectralValueDet (spectralPhysicalValueMap (Zp r))
      (spectralPhysicalValueMap (Zm r)) ≠ 0 := by
    filter_upwards [Real.tendsto_log_atTop.eventually hremK,
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.exp_log hr0] using hr.1
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hd
  let R₂ := max R₀ R₁
  have hW (r : ℝ) (hr : R₂ ≤ r) : HasDerivAt W
      (-(homogeneousRadialDamping r + A r) (W r)) r := by
    have hr₀ := (le_max_left R₀ R₁).trans hr
    have hp := homogeneousPhysicalState_pair_derivatives νp νm eta m _ Zp r (hZp r hr₀)
    have hm := homogeneousPhysicalState_pair_derivatives νp νm eta m _ Zm r (hZm r hr₀)
    have hu := homogeneousPhysicalState_pair_derivatives νp νm eta m _ Z r (hZ r hr₀)
    exact homogeneousRadialDefect_from_columns _ _ _ _ _ _ U Vd r hp.1 hm.1 hp.2 hm.2
      (hR₁ r ((le_max_right R₀ R₁).trans hr)) hu.1 hu.2
  have hwzero := homogeneousOutgoingDefect_eventually_zero νp νm hν A W
    (fun r => (iteratedDeriv (n + 1) U r).1)
    (fun r => (iteratedDeriv (n + 1) U r).2) R₂ n (4 / c ^ 2)
    ((4 / c ^ 2) * (K * M) ^ 2) (n + 1)
    (hR₀.trans_le (le_max_left _ _)) (by positivity) hbeta hgap hW herr hcomp
    (hL2p.mono_set (Ioi_subset_Ioi (by positivity : 0 ≤ R₂)))
    (hL2m.mono_set (Ioi_subset_Ioi (by positivity : 0 ≤ R₂)))
  have hout : ∀ᶠ r in atTop, ∃ a : V, Z r = a.1 • Zp r + a.2 • Zm r := by
    filter_upwards [hwzero, hd] with r hw hd'
    apply (spectralJetRobin_plane _ _ _ hd').1
    exact sub_eq_zero.mp hw
  obtain ⟨T', ⟨a, ha⟩, hT'⟩ := (hout.and (eventually_ge_atTop R)).exists
  refine ⟨a, homogeneousPhysicalOutgoingPlane_backward νp νm eta m Q Z Zp Zm R T'
    (hR₀.trans_le hR) hT' ?_ ?_ ?_ ?_ a ha⟩
  · exact hQ.mono (fun _ hr => hR.trans hr.1)
  · exact fun _ hr => hZ _ (hR.trans hr.1)
  · exact fun _ hr => hZp _ (hR.trans hr.1)
  · exact fun _ hr => hZm _ (hR.trans hr.1)

end DefocusingNLS

end OAI
