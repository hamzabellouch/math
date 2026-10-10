import OAI.MeasureTheory.Falconer.Estimates.ControlledEndpointGain
import OAI.MeasureTheory.Falconer.Estimates.EndpointSphericalPreparation
import OAI.MeasureTheory.Falconer.Angular.EndpointAngularParameters
import OAI.MeasureTheory.Falconer.Slicing.GaussianMomentScale
import OAI.MeasureTheory.Falconer.Estimates.EndpointApplicationNumerics
import OAI.MeasureTheory.Falconer.Angular.OriginalDirectionChart

namespace OAI

/-! # Uniform endpoint angular decay on a small original direction cap -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_chart_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsProbabilityMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  let s : ℝ := t-(h:ℝ)
  let a : ℝ := (2*s-3)/12
  have hs : 3/2 < s := by dsimp [s]; linarith
  have hs' : s < 2 := by dsimp [s]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : a < 1/2 := by dsimp [a]; linarith
  have hgap : 0 < 2*s-3-6*a := by dsimp [a]; linarith
  obtain ⟨ε₀,c₁,c₂,hε₀,hc₁,hc₂,Np,hprep⟩ := endpoint_spherical_preparation (h := h) hLW hζ ha
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t (h+1:ℝ)
  let Mrow : ℝ := (h+3:ℝ)*(2*ρ)+1
  let Z : ℝ := Mrow+1
  let V : ℝ := (2*Z)^h
  let a₀ : ℝ := 4+4*(h:ℝ)
  let D : ℝ := 1+2*(1/4)+C*Mrow
  let B₀ : ℝ := (2:ℝ)^h*gaussianLocalBandConstant (h+2) ρ^h
  have hMrow : 0 < Mrow := by dsimp [Mrow]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+2) hρ
    dsimp [B₀]
    positivity
  obtain ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,Ns,hscalar⟩ :=
    exists_endpoint_angular_parameters hε₀ hc₁ hc₂ hgap ha' Cm
      (4*(1+2*(2:ℝ)^h+1)) V ((4*a₀)^s) ((2*D)^h) C (h:ℝ)
  have hcut := dyadic_inverse_tendsto.eventually
    ((eventually_const_mul_rpow_lt (show u/2 < u by linarith) (1/B₀)).and
      (Ioc_mem_nhdsGT hρ))
  obtain ⟨Nc,hcut⟩ := eventually_atTop.mp hcut
  refine ⟨ε,u/2,hε,by positivity,Np+Ns+Nc,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-u)
  let L : ℝ := δ^(-ε)
  let Ncover : ℝ := δ^(-(h+1:ℝ)-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨habs,hδρ'⟩ := hcut N (by omega)
  have hδρ : δ ≤ ρ := hδρ'.2
  have hδ1 : δ ≤ 1 := hδρ.trans (hρsmall.trans (by norm_num))
  obtain ⟨hcard,hlarge,hcoef,hbase,hmass,hbad,hcount,herror,hbudget⟩ := hscalar N (by omega)
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 1 ≤ K := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -u ≤ 0 by linarith)
  have hCK : Cm*L ≤ K := by
    have hN1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left (by positivity : 0 ≤ Cm*L) hN1).trans hcard
  have hloss : L ≤ ((2:ℝ)^N)^ε₀ := by
    rw [dyadic_loss_conversion]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεε₀.le)
  have hcap : ∀ᵐ (w : Sphere (h+3)) ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8 := by
    filter_upwards [hν] with w hw
    exact hw.trans hρsmall
  obtain ⟨G,hG,hpairCost,htripleCost⟩ := hprep N (by omega) ν hcap
    (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
      (by simpa only [Nat.cast_add,Nat.cast_one] using
        (mul_le_mul_of_nonneg_right hloss
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) (h+1:ℝ))))))
    (fun w r hr hr1 => (hslab w r (by simpa only [one_div] using hr) hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss
        (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
  let ν₀ : Measure (Space (h+2)) := Measure.map gnomonicCoordinates ν
  have hpos : ∀ᵐ (w : Sphere (h+3)) ∂ν, 0 < (w:Space (h+3)) 0 := by
    filter_upwards [hcap] with w hw
    have hh := gnomonic_cap_first_coordinate w (hw.trans (by norm_num : (1/8:ℝ) ≤ 1/2))
    linarith
  have hνeq : Measure.map gnomonicChart ν₀ = ν := gnomonicCoordinates_map_recover ν hpos
  have hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1 := by
    filter_upwards [small_gnomonic_cap_law ν hcap] with p hp
    linarith
  have hpair : ∀ᵐ w : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (w.1:Space (h+3)) (w.2:Space (h+3)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcap,
      Measure.quasiMeasurePreserving_snd.ae hcap] with w hw hv
    exact sphere_chart_pair_inner_nonnegative w.1 w.2 (gnomonicChart (0 : Space (h+2)))
      (hw.trans (by norm_num)) (hv.trans (by norm_num))
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+2) (by omega)
    (sphere_norm (gnomonicChart (0 : Space (h+2))))
  have hKpow (j : ℕ) : K^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hbox : volume (coordinateBox h ((1/4)*Mrow+δ)) ≤ ENNReal.ofReal V := by
    rw [coordinateBox_volume (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    change 2*((1/4)*Mrow+δ) ≤ 2*(Mrow+1)
    nlinarith
  have hpc : (∫⁻ A, endpointPairCost ν₀ δ G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₁) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointPairCost,dyadic_inverse_rpow] using hpairCost
  have htc : (∫⁻ A, endpointTripleCost ν₀ δ (2*δ^a) G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₂) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointTripleCost,dyadic_inverse_rpow] using htripleCost
  have hrow := endpoint_selection_row_budget hδ hV _ _ _ hbox hpc htc hbase
  have hactive := endpoint_active_cover_power hδ hδ1 hεu.le hC hρ.le hcount
  have hsmall := endpoint_stable_small hδρ hstable
  have hbad' := endpoint_bad_mass_ennreal hδ hbad
  have hcoef' : K^6*(4*a₀)^s ≤ δ^(-(40*u)) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul,mul_neg,mul_comm] using hcoef
  have hmass' : δ^(40*u) ≤ (δ^(2*u))^3/(2*(K^6)^5) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul] using hmass
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Ncover := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  have hg := controlled_endpoint_angular_gain μ ν ν₀ hνeq B (gnomonicChart (0 : Space (h+2)))
    E J v G hG hρ.le hδρ hB hν hstable hsmall hμ hν₀ hμmass (by simp)
    (by positivity : 0 ≤ L) (by positivity : 0 ≤ L) (by linarith : (h:ℝ) < t)
    hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hCP hCD hCM hcard hCK hlarge
    ha.le hC (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _)
    ha₀ le_rfl hbad' hmass' hactive hcoef' herror
    (by simpa only [neg_mul] using hbudget) hrow hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+2) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^u := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (pow_nonneg hlocal.le h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le u),mul_assoc] using hr
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^u := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs.2.le

end Falconer

end OAI
