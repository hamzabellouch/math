import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.GlobalDensityConstant
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierRetainedFiniteBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierStepWeak_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem outwardOffset_weak (good : Prop) [Decidable good]
    {Z B C R M κ lam1 lam2 e ξ Cinv hl hh : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh) (hR : 0 < R)
    {a h μ p : TFSpace → ℝ} (ha : Continuous a) (hhc : Continuous h)
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p)
    (hμn : ∀ x, 0 ≤ μ x) (hpn : ∀ x, 0 ≤ p x)
    (hlo : ∀ x, R/2 ≤ ‖x‖ → outerBarrier B (R/2) x ≤ nuclearField Z x+a x)
    (hhi : ∀ x, R/2 ≤ ‖x‖ → nuclearField Z x+a x ≤ C/‖x‖^4)
    (hhcap : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R → nuclearField Z x+h x ≤ C/‖x‖^4)
    (hinv : good → ∀ x, R/2 ≤ ‖x‖ → ‖x‖ < 2*M*R →
      InverseComparisonAt ‖x‖ (nuclearField Z x+h x) (μ x) κ hl hh ξ Cinv)
    (hwa : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource (R/2) μ p x+outerCoefficient (R/2) x*reaction κ (nuclearField Z x+a x)))
    (hwh : good → WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+h x) (fun x => 4*Real.pi*μ x)) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x)
      (fun x => innerSource R μ (addedError good R μ p) x+
        outerCoefficient R x*reaction κ (nuclearField Z x+outwardOffset good a h Z B R M lam1 lam2 x)) := by
  have hM := cal.M_large
  have hlow (x : TFSpace) (hx : (26/25)*R ≤ ‖x‖) (hx' : ‖x‖ < (27/25)*R) :
      outerOffset Z B R x ≤ shiftedCandidates good a h R lam1 lam2 x :=
    outward_lower_overlap good cal.B_pos.le hR cal.shift_small hlo (by linarith) hx'
  have hhigh (x : TFSpace) (hx : M*R < ‖x‖) (hx' : ‖x‖ < 2*M*R) :
      shiftedCandidates good a h R lam1 lam2 x ≤ outerOffset Z B R x :=
    outward_upper_overlap good cal.B_pos.le cal.C_nonneg hR hM cal.shift_order cal.cap_shift hhi
      (fun hg y hy hy' => hhcap hg y (by nlinarith) hy') hx hx'
  have hg := innerSource_locallyIntegrable hμ (addedError_locallyIntegrable good hμ hp R) R
  unfold outwardOffset
  apply cutMaximum_weak_nuclear_of_cover (t := (27/25)*R) (L := M*R)
    (by linarith) (by nlinarith) (by nlinarith) hlow hhigh Z κ hR
    (shiftedCandidates_continuous good ha hhc R lam1 lam2) (outerOffset_continuous Z B hR)
    hg (outerCoefficient_measurable R) (outerCoefficient_bound R) (outerCoefficient_zero R)
  · have hw := outward_region_weak good False cal hR (U := {x : TFSpace | ‖x‖ < (27/25)*R})
      (isOpen_lt continuous_norm continuous_const) (fun x hx => by dsimp at hx; nlinarith)
      (fun h => False.elim h) ha hhc hμ hp hμn hpn hlo hhi hhcap hinv
      (fun x hx hxR => by
        rw [outwardRegionOffset_inner,←nuclear_outerOffset_eq (Z := Z) hxR]
        exact add_le_add_right (outward_lower_overlap good cal.B_pos.le hR cal.shift_small hlo hxR hx) _)
      hwa hwh
    simpa only [outwardRegionOffset_inner] using hw
  · have hopen : IsOpen {x : TFSpace | (26/25)*R < ‖x‖ ∧ ‖x‖ < 2*M*R} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    have hw := outward_region_weak good True cal hR hopen (fun _ hx => hx.2)
      (fun _ x hx => by dsimp at hx; linarith [hx.1]) ha hhc hμ hp hμn hpn hlo hhi hhcap hinv
      (fun x _ hxR => by
        rw [outwardRegionOffset_middle,←nuclear_outerOffset_eq (Z := Z) hxR]
        exact add_le_add_right (le_max_right _ _) _) hwa hwh
    simpa only [outwardRegionOffset_middle] using hw
  · let b := outerOffset Z B R
    let sb := fun x => outerCoefficient R x*reaction κ (nuclearField Z x+b x)
    have hb := outerOffset_continuous Z B hR
    have hsb : LocallyIntegrable sb := by
      simpa only [zero_add] using nuclear_source_locallyIntegrable Z κ hR
        (locallyIntegrable_zero (X := TFSpace) (ε'' := ℝ)) (outerCoefficient_measurable R)
        (outerCoefficient_bound R) (outerCoefficient_zero R) hb
    have hw := (outerOffset_weak_nuclear cal.B_pos hR cal.k_nonneg cal.subsolution Z).mono_set
      (show {x : TFSpace | M*R < ‖x‖} ⊆ {x : TFSpace | R < ‖x‖} from fun x hx => by dsimp at *; nlinarith)
    have hw' : WeakNuclearLowerOn {x : TFSpace | M*R < ‖x‖} Z (fun x => nuclearField Z x+b x) sb :=
      hw.congr_source (fun x hx => by
        have hxR : R ≤ ‖x‖ := by dsimp at hx; nlinarith
        simp only [sb,b,outerCoefficient,ite_eq_left hxR,one_mul])
    apply hw'.source_mono hsb (hg.add hsb)
    intro x hx
    have hxR : R ≤ ‖x‖ := by dsimp at hx; nlinarith
    have hn := addedError_nonneg good (R := R) hμn hpn x
    have hπ := Real.pi_pos
    change innerSource R μ (addedError good R μ p) x+sb x ≤ sb x
    simp only [innerSource,ite_eq_right (not_lt_of_ge hxR),zero_sub]
    nlinarith

end CoulombBarrier

end Work_BarrierStepWeak_barrier_scope

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

def initialDensityConstant : ℝ :=
  (2*Pauli.globalDensityConstant)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*4^(1/5:ℝ)

lemma initialDensityConstant_pos : 0 < initialDensityConstant := by
  unfold initialDensityConstant
  have hc := Pauli.globalDensityConstant_pos
  positivity

lemma initial_density_scale {Z r : ℝ} (hZ : 0 < Z) (hr : 0 < r) :
    ((Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r)^(1/5:ℝ))*(r/Z) =
      initialDensityConstant*(Z*r^3)^(2/5:ℝ) := by
  have hp (a : ℝ) := Real.rpow_pos_of_pos hZ a
  rw [show Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)) =
      (2*Pauli.globalDensityConstant)*Z^(7/3:ℝ) by ring,
    Real.mul_rpow (mul_nonneg (by norm_num) Pauli.globalDensityConstant_pos.le) (hp _).le, ←Real.rpow_mul hZ.le,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr.le,
    Real.mul_rpow hZ.le (pow_nonneg hr.le 3), ←Real.rpow_natCast, ←Real.rpow_mul hr.le]
  norm_num
  unfold initialDensityConstant
  have hZpow : Z^(7/5:ℝ)/Z = Z^(2/5:ℝ) := by
    calc
      _ = Z^(7/5:ℝ)/Z^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hZ]; norm_num
  have hrpow : r^(1/5:ℝ)*r = r^(6/5:ℝ) := by
    calc
      _ = r^(1/5:ℝ)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hr]; norm_num
  calc
    _ = ((2*Pauli.globalDensityConstant)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*4^(1/5:ℝ))*
        (Z^(7/5:ℝ)/Z)*(r^(1/5:ℝ)*r) := by ring
    _ = _ := by rw [hZpow,hrpow]; ring

lemma initial_density_small_of_nuclear_relation {Z r ε : ℝ}
    (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε) (hrel : Z*r^3 = ε^3)
    (hs : initialDensityConstant*ε^(6/5:ℝ) < 1/20) :
    (Pauli.globalDensityConstant*(Z^(7/3:ℝ)+Z^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r)^(1/5:ℝ) < Z/(20*r) := by
  have hh := initial_density_scale hZ hr
  rw [hrel,←Real.rpow_natCast,←Real.rpow_mul hε.le] at hh
  norm_num at hh
  apply (mul_lt_mul_iff_right₀ (div_pos hr hZ)).mp
  rw [mul_comm (r/Z), hh]
  have he : r/Z*(Z/(20*r)) = (1:ℝ)/20 := by field_simp
  rw [he]
  exact hs

lemma exists_initial_epsilon : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    initialDensityConstant*ε^(6/5:ℝ) < 1/20 := by
  have ht : Tendsto (fun ε : ℝ => initialDensityConstant*ε^(6/5:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuousAt_rpow_const 0 (6/5:ℝ) (Or.inr (by norm_num))).tendsto.const_mul
      initialDensityConstant).mono_left (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have h := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))
  have h1' : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 := Iio_mem_nhds (by norm_num)
  have h1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 := h1'.filter_mono inf_le_left
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,he⟩ := (hpos.and (h1.and h)).exists
  exact ⟨ε,hε,hε1,he⟩

lemma initial_event_cost_small :
    Tendsto (fun r : ℝ => r^(7-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)
      (𝓝[>] 0) (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r^(249/250:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (249/250:ℝ) (Or.inr (by norm_num))).tendsto.mono_left (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 249/250)
  have hh := (hpow.sub (hlog.const_mul 40)).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr 40).ne',Real.log_exp,Real.log_pow]
  have he : r^(249/250:ℝ)-40*(Real.log r*r^(249/250:ℝ)) =
      r^(249/250:ℝ)*(1-40*Real.log r) := by ring
  rw [he,mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  norm_num

lemma coarse_offset_nuclear_ratio {Z s : ℝ} (hZ : 0 < Z) (hs : 0 < s) :
    (3*Z*s^(-4:ℝ))/Z^(7/3:ℝ) = 3*(Z*s^3)^(-4/3:ℝ) := by
  rw [Real.mul_rpow hZ.le (pow_nonneg hs.le 3),←Real.rpow_natCast,←Real.rpow_mul hs.le]
  norm_num only [show (3:ℝ)*(-4/3) = -4 by norm_num]
  have he : Z/Z^(7/3:ℝ) = Z^(-4/3:ℝ) := by
    calc
      _ = Z^(1:ℝ)/Z^(7/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_sub hZ]; norm_num
  calc
    _ = 3*(Z/Z^(7/3:ℝ))*s^(-4:ℝ) := by ring
    _ = _ := by rw [he]; ring_nf

theorem coarse_offset_nuclear_vanishes {ι : Type*} {l : Filter ι}
    {Z s : ι → ℝ} (hZ : ∀ᶠ i in l, 0 < Z i) (hs : ∀ᶠ i in l, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop) :
    Tendsto (fun i => (3*Z i*(s i)^(-4:ℝ))/(Z i)^(7/3:ℝ)) l (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 4/3)).comp hscale
  have ht := hh.const_mul 3
  simp only [mul_zero] at ht
  exact ht.congr' (by filter_upwards [hZ,hs] with i hZi hsi; simpa only [Function.comp_apply,neg_div] using (coarse_offset_nuclear_ratio hZi hsi).symm)

end CoulombAtom

end

end OAI
