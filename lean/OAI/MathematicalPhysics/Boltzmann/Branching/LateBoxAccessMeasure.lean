import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.AlmostEverywhereGrowth
import OAI.MathematicalPhysics.Boltzmann.Branching.ChartPointLift
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.LargeOutput
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceGrowthBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceBranchingHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallFirstGain

namespace OAI

section

/-! # The expanding boxes used in the finite-horizon growth contradiction -/

noncomputable section

open Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

def lateBox (κ d t : ℝ) : Set (V × V) :=
  {p | ‖p.1-(κ*t) • firstAxis‖ < d*κ*t ∧ ‖p.2‖ < 5}

theorem lateBox_measurable (κ d t : ℝ) : MeasurableSet (lateBox κ d t) := by
  unfold lateBox
  measurability

theorem physicalBlockTarget_subset_lateBox {κ d t Δ : ℝ} {p q : V × V}
    (hp : p ∈ lateBox κ d t) (hq : q ∈ physicalBlockTarget p.1 Δ κ d) :
    q ∈ lateBox κ d (t+Δ) := by
  refine ⟨?_,hq.2⟩
  have he : q.1-(κ*(t+Δ)) • firstAxis =
      (q.1-(p.1+(κ*Δ) • firstAxis))+(p.1-(κ*t) • firstAxis) := by module
  rw [he]
  have hh := norm_add_le (q.1-(p.1+(κ*Δ) • firstAxis)) (p.1-(κ*t) • firstAxis)
  have hb := add_lt_add hq.1 hp.1
  nlinarith

theorem flight_eventually_lateBox {κ d a : ℝ} (hκ : 0 < κ) (hd : 0 < d) (ha : 0 ≤ a)
    {x v : V} (hv : ‖v-κ • firstAxis‖ < d*κ/4) (hv₅ : ‖v‖ < 5) :
    ∃ T : ℝ, a ≤ T ∧ 0 < T ∧ ∀ t, T ≤ t →
      (x+(t-a) • v,v) ∈ lateBox κ d t := by
  let R := ‖x-(κ*a) • firstAxis‖
  let T := max (max a 1) (4*R/(d*κ)+1)
  have hdk : 0 < d*κ := mul_pos hd hκ
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_right a 1).trans (le_max_left _ _))
  refine ⟨T,(le_max_left a 1).trans (le_max_left _ _),hT,?_⟩
  intro t ht
  have hta : a ≤ t := ((le_max_left a 1).trans (le_max_left _ _)).trans ht
  have htt : 0 < t := hT.trans_le ht
  have hR : R < d*κ*t/4 := by
    have hlarge : 4*R/(d*κ)+1 ≤ t := (le_max_right _ _).trans ht
    have hh := (div_lt_iff₀ hdk).mp (show 4*R/(d*κ) < t by linarith)
    nlinarith
  have he : x+(t-a) • v-(κ*t) • firstAxis =
      (x-(κ*a) • firstAxis)+(t-a) • (v-κ • firstAxis) := by module
  refine ⟨?_,hv₅⟩
  change ‖x+(t-a) • v-(κ*t) • firstAxis‖ < d*κ*t
  rw [he]
  have hn := norm_add_le (x-(κ*a) • firstAxis) ((t-a) • (v-κ • firstAxis))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hta)] at hn
  have hm : (t-a)*‖v-κ • firstAxis‖ ≤ (t-a)*(d*κ/4) :=
    mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hta)
  dsimp only [R] at hR
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The fourth-power mass cap in the expanding branching boxes -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def lateBoxCapConstant (q κ d : ℝ) : ℝ :=
  (Real.pi*4/3)*(d*κ)^3*(∫ v : V, H q v)

theorem lateBoxCapConstant_nonneg {q κ d : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) :
    0 ≤ lateBoxCapConstant q κ d := by
  unfold lateBoxCapConstant
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (integral_nonneg (H_nonneg q))

theorem density_lateBox_bound {q κ d t : ℝ} (hq : q < 2) (hκ : 0 ≤ κ)
    (hd : 0 ≤ d) (ht : 0 ≤ t) {F : V × V → ℝ}
    (hF : ∀ᵐ p ∂volume, F p ≤ (t+1)*H q p.2) :
    positiveDensityMeasure volume F (lateBox κ d t) ≤
      ENNReal.ofReal (lateBoxCapConstant q κ d*(1+t)^4) := by
  let g : V → ℝ := fun v => (t+1)*H q v
  have hg : Measurable g := measurable_const.mul (ChartKernel.measurable_H q)
  let _ : SFinite (positiveDensityMeasure volume g) := by
    unfold positiveDensityMeasure
    infer_instance
  have hgi : Integrable g := (integrable_H hq).const_mul _
  have hgn (v) : 0 ≤ g v := mul_nonneg (by positivity) (H_nonneg q v)
  have hmono : positiveDensityMeasure volume F ≤
      positiveDensityMeasure volume (fun p : V × V => g p.2) :=
    withDensity_mono (hF.mono (fun p hp => ENNReal.ofReal_le_ofReal hp))
  have hprod : positiveDensityMeasure volume (fun p : V × V => g p.2) =
      (volume : Measure V).prod (positiveDensityMeasure volume g) := by
    unfold positiveDensityMeasure
    rw [Measure.volume_eq_prod]
    exact (prod_withDensity_right hg.ennreal_ofReal).symm
  have hmass : positiveDensityMeasure volume g univ =
      ENNReal.ofReal ((t+1)*(∫ v : V, H q v)) := by
    rw [positiveDensityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn)]
    congr 1
    exact integral_const_mul _ _
  calc
    _ ≤ positiveDensityMeasure volume (fun p : V × V => g p.2) (lateBox κ d t) := hmono _
    _ ≤ positiveDensityMeasure volume (fun p : V × V => g p.2)
        (ball ((κ*t) • firstAxis) (d*κ*t) ×ˢ univ) := by
      apply measure_mono
      intro p hp
      exact ⟨hp.1,mem_univ _⟩
    _ = ENNReal.ofReal ((d*κ*t)^3*(Real.pi*4/3)*((t+1)*(∫ v : V, H q v))) := by
      rw [hprod,Measure.prod_prod,EuclideanSpace.volume_ball_fin_three,hmass,
        ← ENNReal.ofReal_pow (by positivity : 0 ≤ d*κ*t),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d*κ*t)^3),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (d*κ*t)^3*(Real.pi*4/3))]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hp : t^3 ≤ (1+t)^3 := pow_le_pow_left₀ ht (by linarith) 3
      have hm := mul_le_mul_of_nonneg_right hp
        (mul_nonneg (lateBoxCapConstant_nonneg (q := q) hκ hd) (by positivity : 0 ≤ 1+t))
      dsimp only [lateBoxCapConstant] at hm ⊢
      convert hm using 1 <;> ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform cold-density scales on the expanding transverse boxes -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_radius_bounds {κ d t : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    {p : V × V} (hp : p ∈ lateBox κ d t) :
    (1-d)*κ*t < ‖transverse p.1‖ ∧ ‖transverse p.1‖ < (1+d)*κ*t ∧
      |axial p.1| < d*κ*t := by
  let c : V := (κ*t) • firstAxis
  have hcax : axial c = 0 := by
    simp [c,axial,firstAxis,EuclideanSpace.single]
  have hcnorm : ‖c‖ = κ*t := by
    simp [c,norm_smul,axis_norms.1,Real.norm_eq_abs,abs_of_pos hκ,abs_of_pos ht]
  have hctn : ‖transverse c‖ = κ*t := by
    have hh := norm_sq_split c
    rw [hcnorm,hcax] at hh
    nlinarith [norm_nonneg (transverse c),mul_pos hκ ht]
  have he : ‖transverse p.1-transverse c‖ < d*κ*t := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le _).trans_lt hp.1
  have hlo := norm_sub_norm_le (transverse c) (transverse p.1)
  have hhi := norm_sub_norm_le (transverse p.1) (transverse c)
  rw [norm_sub_rev] at hlo
  have ha := (SmallInputGeometry.abs_axial_le_norm (p.1-c)).trans_lt hp.1
  rw [PlaneChart.axial_sub,hcax,sub_zero] at ha
  exact ⟨by rw [hctn] at hlo; nlinarith,
    by rw [hctn] at hhi; nlinarith,ha⟩

theorem lateBox_geometric_scale {κ d t : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hd : d ≤ 1/2) (ht : 0 < t) {p : V × V} (hp : p ∈ lateBox κ d t) :
    0 < ‖transverse p.1‖ ∧ t ≤ (4/κ)*‖transverse p.1‖/2 ∧
      |axial p.1| ≤ (4/κ)*‖transverse p.1‖/2 := by
  obtain ⟨hlo,hhi,hax⟩ := lateBox_radius_bounds hκ ht hp
  have hhalf : κ*t/2 < ‖transverse p.1‖ := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hr : 0 < ‖transverse p.1‖ := lt_trans (by positivity) hhalf
  have he : (4/κ)*‖transverse p.1‖/2 = 2*‖transverse p.1‖/κ := by ring
  have htime : t ≤ 2*‖transverse p.1‖/κ :=
    (le_div_iff₀ hκ).mpr (by nlinarith)
  have haxr : |axial p.1| ≤ ‖transverse p.1‖ := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hrr : ‖transverse p.1‖ ≤ 2*‖transverse p.1‖/κ := by
    apply (le_div_iff₀ hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hκ₁ hr.le]
  refine ⟨hr,?_,?_⟩
  · simpa only [he] using htime
  · simpa only [he] using haxr.trans hrr

theorem lateBox_block_duration {κ d t K A₀ : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    (hd : d ≤ 1/2) (hK : 0 < K) (hA₀ : 0 < A₀)
    {p : V × V} (hp : p ∈ lateBox κ d t) :
    (K/(4*‖transverse p.1‖)) * ((8*κ*A₀/K)*t) ∈ Icc A₀ (4*A₀) := by
  obtain ⟨hlo,hhi,_⟩ := lateBox_radius_bounds hκ ht hp
  have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
  have hr : 0 < ‖transverse p.1‖ := by nlinarith
  have he : (K/(4*‖transverse p.1‖)) * ((8*κ*A₀/K)*t) =
      2*κ*A₀*t/‖transverse p.1‖ := by field_simp [hK.ne',hr.ne']; ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hr).mpr
    have hru : ‖transverse p.1‖ ≤ 2*κ*t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hru hA₀.le]
  · apply (div_le_iff₀ hr).mpr
    have hrl : κ*t ≤ 2*‖transverse p.1‖ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hrl (show 0 ≤ 2*A₀ by positivity)]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One physical damping rate serves every local density scale in a late box -/

noncomputable section

open Set
open scoped NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_damping_range {κ d t : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    (hd : d ≤ 1/2) {p : V × V} (hp : p ∈ lateBox κ d t) :
    (referenceClock:ℝ) ≤ 96*Real.pi*‖transverse p.1‖/(κ*t) ∧
      96*Real.pi*‖transverse p.1‖/(κ*t) ≤ 3*(referenceClock:ℝ) := by
  obtain ⟨hlo,hhi,_⟩ := lateBox_radius_bounds hκ ht hp
  have hhalf : κ*t/2 < ‖transverse p.1‖ := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hthree : ‖transverse p.1‖ < 3*(κ*t)/2 := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  constructor
  · apply (le_div_iff₀ (mul_pos hκ ht)).mpr
    change 48*Real.pi*(κ*t) ≤ 96*Real.pi*‖transverse p.1‖
    nlinarith [mul_le_mul_of_nonneg_left hhalf.le (show 0 ≤ 96*Real.pi by positivity)]
  · apply (div_le_iff₀ (mul_pos hκ ht)).mpr
    change 96*Real.pi*‖transverse p.1‖ ≤ 3*(48*Real.pi)*(κ*t)
    nlinarith [mul_le_mul_of_nonneg_left hthree.le (show 0 ≤ 96*Real.pi by positivity)]

theorem lateBox_damping_normalization {κ t K : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    {x : V} (hx : 0 < ‖transverse x‖) :
    (K/(4*‖transverse x‖)) * (96*Real.pi*‖transverse x‖/(κ*t)) =
      24*Real.pi*K/(κ*t) := by
  field_simp
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The branching contradiction after a fixed positive starting time -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness.GrowthContradiction

theorem next_good_growth_time_in_interval {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G)
    {m : ℝ → ℝ} {r₀ r₁ t : ℝ} (hrr : r₀ < r₁) (ht : 0 < t)
    (hstep : ∀ᵐ u ∂volume, u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u) :
    ∃ u, u ∈ G ∧ u ∈ Ioo (r₀*t) (r₁*t) ∧ 3*m t ≤ m u := by
  have hi : r₀*t < r₁*t := mul_lt_mul_of_pos_right hrr ht
  have hpos : (volume : Measure ℝ) (Ioo (r₀*t) (r₁*t)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hi))
  have hae : ∀ᵐ u ∂volume.restrict (Ioo (r₀*t) (r₁*t)), u ∈ G ∧ 3*m t ≤ m u := by
    filter_upwards [ae_restrict_of_ae hG,ae_restrict_of_ae hstep,
      ae_restrict_mem measurableSet_Ioo] with u hu hs hiu
    exact ⟨hu,hs hiu⟩
  obtain ⟨u,hu,hgu,hmu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hae
  exact ⟨u,hgu,hu,hmu⟩

theorem no_late_ae_growth_with_cap {G : Set ℝ}
    (hG : ∀ᵐ t ∂volume, t ∈ G) {m : ℝ → ℝ} {r₀ r₁ C R t₀ : ℝ}
    (hR : 0 ≤ R) (hr₀ : 1 ≤ r₀) (hrr : r₀ < r₁) (hgrowth : r₁^4 < 3)
    (hC : 0 ≤ C) (ht₀ : R < t₀) (htG : t₀ ∈ G) (hm₀ : 0 < m t₀)
    (hcap : ∀ t ∈ G, R < t → m t ≤ C*(1+t)^4)
    (hstep : ∀ t ∈ G, R < t → ∀ᵐ u ∂volume,
      u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u) : False := by
  have hr₁ : 1 < r₁ := hr₀.trans_lt hrr
  have hex (n : ℕ) : ∃ t, t ∈ G ∧ R < t ∧ t ≤ r₁^n*t₀ ∧ 3^n*m t₀ ≤ m t := by
    induction n with
    | zero => exact ⟨t₀,htG,ht₀,by simp,by simp⟩
    | succ n ih =>
      obtain ⟨t,htG,ht,htbound,hm⟩ := ih
      have htpos := hR.trans_lt ht
      obtain ⟨u,huG,hu,hmu⟩ := next_good_growth_time_in_interval hG hrr htpos (hstep t htG ht)
      have htu : t < u := (le_mul_of_one_le_left htpos.le hr₀).trans_lt hu.1
      refine ⟨u,huG,ht.trans htu,?_,?_⟩
      · calc
          u ≤ r₁*t := hu.2.le
          _ ≤ r₁*(r₁^n*t₀) := mul_le_mul_of_nonneg_left htbound (zero_le_one.trans hr₁.le)
          _ = r₁^(n+1)*t₀ := by rw [pow_succ']; ring
      · calc
          3^(n+1)*m t₀ = 3*(3^n*m t₀) := by rw [pow_succ']; ring
          _ ≤ 3*m t := mul_le_mul_of_nonneg_left hm (by norm_num)
          _ ≤ m u := hmu
  apply no_uniform_branching_cap (a := r₁-1) (t₀ := t₀) (m₀ := m t₀) (C := C)
    (by linarith) (hR.trans_lt ht₀) hm₀ hC (by simpa only [show 1+(r₁-1)=r₁ by ring] using hgrowth)
  intro n
  obtain ⟨t,htG,ht,htb,hm⟩ := hex n
  have hp : (1+t)^4 ≤ (1+r₁^n*t₀)^4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  simpa only [show 1+(r₁-1)=r₁ by ring] using
    hm.trans ((hcap t htG ht).trans (mul_le_mul_of_nonneg_left hp hC))

theorem ae_zero_of_late_growth_cap {m : ℝ → ℝ} {r₀ r₁ C R : ℝ}
    (hR : 0 ≤ R) (hr₀ : 1 ≤ r₀) (hrr : r₀ < r₁) (hgrowth : r₁^4 < 3) (hC : 0 ≤ C)
    (hn : ∀ t, 0 ≤ m t)
    (hcap : ∀ᵐ t ∂volume, R < t → m t ≤ C*(1+t)^4)
    (hstep : ∀ᵐ t ∂volume, R < t → ∀ᵐ u ∂volume,
      u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u) :
    ∀ᵐ t ∂volume, R < t → m t = 0 := by
  let G := {t | (R < t → m t ≤ C*(1+t)^4) ∧
    (R < t → ∀ᵐ u ∂volume, u ∈ Ioo (r₀*t) (r₁*t) → 3*m t ≤ m u)}
  have hG : ∀ᵐ t ∂volume, t ∈ G := hcap.and hstep
  filter_upwards [hG] with t ht
  intro hRt
  apply le_antisymm _ (hn t)
  by_contra h
  exact no_late_ae_growth_with_cap hG hR hr₀ hrr hgrowth hC hRt ht (lt_of_not_ge h)
    (fun _ hu => hu.1) (fun _ hu => hu.2)

end BoltzmannNonuniqueness.GrowthContradiction

end

end

section

/-! # Positive mass with the entry velocities eventually reaches the growing box -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem bounded_flight_lateBox {κ d a X : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (ha : 0 ≤ a) :
    ∃ T : ℝ, a ≤ T ∧ 0 < T ∧ ∀ (x v : V), ‖x‖ ≤ X →
      ‖v-κ • firstAxis‖ < d*κ/4 → ‖v‖ < 5 → ∀ t, T ≤ t →
        (x+(t-a) • v,v) ∈ lateBox κ d t := by
  let R := X+κ*a
  let T := max (max a 1) (4*R/(d*κ)+1)
  have hdk : 0 < d*κ := mul_pos hd hκ
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_right a 1).trans (le_max_left _ _))
  refine ⟨T,(le_max_left a 1).trans (le_max_left _ _),hT,?_⟩
  intro x v hx hv hv₅ t ht
  have hta : a ≤ t := ((le_max_left a 1).trans (le_max_left _ _)).trans ht
  have htt : 0 < t := hT.trans_le ht
  have hR : R < d*κ*t/4 := by
    have hlarge : 4*R/(d*κ)+1 ≤ t := (le_max_right _ _).trans ht
    have hdiv := (div_lt_iff₀ hdk).mp (show 4*R/(d*κ) < t by linarith)
    linarith
  have hxR : ‖x-(κ*a) • firstAxis‖ ≤ R := by
    have hb := norm_sub_le x ((κ*a) • firstAxis)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hκ.le ha),axis_norms.1,mul_one] at hb
    exact hb.trans (show ‖x‖+κ*a ≤ R from add_le_add hx le_rfl)
  have he : x+(t-a) • v-(κ*t) • firstAxis =
      (x-(κ*a) • firstAxis)+(t-a) • (v-κ • firstAxis) := by module
  refine ⟨?_,hv₅⟩
  change ‖x+(t-a) • v-(κ*t) • firstAxis‖ < d*κ*t
  rw [he]
  have hn := norm_add_le (x-(κ*a) • firstAxis) ((t-a) • (v-κ • firstAxis))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hta)] at hn
  have hm : (t-a)*‖v-κ • firstAxis‖ ≤ (t-a)*(d*κ/4) :=
    mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hta)
  nlinarith

def entryVelocityRegion (κ d : ℝ) : Set (V × V) :=
  {p | ‖p.2-κ • firstAxis‖ < d*κ/4 ∧ ‖p.2‖ < 5}

theorem entryVelocityRegion_measurable (κ d : ℝ) : MeasurableSet (entryVelocityRegion κ d) := by
  unfold entryVelocityRegion
  measurability

theorem positive_mass_eventually_lateBox {κ d a : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (ha : 0 ≤ a) (μ : Measure (V × V)) (hμ : 0 < μ (entryVelocityRegion κ d)) :
    ∃ T : ℝ, a ≤ T ∧ 0 < T ∧ ∀ t, T ≤ t →
      0 < (μ.map (fun p => (p.1+(t-a) • p.2,p.2))) (lateBox κ d t) := by
  let E : ℕ → Set (V × V) := fun n => entryVelocityRegion κ d ∩ {p | ‖p.1‖ ≤ (n:ℝ)}
  have hE : (⋃ n, E n) = entryVelocityRegion κ d := by
    ext p
    constructor
    · intro hp
      obtain ⟨n,hn⟩ := mem_iUnion.mp hp
      exact hn.1
    · intro hp
      obtain ⟨n,hn⟩ := exists_nat_gt ‖p.1‖
      exact mem_iUnion.mpr ⟨n,hp,hn.le⟩
  obtain ⟨n,hn⟩ : ∃ n, 0 < μ (E n) :=
    exists_measure_pos_of_not_measure_iUnion_null (by rw [hE]; exact ne_of_gt hμ)
  obtain ⟨T,haT,hT,hbound⟩ := bounded_flight_lateBox (X := (n:ℝ)) hκ hd ha
  refine ⟨T,haT,hT,?_⟩
  intro t ht
  rw [Measure.map_apply (by fun_prop) (lateBox_measurable κ d t)]
  apply hn.trans_le (measure_mono ?_)
  intro p hp
  exact hbound p.1 p.2 hp.2 hp.1.1 hp.1.2 t ht

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
