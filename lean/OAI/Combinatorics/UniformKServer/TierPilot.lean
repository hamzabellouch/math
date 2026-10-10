import Mathlib
import OAI.Combinatorics.UniformKServer.PilotDrift
import OAI.Combinatorics.UniformKServer.PilotFiltering

namespace OAI

noncomputable section

namespace UniformKServer.TierPilot

section
attribute [local instance] Classical.propDecidable
open PilotCompact

/-- The two source pilot templates use D_H=51200, R_L=4D_H, D_L=100R_L.
The small numerical parameters remain free so the later travel absorption can
choose them once and for all. -/
structure Parameters where
  sigma : ℝ
  gammaH : ℝ
  gammaL : ℝ
  deltaH : ℝ
  sigma_pos : 0 < sigma
  sigma_small : 3*sigma < 1/8
  sigma_gamma : 10*sigma < gammaH
  gammaH_small : gammaH ≤ 1/100
  gammaL_pos : 0 < gammaL
  gammaL_small : gammaL < sigma
  deltaH_pos : 0 < deltaH
  deltaH_small : deltaH ≤ 1/4112

variable {X : Type*} [Fintype X] [MetricSpace X]

def heavy (P : Parameters) (r : ℝ) (μ : X → ℝ) (x : X) : Prop :=
  ballMass r 51200 μ x ≤ (1+P.deltaH)*ballMass r P.gammaH μ x

def insertionMass (P : Parameters) (r : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  if heavy P r μ x then ballMass r 51200 μ x-ballMass r P.gammaH μ x
  else ballMass r 20480000 μ x

/-- Structural facts of the source short-roster expected parameter at an
insertion; its explicit finite-law construction is separate from this local
analytic gain. These are ramp/retirement facts, not a pilot gain premise. -/
structure Edit (r ε : ℝ) (x : X) (go gn : X → ℝ) : Prop where
  old_range : ∀ p, go p ∈ Set.Icc (0:ℝ) 1
  new_range : ∀ p, gn p ∈ Set.Icc (0:ℝ) 1
  unit_drop : ∀ p, dist x p ≤ r/8 → go p = 1 ∧ gn p = 0
  increase : ∀ p, gn p-go p ≤ ε
  support : ∀ p, go p < gn p → r/8 < dist x p ∧ dist x p ≤ 21*r

def variation (r σ : ℝ) (z f : X → ℝ) (p : X) : ℝ :=
  f p*(1-∑ s, z s*bumpB σ (dist s p/r)) +
    256*∑ s, z s*f s*bumpA σ 204800 (dist s p/r)

omit [Fintype X] [MetricSpace X] in
theorem Parameters.sigma_le_one (P : Parameters) : P.sigma ≤ 1 := by linarith [P.sigma_small]
omit [Fintype X] [MetricSpace X] in
theorem Parameters.gammaH_pos (P : Parameters) : 0 < P.gammaH := by
  linarith [P.sigma_pos,P.sigma_gamma]

theorem ballMass_nonneg (r a : ℝ) (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ ballMass r a μ x := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> first | exact hμ p | rfl

theorem annulus_identity (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b) (μ : X → ℝ) (x : X) :
    ballMass r b μ x-ballMass r a μ x =
      ∑ p, if a*r < dist x p ∧ dist x p ≤ b*r then μ p else 0 := by
  simp only [ballMass,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hm := mul_le_mul_of_nonneg_right hab hr
  by_cases ha : dist x p ≤ a*r
  · have hb : dist x p ≤ b*r := ha.trans hm
    simp [ha,hb,not_lt.mpr ha]
  · have ha' : a*r < dist x p := lt_of_not_ge ha
    simp [ha,ha']

theorem insertionMass_bounds (P : Parameters) (r : ℝ) (hr : 0 ≤ r)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ insertionMass P r μ x ∧ insertionMass P r μ x ≤ ballMass r 20480000 μ x := by
  have hm := ballMass_mono r P.gammaH 51200 hr (by linarith [P.gammaH_small]) μ hμ x
  have hbig := ballMass_mono r 51200 20480000 hr (by norm_num) μ hμ x
  have hn := ballMass_nonneg r P.gammaH μ hμ x
  unfold insertionMass
  split_ifs
  · constructor <;> linarith
  · exact ⟨ballMass_nonneg r 20480000 μ hμ x,le_rfl⟩

theorem residual_bounds (P : Parameters) (r : ℝ) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (p : X) :
    (1-∑ s, z s*bumpB P.sigma (dist s p/r)) ∈ Set.Icc (0:ℝ) 1 := by
  have h := weighted_bumpB_sum r P.sigma 204800 P.sigma_pos P.sigma_le_one
    (by norm_num) z hz p
  constructor <;> linarith [h.1,h.2]

theorem variation_nonneg (P : Parameters) (r : ℝ) (z f : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (hf : ∀ p, 0 ≤ f p) (p : X) :
    0 ≤ variation r P.sigma z f p := by
  apply add_nonneg
  · exact mul_nonneg (hf p) (residual_bounds P r z hz p).1
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (hf s))
      (bumpA_bounds P.sigma 204800 _ (by norm_num)).1

theorem variation_mono (P : Parameters) (r : ℝ) (z f g : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (hfg : ∀ p, f p ≤ g p) (p : X) :
    variation r P.sigma z f p ≤ variation r P.sigma z g p := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hfg p) (residual_bounds P r z hz p).1
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hfg s) (hz.1 s)) (bumpA_bounds P.sigma 204800 _ (by norm_num)).1

theorem variation_sub (r σ : ℝ) (z f g : X → ℝ) (p : X) :
    variation r σ z (fun s => f s-g s) p = variation r σ z f p-variation r σ z g p := by
  simp only [variation,sub_mul,mul_sub,Finset.sum_sub_distrib]
  ring

theorem integrand_variation (r σ : ℝ) (z go gn : X → ℝ) (p : X) :
    integrand r σ 204800 go z p-integrand r σ 204800 gn z p =
      variation r σ z (fun s => go s-gn s) p := by
  simp only [integrand,variation,mul_sub,sub_mul,mul_add,add_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

theorem variation_constant_bound (P : Parameters) (r ε : ℝ) (hε : 0 ≤ ε) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (p : X) : variation r P.sigma z (fun _ => ε) p ≤ 257*ε := by
  have hB := (residual_bounds P r z hz p).2
  have hA : (∑ s, z s*bumpA P.sigma 204800 (dist s p/r)) ≤ 1 :=
    (Finset.sum_le_sum fun s _ => weighted_bumpA P.sigma 204800 _ _ (by norm_num) (hz.1 s)).trans (hz.2.1 p)
  have heq : (∑ s, z s*ε*bumpA P.sigma 204800 (dist s p/r)) =
      ε*∑ s, z s*bumpA P.sigma 204800 (dist s p/r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  unfold variation
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hB hε, mul_le_mul_of_nonneg_left hA hε]

omit [Fintype X] [MetricSpace X] in
theorem plateau (σ R v : ℝ) (hσ : 0 < σ) (hlo : σ ≤ v) (hhi : v ≤ R) :
    bumpA σ R v = 1 := by
  simp only [bumpA,ite_eq_left hhi]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  nlinarith

omit [Fintype X] in
theorem heavy_coefficient_lower (P : Parameters) (r : ℝ) (hr : 0 < r)
    (go : X → ℝ) (hg : ∀ p, go p ∈ Set.Icc (0:ℝ) 1) (x c p : X)
    (hc : r/8 < dist x c ∧ dist x c ≤ 21*r) :
    256*(if dist x p ≤ P.gammaH*r then 1 else 0) -
      2*(if dist x p ≤ 51200*r then 1 else 0) ≤
        coefficient r P.sigma 204800 go c p := by
  have hcx : 1/8 < dist c x/r ∧ dist c x/r ≤ 21 := by
    rw [dist_comm c x]
    constructor
    · apply (lt_div_iff₀ hr).mpr
      linarith [hc.1]
    · exact (div_le_iff₀ hr).mpr hc.2
  have hA : (if dist x p ≤ P.gammaH*r then 1 else 0) ≤
      bumpA P.sigma 204800 (dist c p/r) := by
    split_ifs with hp
    · have hpx := (div_le_iff₀ hr).mpr hp
      have ht := normalized_triangle r hr c p x
      have ht' := normalized_triangle r hr c x p
      rw [dist_comm p x] at ht
      rw [plateau P.sigma 204800 _ P.sigma_pos
        (by linarith [P.sigma_small,P.gammaH_small,hcx.1])
        (by linarith [P.gammaH_small,hcx.2])]
    · exact (bumpA_bounds _ _ _ (by norm_num)).1
  have hB : bumpB P.sigma (dist c p/r) ≤ (if dist x p ≤ 51200*r then 1 else 0) := by
    split_ifs with hp
    · exact (bumpB_bounds _ _).2
    · have hpx := (lt_div_iff₀ hr).mpr (lt_of_not_ge hp)
      have ht := normalized_triangle r hr x c p
      rw [dist_comm x c] at ht
      rw [bumpB_zero P.sigma _ P.sigma_pos (by linarith [hcx.2,P.sigma_le_one])]
  have hcoeff : 256*bumpA P.sigma 204800 (dist c p/r)-2*bumpB P.sigma (dist c p/r) ≤
      coefficient r P.sigma 204800 go c p := by
    unfold coefficient
    nlinarith [mul_nonneg (hg c).1 (bumpA_bounds P.sigma 204800 (dist c p/r) (by norm_num)).1,
      mul_nonneg (show 0 ≤ 1-go p by linarith [(hg p).2]) (bumpB_bounds P.sigma (dist c p/r)).1]
  linarith

theorem increasing_site_zero (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x) (hh : heavy P r μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go)
    (c : X) (hc : go c < gn c) : z c = 0 := by
  classical
  have hcoef : 256*ballMass r P.gammaH μ x-2*ballMass r 51200 μ x ≤
      ∑ p, μ p*coefficient r P.sigma 204800 go c p := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left
        (heavy_coefficient_lower P r hr go he.old_range x c p (he.support c hc)) (hμ p))
    have hid : (∑ p, μ p*(256*(if dist x p ≤ P.gammaH*r then 1 else 0)-
        2*(if dist x p ≤ 51200*r then 1 else 0))) =
        256*ballMass r P.gammaH μ x-2*ballMass r 51200 μ x := by
      simp only [ballMass,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rwa [hid] at hi
  have hmass : ballMass r 51200 μ x ≤ 2*ballMass r P.gammaH μ x := by
    have hd : P.deltaH*ballMass r P.gammaH μ x ≤ ballMass r P.gammaH μ x := by
      have := mul_le_mul_of_nonneg_right
        (show P.deltaH ≤ 1 by linarith [P.deltaH_small]) hM.le
      simpa using this
    dsimp [heavy] at hh
    nlinarith
  have hpos : 0 < ∑ p, μ p*coefficient r P.sigma 204800 go c p := by linarith
  have hval := value_le r P.sigma 204800 μ go (Function.update z c 0) (erase_feasible r P.sigma 204800 z hz c)
  have hdiff := objective_erase r P.sigma 204800 μ go z c
  rw [hmin] at hdiff
  by_contra hn
  have hzc : 0 < z c := lt_of_le_of_ne (hz.1 c) (Ne.symm hn)
  have hmul := mul_pos (mul_pos hr hzc) hpos
  linarith

def rise (go gn : X → ℝ) (p : X) : ℝ := max (gn p-go p) 0
def fall (go gn : X → ℝ) (p : X) : ℝ := max (go p-gn p) 0

omit [Fintype X] [MetricSpace X] in
theorem rise_nonneg (go gn : X → ℝ) (p : X) : 0 ≤ rise go gn p := le_max_right _ _
omit [Fintype X] [MetricSpace X] in
theorem fall_nonneg (go gn : X → ℝ) (p : X) : 0 ≤ fall go gn p := le_max_right _ _

omit [Fintype X] in
theorem rise_bound (r ε : ℝ) (hε : 0 ≤ ε) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) : rise go gn p ≤ ε :=
  max_le (he.increase p) hε

omit [Fintype X] [MetricSpace X] in
theorem rise_zero (go gn : X → ℝ) (p : X) (hp : gn p ≤ go p) : rise go gn p = 0 :=
  max_eq_right (sub_nonpos.mpr hp)

omit [Fintype X] in
theorem rise_support (r ε : ℝ) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) (hp : rise go gn p ≠ 0) :
    r/8 < dist x p ∧ dist x p ≤ 21*r := by
  apply he.support p
  by_contra hn
  exact hp (rise_zero go gn p (le_of_not_gt hn))

theorem rise_nonheavy_point (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z) (p : X) :
    variation r P.sigma z (rise go gn) p ≤
      257*ε*(if dist x p ≤ 20480000*r then 1 else 0) := by
  by_cases hp : dist x p ≤ 20480000*r
  · rw [ite_eq_left hp,mul_one]
    exact (variation_mono P r z _ _ hz (rise_bound r ε hε x go gn he) p).trans
      (variation_constant_bound P r ε hε z hz p)
  · rw [ite_eq_right hp,mul_zero]
    have hzero : rise go gn p = 0 := by
      by_contra hn
      have h := (rise_support r ε x go gn he p hn).2
      linarith [lt_of_not_ge hp]
    have hsum : (∑ s, z s*rise go gn s*bumpA P.sigma 204800 (dist s p/r)) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      by_cases hs : rise go gn s = 0
      · simp [hs]
      · have hxs := (rise_support r ε x go gn he s hs).2
        have ht := dist_triangle x s p
        have hd : 2*(204800:ℝ) ≤ dist s p/r := by
          apply (le_div_iff₀ hr).mpr
          linarith [lt_of_not_ge hp]
        rw [bumpA_zero P.sigma 204800 _ (by norm_num) hd,mul_zero]
    simp [variation,hzero,hsum]

theorem rise_heavy_point (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x) (hh : heavy P r μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go)
    (p : X) : variation r P.sigma z (rise go gn) p ≤
      ε*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0) := by
  have hsum : (∑ s, z s*rise go gn s*bumpA P.sigma 204800 (dist s p/r)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : go s < gn s
    · rw [increasing_site_zero P r ε hr μ go gn z hμ x hM hh he hz hmin s hs]
      ring
    · rw [rise_zero go gn s (le_of_not_gt hs)]
      ring
  simp only [variation,hsum,mul_zero,add_zero]
  have hbound := mul_le_mul_of_nonneg_left (residual_bounds P r z hz p).2 (rise_nonneg go gn p)
  by_cases hp : P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r
  · rw [ite_eq_left hp,mul_one]
    exact (by simpa using hbound : rise go gn p*(1-∑ s, z s*bumpB P.sigma (dist s p/r)) ≤ rise go gn p).trans
      (rise_bound r ε hε x go gn he p)
  · have hn : rise go gn p = 0 := by
      by_contra hne
      have hd := rise_support r ε x go gn he p hne
      apply hp
      constructor
      · nlinarith [P.gammaH_small]
      · linarith [hd.2]
    simp [hn,hp]

theorem rise_integral_bound (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go) :
    (∑ p, μ p*variation r P.sigma z (rise go gn) p) ≤
      257*ε*insertionMass P r μ x := by
  by_cases hh : heavy P r μ x
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (rise_heavy_point P r ε hr hε μ go gn z hμ x hM hh he hz hmin p) (hμ p))
    have hid : (∑ p, μ p*(ε*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0))) =
        ε*insertionMass P r μ x := by
      rw [insertionMass,ite_eq_left hh,annulus_identity r P.gammaH 51200 hr.le (by linarith [P.gammaH_small]),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    have hn := (insertionMass_bounds P r hr.le μ hμ x).1
    nlinarith [mul_nonneg hε hn]
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (rise_nonheavy_point P r ε hr hε x go gn z he hz p) (hμ p))
    have hid : (∑ p, μ p*(257*ε*(if dist x p ≤ 20480000*r then 1 else 0))) =
        257*ε*insertionMass P r μ x := by
      simp only [insertionMass,ite_eq_right hh,ballMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rwa [hid] at hi

omit [Fintype X] in
theorem fall_unit (r ε : ℝ) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) (hp : dist x p ≤ r/8) : fall go gn p = 1 := by
  obtain ⟨ho,hn⟩ := he.unit_drop p hp
  norm_num [fall,ho,hn]

theorem fall_near_point (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z) (s : X)
    (hxs : dist x s ≤ 3*P.sigma*r) (hzs : 1/2 ≤ z s) (p : X) :
    128*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0) ≤
      variation r P.sigma z (fall go gn) p := by
  have hn := variation_nonneg P r z (fall go gn) hz (fall_nonneg go gn) p
  by_cases hp : P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r
  · rw [ite_eq_left hp,mul_one]
    have hfs := fall_unit r ε x go gn he s (by nlinarith [P.sigma_small])
    have hA : bumpA P.sigma 204800 (dist s p/r) = 1 := by
      apply plateau P.sigma 204800 _ P.sigma_pos
      · apply (le_div_iff₀ hr).mpr
        have := dist_triangle x s p
        nlinarith [P.sigma_gamma,P.sigma_pos]
      · apply (div_le_iff₀ hr).mpr
        have := dist_triangle s x p
        rw [dist_comm s x] at this
        nlinarith [P.sigma_le_one,hp.2]
    have hs := Finset.single_le_sum (s := Finset.univ) (a := s)
      (fun t _ => mul_nonneg (mul_nonneg (hz.1 t) (fall_nonneg go gn t))
        (bumpA_bounds P.sigma 204800 (dist t p/r) (by norm_num)).1) (Finset.mem_univ s)
    rw [hfs,hA,mul_one,mul_one] at hs
    have hres := mul_nonneg (fall_nonneg go gn p) (residual_bounds P r z hz p).1
    unfold variation
    linarith
  · rw [ite_eq_right hp,mul_zero]
    exact hn

theorem residual_half (P : Parameters) (r : ℝ) (hr : 0 < r) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (x : X)
    (hnear : ¬∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s)
    (p : X) (hp : dist x p ≤ P.gammaL*r) :
    1/2 ≤ 1-∑ s, z s*bumpB P.sigma (dist s p/r) := by
  have hsum : (∑ s, z s*bumpB P.sigma (dist s p/r)) ≤ 1/2 := by
    apply sum_le_unique _ _ (by norm_num)
    · intro s
      by_cases hb : 0 < bumpB P.sigma (dist s p/r)
      · have hd : dist s p/r < 2*P.sigma := by
          by_contra hn
          rw [bumpB_zero P.sigma _ P.sigma_pos (le_of_not_gt hn)] at hb
          linarith
        have hxs : dist x s ≤ 3*P.sigma*r := by
          have ht := dist_triangle x p s
          rw [dist_comm p s] at ht
          have := (div_lt_iff₀ hr).mp hd
          nlinarith [P.gammaL_small]
        have hzs : z s < 1/2 := lt_of_not_ge (fun hs => hnear ⟨s,hxs,hs⟩)
        calc
          z s*bumpB P.sigma (dist s p/r) ≤ z s*1 :=
            mul_le_mul_of_nonneg_left (bumpB_bounds _ _).2 (hz.1 s)
          _ ≤ 1/2 := by linarith
      · have hzero : bumpB P.sigma (dist s p/r) = 0 :=
          le_antisymm (le_of_not_gt hb) (bumpB_bounds _ _).1
        norm_num [hzero]
    · exact positive_bump_unique r P.sigma 204800 hr P.sigma_pos z hz p
  linarith

theorem fall_far_point (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z)
    (hnear : ¬∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s) (p : X) :
    (1/2)*(if dist x p ≤ P.gammaL*r then 1 else 0) ≤
      variation r P.sigma z (fall go gn) p := by
  by_cases hp : dist x p ≤ P.gammaL*r
  · rw [ite_eq_left hp,mul_one]
    have hfp := fall_unit r ε x go gn he p (by nlinarith [P.gammaL_small,P.sigma_small])
    have hres := residual_half P r hr z hz x hnear p hp
    have hs : 0 ≤ ∑ s, z s*fall go gn s*bumpA P.sigma 204800 (dist s p/r) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (fall_nonneg go gn s))
        (bumpA_bounds P.sigma 204800 _ (by norm_num)).1
    unfold variation
    rw [hfp,one_mul]
    linarith
  · rw [ite_eq_right hp,mul_zero]
    exact variation_nonneg P r z _ hz (fall_nonneg go gn) p

theorem qualification_inner (P : Parameters) (r h : ℝ) (hr : 0 ≤ r)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x) :
    Real.exp (-h)*insertionMass P r μ x ≤ ballMass r P.gammaL μ x := by
  have hi := mul_le_mul_of_nonneg_left
    ((insertionMass_bounds P r hr μ hμ x).2.trans hqual) (Real.exp_pos (-h)).le
  have he : Real.exp (-h)*Real.exp h = 1 := by rw [←Real.exp_add]; simp
  simpa only [←mul_assoc,he,one_mul] using hi

theorem fall_integral_bound (P : Parameters) (r ε h : ℝ) (hr : 0 < r) (hh : 0 ≤ h)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z) :
    min (1/2) (128*P.deltaH)*Real.exp (-h)*insertionMass P r μ x ≤
      ∑ p, μ p*variation r P.sigma z (fall go gn) p := by
  have hinner := qualification_inner P r h hr.le μ hμ x hqual
  have hW := (insertionMass_bounds P r hr.le μ hμ x).1
  have hc : 0 ≤ min (1/2:ℝ) (128*P.deltaH) := le_min (by norm_num) (mul_nonneg (by norm_num) P.deltaH_pos.le)
  by_cases hnear : ∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s
  · obtain ⟨s,hxs,hzs⟩ := hnear
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (fall_near_point P r ε hr x go gn z he hz s hxs hzs p) (hμ p))
    have hid : (∑ p, μ p*(128*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0))) =
        128*(ballMass r 51200 μ x-ballMass r P.gammaH μ x) := by
      rw [annulus_identity r P.gammaH 51200 hr.le (by linarith [P.gammaH_small]),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    by_cases hheavy : heavy P r μ x
    · have hidW : insertionMass P r μ x = ballMass r 51200 μ x-ballMass r P.gammaH μ x := ite_eq_left hheavy
      have he1 : Real.exp (-h) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -h ≤ 0 by linarith)
      have hce : min (1/2:ℝ) (128*P.deltaH)*Real.exp (-h) ≤ 128 := by
        have := mul_le_mul_of_nonneg_left he1 hc
        linarith [min_le_left (1/2:ℝ) (128*P.deltaH)]
      have hm := mul_le_mul_of_nonneg_right hce hW
      rw [hidW] at hm
      simpa only [hidW] using hm.trans hi
    · have hann : P.deltaH*ballMass r P.gammaL μ x ≤
          ballMass r 51200 μ x-ballMass r P.gammaH μ x := by
        have hLH := ballMass_mono r P.gammaL P.gammaH hr.le
          (by linarith [P.gammaL_small,P.sigma_gamma,P.sigma_pos]) μ hμ x
        have hh' := lt_of_not_ge hheavy
        change (1+P.deltaH)*ballMass r P.gammaH μ x < ballMass r 51200 μ x at hh'
        nlinarith [mul_le_mul_of_nonneg_left hLH P.deltaH_pos.le]
      have hci := mul_le_mul_of_nonneg_left hinner hc
      have hcM := mul_le_mul_of_nonneg_right (min_le_right (1/2:ℝ) (128*P.deltaH))
        (ballMass_nonneg r P.gammaL μ hμ x)
      nlinarith
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (fall_far_point P r ε hr x go gn z he hz hnear p) (hμ p))
    have hid : (∑ p, μ p*((1/2)*(if dist x p ≤ P.gammaL*r then 1 else 0))) =
        (1/2)*ballMass r P.gammaL μ x := by
      simp only [ballMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    have hci := mul_le_mul_of_nonneg_left hinner hc
    have hcM := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (128*P.deltaH))
      (ballMass_nonneg r P.gammaL μ hμ x)
    nlinarith

end
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Source tier-pilot drop with explicit absolute constants. The later
short-roster bound substitutes ε ≤ C/√K. -/
theorem insertion_gain (P : Parameters) (r ε h : ℝ) (hr : 0 < r)
    (hε : 0 ≤ ε) (hh : 1 ≤ h) (μ go gn : X → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (x : X) (hM : 0 < ballMass r P.gammaH μ x)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x)
    (he : Edit r ε x go gn) :
    r*insertionMass P r μ x*
      (min (1/2) (128*P.deltaH)*Real.exp (-h)-257*ε) ≤
        value r P.sigma 204800 μ go-value r P.sigma 204800 μ gn
 := by
  classical
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r P.sigma 204800 μ go
  have hrise := rise_integral_bound P r ε hr hε μ go gn z hμ x hM he hz hmin
  have hfall := fall_integral_bound P r ε h hr (by linarith) μ go gn z hμ x hqual he hz
  have hsplit : (fun p => go p-gn p) = (fun p => fall go gn p-rise go gn p) := by
    funext p
    simp only [fall,rise]
    by_cases hp : go p ≤ gn p
    · rw [max_eq_right (sub_nonpos.mpr hp),max_eq_left (sub_nonneg.mpr hp)]
      ring
    · have hp' := le_of_not_ge hp
      rw [max_eq_left (sub_nonneg.mpr hp'),max_eq_right (sub_nonpos.mpr hp')]
      ring
  have hid : objective r P.sigma 204800 μ go z-objective r P.sigma 204800 μ gn z =
      r*((∑ p, μ p*variation r P.sigma z (fall go gn) p)-
        ∑ p, μ p*variation r P.sigma z (rise go gn) p) := by
    simp only [objective,←mul_sub,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [integrand_variation,hsplit,variation_sub]
  have hv := value_le r P.sigma 204800 μ gn z hz
  rw [hmin] at hid
  have hi := mul_le_mul_of_nonneg_left (sub_le_sub hfall hrise) hr.le
  nlinarith

end UniformKServer.TierPilot

end

end OAI
