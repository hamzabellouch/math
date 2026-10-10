import Mathlib
import OAI.Combinatorics.UniformKServer.PilotDeletion

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
theorem near_deficit [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    (1-nearWeight r σ z x)*ballMass r γ μ x ≤
      (512*γ/σ^2)*innerMoment r γ μ x +
        514*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
  have hmid := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  let w := insertUnit r R z x
  have hw : feasible r σ R w := insertUnit_feasible r σ R hr hσ hσ1 hR z hz x
  have hpoint : ∀ p : X,
      integrand r σ R g w p - integrand r σ R g z p ≤
        (if dist x p ≤ γ*r then (512*γ/σ^2)*(dist x p/r)-(1-nearWeight r σ z x) else 0) +
        514*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)) := by
    intro p
    by_cases hi : dist x p ≤ γ*r
    · have ho : dist x p ≤ (100*R)*r := hi.trans (by nlinarith)
      simp only [ite_eq_left hi, ite_eq_left ho]
      have hu := new_inner_upper r σ R γ hr hσ hσ1 hR hγσ g z hg x p hi
      have hl := old_inner_lower r σ R γ hr hσ hσ1 hR hγ hγσ g z hg hz x p hi hmid
      have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hi
      have hsq : (dist x p/r)^2 ≤ γ*(dist x p/r) := by
        nlinarith [mul_nonneg (div_nonneg (dist_nonneg (x := x) (y := p)) hr.le) (sub_nonneg.mpr hv)]
      have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 512/σ^2 by positivity)
      have hm' : 512/σ^2*(dist x p/r)^2 ≤ (512*γ/σ^2)*(dist x p/r) := by
        calc
          _ ≤ (512/σ^2)*(γ*(dist x p/r)) := hm
          _ = _ := by ring
      change integrand r σ R g (insertUnit r R z x) p - integrand r σ R g z p ≤ _
      linarith only [hu, hl, hm']
    · by_cases ho : dist x p ≤ (100*R)*r
      · simp only [ite_eq_right hi, ite_eq_left ho]
        have hu := (integrand_bounds r σ R hr hσ hσ1 hR g w hg hw p).2
        have hl := (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz p).1
        linarith
      · simp only [ite_eq_right hi, ite_eq_right ho]
        change integrand r σ R g (insertUnit r R z x) p - integrand r σ R g z p ≤ _
        rw [unchanged_outside r σ R hr hσ hσ1 hR g z x p (lt_of_not_ge ho)]
        norm_num
  have hs := Finset.sum_le_sum (fun (p : X) (_ : p ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint p) (hμ p))
  have he : (∑ p, μ p*((if dist x p ≤ γ*r then (512*γ/σ^2)*(dist x p/r)-
        (1-nearWeight r σ z x) else 0) +
        514*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)))) =
      (512*γ/σ^2)*innerMoment r γ μ x - (1-nearWeight r σ z x)*ballMass r γ μ x +
        514*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
    unfold innerMoment ballMass
    simp only [Finset.mul_sum, mul_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> ring
  rw [he] at hs
  have hmin' := value_le r σ R μ g w hw
  rw [← hmin] at hmin'
  have hcost : 0 ≤ ∑ p, μ p*(integrand r σ R g w p-integrand r σ R g z p) := by
    unfold objective at hmin'
    have hh : (∑ p, μ p*integrand r σ R g z p) ≤ ∑ p, μ p*integrand r σ R g w p :=
      (mul_le_mul_iff_right₀ hr).mp hmin'
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith
  linarith

theorem nearWeight_large [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    (3:ℝ)/4 ≤ nearWeight r σ z x := by
  have hd := near_deficit r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hm := (innerMoment_bounds r γ hr μ hμ x).2
  have hsq : 512*γ^2/σ^2 ≤ (1:ℝ)/8 := by
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith [sq_nonneg (σ-64*γ), mul_nonneg (sub_nonneg.mpr hγσ) hγ.le]
  have hc : 0 ≤ 512*γ/σ^2 := by positivity
  have hmoment : (512*γ/σ^2)*innerMoment r γ μ x ≤ (1:ℝ)/8*ballMass r γ μ x := by
    calc
      _ ≤ (512*γ/σ^2)*(γ*ballMass r γ μ x) := mul_le_mul_of_nonneg_left hm hc
      _ = (512*γ^2/σ^2)*ballMass r γ μ x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq hM.le
  have hshell : 514*(ballMass r (100*R) μ x-ballMass r γ μ x) ≤
      (1:ℝ)/8*ballMass r γ μ x := by
    have hh := mul_le_mul_of_nonneg_right (show 514*δ ≤ (1:ℝ)/8 by linarith) hM.le
    nlinarith
  have hprod : (3/4-nearWeight r σ z x)*ballMass r γ μ x ≤ 0 := by nlinarith
  by_contra hh
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hM
  linarith

theorem near_positive_unique (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (x s s' : X)
    (hs : 0 < z s) (hs' : 0 < z s') (hn : dist s x/r < σ/4)
    (hn' : dist s' x/r < σ/4) : s'=s := by
  by_contra hne
  have hsep : 5*σ ≤ dist s s'/r := (le_div_iff₀ hr).mpr (by
    convert hz.2.2 s s' (Ne.symm hne) hs hs' using 1)
  have ht := normalized_triangle r hr s x s'
  rw [dist_comm x s'] at ht
  linarith

theorem nearWeight_eq_site (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (x s : X)
    (hs : 0 < z s) (hn : dist s x/r < σ/4) : nearWeight r σ z x = z s := by
  classical
  unfold nearWeight
  rw [Finset.sum_eq_single s]
  · rw [ite_eq_left hn]
  · intro t ht hne
    split_ifs with htnear
    · have hnpos : ¬0<z t := by
        intro htp
        exact hne (near_positive_unique r σ R hr hσ z hz x s t hs htp hn htnear)
      linarith [hz.1 t]
    · rfl
  · simp

theorem near_site_exists [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    ∃ s, dist s x/r < σ/4 ∧ (3:ℝ)/4 ≤ z s ∧
      (∀ s', 0 < z s' → dist s' x/r < σ/4 → s'=s) ∧
      1-z s ≤ (512*γ/σ^2)*(innerMoment r γ μ x/ballMass r γ μ x) +
        514*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x) := by
  have hl := nearWeight_large r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hp : 0 < ∑ s, if dist s x/r < σ/4 then z s else 0 := lt_of_lt_of_le (by norm_num) hl
  have hn : ∀ s ∈ (Finset.univ : Finset X), 0 ≤ (if dist s x/r < σ/4 then z s else 0) := by
    intro s hs
    split_ifs <;> first | exact hz.1 s | rfl
  obtain ⟨s, hs, hspos⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hp
  have hnear : dist s x/r < σ/4 := by
    by_contra hn
    rw [ite_eq_right hn] at hspos
    linarith
  rw [ite_eq_left hnear] at hspos
  have he := nearWeight_eq_site r σ R hr hσ z hz x s hspos hnear
  rw [he] at hl
  refine ⟨s, hnear, hl, ?_, ?_⟩
  · intro t ht hn
    exact near_positive_unique r σ R hr hσ z hz x s t hspos ht hnear hn
  · have hd := near_deficit r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
      μ g z hμ hg x hM hconc hz hmin
    rw [he] at hd
    have heq : (512*γ/σ^2)*(innerMoment r γ μ x/ballMass r γ μ x) +
        514*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x) =
        ((512*γ/σ^2)*innerMoment r γ μ x +
          514*(ballMass r (100*R) μ x-ballMass r γ μ x))/ballMass r γ μ x := by ring
    rw [heq]
    exact (le_div_iff₀ hM).mpr hd

/-! Scalar slope proofs for exact compact pilot. -/

theorem clamp_abs (u v : ℝ) :
    |max 0 (min 1 u)-max 0 (min 1 v)| ≤ |u-v| := by
  have hmin := abs_min_sub_min_le_max (1:ℝ) u 1 v
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 u) 0 (min 1 v)
  simp only [sub_self, abs_zero] at hmin hmax
  rw [max_eq_right (abs_nonneg (u-v))] at hmin
  rw [max_eq_right (abs_nonneg (min 1 u-min 1 v))] at hmax
  exact hmax.trans hmin

theorem bumpB_lipschitz (σ u v : ℝ) (hσ : 0 < σ) :
    |bumpB σ u-bumpB σ v| ≤ |u-v|/σ := by
  have h := clamp_abs (2-u/σ) (2-v/σ)
  unfold bumpB
  convert h using 1
  have he : (2-u/σ)-(2-v/σ) = -(u-v)/σ := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hσ]

theorem gate_lipschitz (R u v : ℝ) (hR : 0 < R) :
    |gate R u-gate R v| ≤ |u-v|/(10*R) := by
  have h := clamp_abs (u/(10*R)-1) (v/(10*R)-1)
  unfold gate
  convert h using 1
  have he : (u/(10*R)-1)-(v/(10*R)-1) = (u-v)/(10*R) := by ring
  rw [he, abs_div, abs_of_pos (by positivity : 0<10*R)]

theorem capped_square_order (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    0 ≤ min (v^2) 1-min (u^2) 1 ∧ min (v^2) 1-min (u^2) 1 ≤ 2*(v-u) := by
  have hv : 0 ≤ v := hu.trans huv
  have hsq : u^2 ≤ v^2 := by nlinarith
  refine ⟨sub_nonneg.mpr (min_le_min_right 1 hsq), ?_⟩
  by_cases hv1 : v ≤ 1
  · have hu1 : u ≤ 1 := huv.trans hv1
    rw [min_eq_left (by nlinarith : v^2 ≤ 1), min_eq_left (by nlinarith : u^2 ≤ 1)]
    nlinarith [mul_nonneg (show 0≤v-u by linarith) (show 0≤2-v-u by linarith)]
  · rw [min_eq_right (by nlinarith : 1 ≤ v^2)]
    by_cases hu1 : u ≤ 1
    · rw [min_eq_left (by nlinarith : u^2 ≤ 1)]
      nlinarith [sq_nonneg (1-u)]
    · rw [min_eq_right (by nlinarith : 1 ≤ u^2)]
      linarith

theorem capped_square_abs (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |min (u^2) 1-min (v^2) 1| ≤ 2*|u-v| := by
  rcases le_total u v with huv | hvu
  · have hh := capped_square_order u v hu huv
    rw [abs_sub_comm, abs_of_nonneg hh.1, abs_of_nonpos (sub_nonpos.mpr huv)]
    linarith [hh.2]
  · have hh := capped_square_order v u hv hvu
    rw [abs_of_nonneg hh.1, abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hh.2

theorem quadratic_abs (σ u v : ℝ) (hσ : 0 < σ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |min (u^2/σ^2) 1-min (v^2/σ^2) 1| ≤ (2/σ)*|u-v| := by
  have hh := capped_square_abs (u/σ) (v/σ) (div_nonneg hu hσ.le) (div_nonneg hv hσ.le)
  rw [div_pow, div_pow, ← sub_div, abs_div, abs_of_pos hσ] at hh
  calc
    _ ≤ 2*(|u-v|/σ) := hh
    _ = _ := by ring

theorem tail_abs (R u v : ℝ) (hR : 0 < R) :
    |max (2-u/R) 0-max (2-v/R) 0| ≤ (1/R)*|u-v| := by
  have hh := abs_max_sub_max_le_abs (2-u/R) (2-v/R) 0
  have he : (2-u/R)-(2-v/R) = -(u-v)/R := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hR] at hh
  calc
    _ ≤ |u-v|/R := hh
    _ = _ := by ring

theorem bumpA_tail (σ R u : ℝ) (hR : 0 < R) (hu : R < u) :
    bumpA σ R u = max (2-u/R) 0 := by
  unfold bumpA
  rw [ite_eq_right (not_le_of_gt hu)]
  split_ifs with h2
  · exact (max_eq_left (by have hh := (div_le_iff₀ hR).mpr h2; linarith)).symm
  · have hh : 2 < u/R := (lt_div_iff₀ hR).mpr (lt_of_not_ge h2)
    exact (max_eq_right (by linarith)).symm

theorem bumpA_at_R (σ R : ℝ) (hσ : 0 < σ) (hRσ : σ ≤ R) : bumpA σ R R = 1 := by
  unfold bumpA
  rw [ite_eq_left le_rfl]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  have hR : 0 ≤ R := hσ.le.trans hRσ
  nlinarith

theorem bumpA_cross (σ R u v : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hu : 0 ≤ u) (huR : u ≤ R) (hRv : R < v) :
    |bumpA σ R u-bumpA σ R v| ≤ (2/σ)*(v-u) := by
  have hRpos : 0 < R := by linarith
  have hf : min (R^2/σ^2) 1 = 1 := by
    have he := bumpA_at_R σ R hσ (by linarith)
    simpa only [bumpA, ite_eq_left le_rfl] using he
  have hg : max (2-R/R) 0 = 1 := by norm_num [ne_of_gt hRpos]
  have hqi := quadratic_abs σ u R hσ hu hRpos.le
  rw [hf, abs_of_nonpos (sub_nonpos.mpr huR)] at hqi
  have hti := tail_abs R R v hRpos
  rw [hg, abs_of_nonpos (sub_nonpos.mpr hRv.le)] at hti
  have hC : 1/R ≤ 2/σ := by
    apply (div_le_div_iff₀ hRpos hσ).mpr
    linarith
  have hlo : |bumpA σ R u-1| ≤ (2/σ)*(R-u) := by
    simpa only [bumpA, ite_eq_left huR, neg_sub] using hqi
  have hhi : |1-bumpA σ R v| ≤ (2/σ)*(v-R) := by
    rw [bumpA_tail σ R v hRpos hRv]
    have ht' : |1-max (2-v/R) 0| ≤ (1/R)*(v-R) := by
      simpa only [neg_sub] using hti
    exact ht'.trans (mul_le_mul_of_nonneg_right hC (by linarith))
  calc
    _ ≤ |bumpA σ R u-1|+|1-bumpA σ R v| := abs_sub_le _ _ _
    _ ≤ (2/σ)*(R-u)+(2/σ)*(v-R) := add_le_add hlo hhi
    _ = _ := by ring

theorem bumpA_lipschitz (σ R u v : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |bumpA σ R u-bumpA σ R v| ≤ (2/σ)*|u-v| := by
  have hRpos : 0 < R := by linarith
  by_cases huR : u ≤ R
  · by_cases hvR : v ≤ R
    · simpa only [bumpA, ite_eq_left huR, ite_eq_left hvR] using quadratic_abs σ u v hσ hu hv
    · have hh := bumpA_cross σ R u v hσ hσ1 hR hu huR (lt_of_not_ge hvR)
      rw [abs_of_nonpos (by linarith : u-v≤0), neg_sub]
      exact hh
  · by_cases hvR : v ≤ R
    · have hh := bumpA_cross σ R v u hσ hσ1 hR hv hvR (lt_of_not_ge huR)
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0≤u-v)]
      exact hh
    · rw [bumpA_tail σ R u hRpos (lt_of_not_ge huR), bumpA_tail σ R v hRpos (lt_of_not_ge hvR)]
      have hC : 1/R ≤ 2/σ := by
        apply (div_le_div_iff₀ hRpos hσ).mpr
        linarith
      exact (tail_abs R u v hRpos).trans (mul_le_mul_of_nonneg_right hC (abs_nonneg _))


def relocate [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x t : X) : ℝ :=
  if t=x then z s else if t=s then 0 else
    if dist t x ≤ (50*R)*r then max (z t-(dist s x/r)/(10*R)) 0 else z t


theorem trim_contribution (z G q : ℝ) (hG : 0 ≤ G) (hq : 0 ≤ q) :
    max (max (z-q) 0-G) 0 = max (max (z-G) 0-q) 0 := by
  by_cases hzq : q ≤ z
  · rw [max_eq_left (sub_nonneg.mpr hzq)]
    by_cases hzG : G ≤ z
    · rw [max_eq_left (sub_nonneg.mpr hzG)]
      congr 1
      ring
    · rw [max_eq_right (by linarith : z-G≤0), max_eq_right (by linarith : 0-q≤0)]
      exact max_eq_right (by linarith)
  · rw [max_eq_right (by linarith : z-q≤0), max_eq_right (by linarith : 0-G≤0)]
    symm
    apply max_eq_right
    have hh : max (z-G) 0 ≤ q := max_le (by linarith) hq
    linarith

theorem trim_add_le (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    max (a-q) 0+max (b-q) 0 ≤ max (a+b-q) 0 := by
  by_cases ha' : q ≤ a <;> by_cases hb' : q ≤ b
  · rw [max_eq_left (by linarith : 0≤a-q), max_eq_left (by linarith : 0≤b-q),
      max_eq_left (by linarith : 0≤a+b-q)]
    linarith
  · rw [max_eq_left (by linarith : 0≤a-q), max_eq_right (by linarith : b-q≤0)]
    exact (by linarith : a-q+0 ≤ a+b-q).trans (le_max_left _ _)
  · rw [max_eq_right (by linarith : a-q≤0), max_eq_left (by linarith : 0≤b-q)]
    exact (by linarith : 0+(b-q) ≤ a+b-q).trans (le_max_left _ _)
  · rw [max_eq_right (by linarith : a-q≤0), max_eq_right (by linarith : b-q≤0)]
    simp


end
end UniformKServer.PilotCompact

end OAI
