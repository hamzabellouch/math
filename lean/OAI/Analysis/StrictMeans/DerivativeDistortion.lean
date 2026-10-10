import OAI.Analysis.StrictMeans.DiskAutomorphisms

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_normalize {f : ℂ → ℂ} {z b c : ℂ} (hf : AnalyticAt ℂ f z) :
    deriv (deriv (fun w => (f w - b) / c)) z = deriv (deriv f) z / c := by
  have he : deriv (fun w => (f w - b) / c) =ᶠ[𝓝 z] (fun w => deriv f w / c) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact ((hw.differentiableAt.hasDerivAt.sub_const b).div_const c).deriv
  have hp := hf.deriv.differentiableAt.hasDerivAt.div_const c
  exact (hp.congr_of_eventuallyEq he).deriv

theorem preSchwarzian_bound {f : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : ‖a‖ < 1) :
    ‖(1 - (‖a‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) a / deriv f a) - 2 * conj a‖ ≤ 4 := by
  have ha' : a ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using ha
  have hfn := deriv_ne_zero_of_injOn isOpen_ball ha' hi hd
  let δ : ℂ := 1 - conj a * a
  have hδ : δ ≠ 0 := by
    dsimp only [δ]
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero,
      normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  let g : ℂ → ℂ := fun w => (f (diskAutomorphism a w) - f a) / (δ * deriv f a)
  have hφd := diskAutomorphism_differentiableOn ha
  have hφm := diskAutomorphism_mapsTo ha
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    ((hd.comp hφd hφm).sub_const _).div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro z hz w hw he
    apply diskAutomorphism_injOn ha hz hw
    apply hi (hφm hz) (hφm hw)
    exact sub_left_inj.mp ((div_left_inj' (mul_ne_zero hδ hfn)).mp he)
  have hg0 : g 0 = 0 := by simp [g]
  have hφ0 : HasDerivAt (diskAutomorphism a) δ 0 := by
    convert diskAutomorphism_hasDerivAt (z := 0) ha (by simp) using 1; simp [δ]
  have hfa := hd.analyticAt (isOpen_ball.mem_nhds ha')
  have hfac : HasDerivAt f (deriv f a) (diskAutomorphism a 0) := by
    simpa using hfa.differentiableAt.hasDerivAt
  have hg1 : deriv g 0 = 1 := by
    have hp := ((hfac.comp 0 hφ0).sub_const (f a)).div_const (δ * deriv f a)
    convert hp.deriv using 1
    all_goals first | rfl | field_simp
  have hφa := hφd.analyticAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hF : AnalyticAt ℂ (f ∘ diskAutomorphism a) 0 :=
    (show AnalyticAt ℂ f (diskAutomorphism a 0) by simpa using hfa).comp hφa
  have hg2 : deriv (deriv g) 0 = δ * (deriv (deriv f) a / deriv f a) - 2 * conj a := by
    change deriv (deriv (fun w => ((f ∘ diskAutomorphism a) w - f a) /
      (δ * deriv f a))) 0 = _
    rw [second_deriv_normalize hF]
    rw [second_deriv_comp (by simpa using hfa) hφa]
    simp only [diskAutomorphism_zero, diskAutomorphism_deriv_zero ha,
      diskAutomorphism_second_deriv_zero ha]
    dsimp only [δ]
    dsimp only [δ] at hδ
    field_simp
    ring
  have hb := second_deriv_norm_le_four hgd hgi hg0 hg1
  rw [hg2] at hb
  simpa only [δ, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, ofReal_sub, ofReal_pow,
    ofReal_one] using hb

lemma hasDerivAt_log_norm {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) (hn : g t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖g s‖) (g' / g t).re t := by
  have hp := (hg.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).div_const 2
  have he : (fun s => Real.log (‖g s‖ ^ 2) / 2) = (fun s => Real.log ‖g s‖) := by
    funext s
    rw [Real.log_pow]
    ring
  have hv : (2 * inner ℝ (g t) g' / ‖g t‖ ^ 2) / 2 = (g' / g t).re := by
    rw [Complex.inner, Complex.div_re, ← normSq_eq_norm_sq]
    simp only [mul_re, conj_re, conj_im]
    ring
  convert hp using 1
  all_goals first | rfl | exact he.symm | exact hv.symm

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma radial_preSchwarzian_bounds {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hu : ‖u‖ = 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    (2 * t - 4) / (1 - t ^ 2) ≤
        (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ∧
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re ≤
        (2 * t + 4) / (1 - t ^ 2) := by
  have hnorm : ‖(t : ℂ) * u‖ = t := by simp [hu, abs_of_nonneg ht]
  have hsu : conj u * u = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hu]
    norm_num
  have hb := preSchwarzian_bound hd hi (a := (t : ℂ) * u) (by rwa [hnorm])
  rw [hnorm] at hb
  let p : ℂ := deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)
  have he : ((1 - (t ^ 2 : ℝ) : ℂ) * p - 2 * conj ((t : ℂ) * u)) * u =
      (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) := by
    simp only [map_mul, conj_ofReal, sub_mul]
    calc
      _ = (1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ) * (conj u * u) := by ring
      _ = _ := by rw [hsu, mul_one]; ring
  have hb' : ‖(1 - (t ^ 2 : ℝ) : ℂ) * (p * u) - 2 * (t : ℂ)‖ ≤ 4 := by
    rw [← he, norm_mul, hu, mul_one]
    exact hb
  have hh := (Complex.abs_re_le_norm _).trans hb'
  have hh' : |(1 - t ^ 2) * (p * u).re - 2 * t| ≤ 4 := by
    simpa [← ofReal_pow, Complex.mul_re] using hh
  have hp : 0 < 1 - t ^ 2 := by nlinarith
  have hlo := (abs_le.mp hh').1
  have hhi := (abs_le.mp hh').2
  have hval : (p * u).re =
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re := by
    congr 1
    dsimp only [p]
    ring
  rw [← hval]
  constructor
  · exact (div_le_iff₀ hp).mpr (by nlinarith)
  · exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma hasDerivAt_radial_log_deriv {f : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1) :
    HasDerivAt (fun s : ℝ => Real.log ‖deriv f ((s : ℂ) * u)‖)
      (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re t := by
  have hdf := (hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hmem)
  have hp := (hdf.hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const u)).comp_ofReal
  apply hasDerivAt_log_norm _ (deriv_ne_zero_of_injOn isOpen_ball hmem hi hd)
  simpa only [Function.comp_apply, id_eq, one_mul] using hp

lemma log_derivative_distortion_radial {f : ℂ → ℂ} {u : ℂ} {r : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hu : ‖u‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log (1 - r) - 3 * Real.log (1 + r) ≤ Real.log ‖deriv f ((r : ℂ) * u)‖ ∧
      Real.log ‖deriv f ((r : ℂ) * u)‖ ≤ Real.log (1 + r) - 3 * Real.log (1 - r) := by
  let A : ℝ → ℝ := fun t => Real.log ‖deriv f ((t : ℂ) * u)‖
  let D : ℝ → ℝ := fun t =>
    (deriv (deriv f) ((t : ℂ) * u) * u / deriv f ((t : ℂ) * u)).re
  have hrad (t : ℝ) (ht : t ∈ Icc 0 r) : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball, dist_zero_right, hu, abs_of_nonneg ht.1] using ht.2.trans_lt hr1
  have hA (t : ℝ) (ht : t ∈ Icc 0 r) : HasDerivAt A (D t) t :=
    hasDerivAt_radial_log_deriv hd hi (hrad t ht)
  have hL (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 - s) - 3 * Real.log (1 + s))
        ((2 * t - 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdminus.log hm).sub ((hdplus.log hp).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hU (t : ℝ) (ht : t ∈ Icc 0 r) :
      HasDerivAt (fun s : ℝ => Real.log (1 + s) - 3 * Real.log (1 - s))
        ((2 * t + 4) / (1 - t ^ 2)) t := by
    have hm : 1 - t ≠ 0 := by linarith [ht.2]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have hdminus : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hdplus : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    have h := (hdplus.log hp).sub ((hdminus.log hm).const_mul 3)
    convert! h using 1
    field_simp
    ring
  have hbounds (t : ℝ) (ht : t ∈ Icc 0 r) :=
    radial_preSchwarzian_bounds hd hi hu ht.1 (ht.2.trans_lt hr1)
  have hmonoL : MonotoneOn (fun t => A t -
      (Real.log (1 - t) - 3 * Real.log (1 + t))) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hA t ht).sub (hL t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hA t (interior_subset ht)).sub
        (hL t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (A - (fun s => Real.log (1 - s) - 3 * Real.log (1 + s))) t
      rw [((hA t (interior_subset ht)).sub (hL t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).1
  have hmonoU : MonotoneOn (fun t =>
      (Real.log (1 + t) - 3 * Real.log (1 - t)) - A t) (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    · exact fun t ht => ((hU t ht).sub (hA t ht)).continuousAt.continuousWithinAt
    · exact fun t ht => ((hU t (interior_subset ht)).sub
        (hA t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv ((fun s => Real.log (1 + s) - 3 * Real.log (1 - s)) - A) t
      rw [((hU t (interior_subset ht)).sub (hA t (interior_subset ht))).deriv]
      exact sub_nonneg.mpr (hbounds t (interior_subset ht)).2
  have hlo := hmonoL (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hhi := hmonoU (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  simp only [A, ofReal_zero, zero_mul, h1, norm_one, Real.log_one, sub_zero, add_zero,
    mul_zero, sub_self] at hlo hhi
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

theorem derivative_distortion {f : ℂ → ℂ} {z : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h1 : deriv f 0 = 1) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖) ^ 3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
  by_cases hz0 : z = 0
  · subst z
    simp [h1]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  let u : ℂ := z / (‖z‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, hr.ne']
  have he : (‖z‖ : ℂ) * u = z := by
    dsimp only [u]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  have hb := log_derivative_distortion_radial hd hi h1 hu hr.le hz
  rw [he] at hb
  have hm : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hdf : 0 < ‖deriv f z‖ := norm_pos_iff.mpr
    (deriv_ne_zero_of_injOn isOpen_ball (by simpa using hz) hi hd)
  have expL : Real.exp (Real.log (1 - ‖z‖) - 3 * Real.log (1 + ‖z‖)) =
      (1 - ‖z‖) / (1 + ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 + ‖z‖) = Real.log ((1 + ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hm, Real.exp_log (pow_pos hp 3)]
  have expU : Real.exp (Real.log (1 + ‖z‖) - 3 * Real.log (1 - ‖z‖)) =
      (1 + ‖z‖) / (1 - ‖z‖) ^ 3 := by
    rw [show 3 * Real.log (1 - ‖z‖) = Real.log ((1 - ‖z‖) ^ 3) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_sub, Real.exp_log hp, Real.exp_log (pow_pos hm 3)]
  constructor
  · simpa only [expL, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.1
  · simpa only [expU, Real.exp_log hdf] using Real.exp_le_exp.mpr hb.2

end
end StrictInverseFirstPower

end

end OAI
