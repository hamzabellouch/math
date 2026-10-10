import Mathlib

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337

/-- A fixed affine function of the iterated logarithm is negligible beside
any positive multiple of the logarithm. -/
theorem eventually_affine_loglog_le_log (A B c : ℝ) (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop, A + B * Real.log (Real.log S) ≤ c * Real.log S := by
  have hratio : Tendsto (fun S : ℝ =>
      (A + B * Real.log (Real.log S)) / Real.log S) atTop (𝓝 0) := by
    have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      Real.tendsto_log_atTop
    have hconst : Tendsto (fun S : ℝ => A / Real.log S) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    convert hconst.add (hlog.const_mul B) using 1 <;> simp [add_div, mul_div_assoc]
  filter_upwards [hratio.eventually (gt_mem_nhds hc),
    (eventually_gt_atTop (1 : ℝ))] with S hratio hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  exact le_of_lt ((div_lt_iff₀ hlogS).mp hratio)

/-- Uniform analytic domination for the intermediate-prime band. The
conditions on `B`, `Q`, and the logarithmic factor are the coarse bounds
obtained from the manuscript's ranges for `v` and `t`. -/
theorem eventually_intermediate_band_envelope
    (r C E : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hE : 0 < E) :
    ∀ᶠ S : ℝ in atTop, ∀ B Q L : ℝ,
      B ≤ 1 + Real.log (2 * E * Real.log S) →
      S ^ (1 / 32 : ℝ) ≤ Q → L ≤ 2 * Real.log S →
      r * B * Q - Q * Real.log Q / 50 + C * Q ^ (1 / 5 : ℝ) * L ≤
        -(Q * Real.log Q) / 100 := by
  have hsmall := eventually_affine_loglog_le_log
    (r * (1 + Real.log (2 * E))) r (1 / 6400) (by norm_num)
  have hlarge : ∀ᶠ S : ℝ in atTop, 12800 * C ≤ S ^ (1 / 40 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).eventually
      (eventually_ge_atTop (12800 * C))
  filter_upwards [hsmall, hlarge, eventually_gt_atTop (1 : ℝ)] with S hsmall hlarge hS
  intro B Q L hB hQ hL
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.rpow_pos_of_pos hSpos _) hQ
  have hlogQ : Real.log S / 32 ≤ Real.log Q := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hSpos (1 / 32)) hQ
    rw [Real.log_rpow hSpos] at h
    linarith
  have hB' : r * B ≤ Real.log S / 6400 := by
    have hlogmul : Real.log (2 * E * Real.log S) =
        Real.log (2 * E) + Real.log (Real.log S) :=
      Real.log_mul (by positivity) (ne_of_gt hlogS)
    rw [hlogmul] at hB
    have h := mul_le_mul_of_nonneg_left hB hr
    nlinarith
  have hfirst : r * B * Q ≤ Q * Real.log Q / 200 := by
    have h := mul_le_mul_of_nonneg_right hB' (le_of_lt hQpos)
    have h' := mul_le_mul_of_nonneg_left hlogQ (le_of_lt hQpos)
    nlinarith
  have hqpow : 12800 * C ≤ Q ^ (4 / 5 : ℝ) := by
    have h := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hSpos _)) hQ
      (by norm_num : (0 : ℝ) ≤ 4 / 5)
    rw [← Real.rpow_mul (le_of_lt hSpos)] at h
    norm_num at h
    exact hlarge.trans h
  have hpowprod : Q ^ (1 / 5 : ℝ) * Q ^ (4 / 5 : ℝ) = Q := by
    rw [← Real.rpow_add hQpos]
    norm_num
  have hqpow' : 12800 * C * Q ^ (1 / 5 : ℝ) ≤ Q := by
    have h := mul_le_mul_of_nonneg_left hqpow
      (le_of_lt (Real.rpow_pos_of_pos hQpos (1 / 5)))
    rw [hpowprod] at h
    nlinarith
  have hsecond : C * Q ^ (1 / 5 : ℝ) * L ≤ Q * Real.log Q / 200 := by
    have h := mul_le_mul_of_nonneg_left hL
      (mul_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hQpos (1 / 5))))
    have h' := mul_le_mul_of_nonneg_right hqpow' (le_of_lt hlogS)
    have h'' := mul_le_mul_of_nonneg_left hlogQ (le_of_lt hQpos)
    nlinarith
  linarith

/-- The lower endpoint in the divisor-moment range eventually exceeds the
square root of the main parameter. -/
theorem eventually_rpow_half_le_log_range :
    ∀ᶠ S : ℝ in atTop, S ^ (1 / 2 : ℝ) ≤ S / (2 * Real.log S) := by
  have hratio := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (1 : ℝ)] with S hratio hS
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hroot : 0 < S ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hsmall : 2 * Real.log S ≤ S ^ (1 / 2 : ℝ) := by
    have h := (div_lt_iff₀ hroot).mp hratio
    linarith
  have hsquare : S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) = S := by
    rw [← Real.rpow_add hSpos]
    norm_num
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).2
  have h := mul_le_mul_of_nonneg_left hsmall (le_of_lt hroot)
  rw [hsquare] at h
  exact h

/-- The exact uniform intermediate-band estimate from the divisor-moment
argument. Constants remain fixed while `S`, `v`, and `t` vary. -/
theorem eventually_divisor_intermediate_band_decay
    (D r C : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v t : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      4 * Real.log S ≤ t → t ≤ v ^ (15 / 16 : ℝ) →
      r * (1 + Real.log ((D + 1) * S / v)) * (v / t) -
          (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤
        -((v / t) * Real.log (v / t)) / 100 := by
  have hE : 0 < D + 1 := by linarith
  filter_upwards [eventually_intermediate_band_envelope r C (D + 1) hr hC hE,
    eventually_rpow_half_le_log_range, eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (2 * D)] with S henv hroot hS hSD
  intro v t hvlow hvhigh htlow hthigh
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hvroot : S ^ (1 / 2 : ℝ) ≤ v := hroot.trans hvlow
  have hvpos : 0 < v := lt_of_lt_of_le (Real.rpow_pos_of_pos hSpos _) hvroot
  have hvone : 1 ≤ v := by
    have h := Real.one_le_rpow (le_of_lt hS) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact h.trans hvroot
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) htlow
  apply henv (1 + Real.log ((D + 1) * S / v)) (v / t) (Real.log (2 * t))
  · apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    apply (div_le_iff₀ hvpos).2
    have h := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hvlow
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt hE)
    nlinarith
  · have hvpower : S ^ (1 / 32 : ℝ) ≤ v ^ (1 / 16 : ℝ) := by
      have h := Real.rpow_le_rpow
        (le_of_lt (Real.rpow_pos_of_pos hSpos (1 / 2))) hvroot
        (by norm_num : (0 : ℝ) ≤ 1 / 16)
      rw [← Real.rpow_mul (le_of_lt hSpos)] at h
      norm_num at h
      exact h
    apply hvpower.trans
    apply (le_div_iff₀ htpos).2
    have h := mul_le_mul_of_nonneg_left hthigh
      (le_of_lt (Real.rpow_pos_of_pos hvpos (1 / 16)))
    have heq : v ^ (1 / 16 : ℝ) * v ^ (15 / 16 : ℝ) = v := by
      rw [← Real.rpow_add hvpos]
      norm_num
    rw [heq] at h
    exact h
  · have htv : t ≤ v := by
      apply hthigh.trans
      conv_rhs => rw [← Real.rpow_one v]
      exact Real.rpow_le_rpow_of_exponent_le hvone (by norm_num)
    have htsq : 2 * t ≤ S ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hSD (le_of_lt hSpos)
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < 2 * t) htsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- Fixed affine logarithmic functions are dominated by any positive power. -/
theorem eventually_affine_log_le_rpow (A B δ a : ℝ)
    (hδ : 0 < δ) (ha : 0 < a) :
    ∀ᶠ S : ℝ in atTop, A + B * Real.log S ≤ δ * S ^ a := by
  have hlog := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have hconst : Tendsto (fun S : ℝ => A / S ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
  have hratio : Tendsto (fun S : ℝ => (A + B * Real.log S) / S ^ a)
      atTop (𝓝 0) := by
    convert hconst.add (hlog.const_mul B) using 1 <;> simp [add_div, mul_div_assoc]
  filter_upwards [hratio.eventually (gt_mem_nhds hδ),
    eventually_gt_atTop (0 : ℝ)] with S hratio hS
  exact le_of_lt ((div_lt_iff₀ (Real.rpow_pos_of_pos hS a)).mp hratio)

/-- Every fixed sublinear power lies below the divisor-moment lower range. -/
theorem eventually_rpow_le_log_range (a : ℝ) (ha : a < 1) :
    ∀ᶠ S : ℝ in atTop, S ^ a ≤ S / (2 * Real.log S) := by
  have hsmall := eventually_affine_log_le_rpow 0 2 1 (1 - a)
    (by norm_num) (by linarith)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with S hsmall hS
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have h : 2 * Real.log S ≤ S ^ (1 - a) := by simpa using hsmall
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (Real.rpow_pos_of_pos hSpos a))
  have heq : S ^ a * S ^ (1 - a) = S := by
    rw [← Real.rpow_add hSpos]
    ring_nf
    exact Real.rpow_one S
  rw [heq] at hmul
  exact (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).2 hmul

/-- The pointwise divisor bound and smooth-prefix Euler-product loss are
uniformly negligible compared with the negative small-prime Rankin exponent. -/
theorem eventually_divisor_small_prime_absorption
    (E r C : ℝ) (hE : 0 < E) (hr : 0 ≤ r) (_hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v : ℝ,
      S / (2 * Real.log S) ≤ v →
      C * S ^ (2 / 5 : ℝ) +
        r * (S ^ (1 / 2 : ℝ) * Real.log (1 + E * S / Real.log 2) +
          2 * (1 + Real.log (E * S / v)) * v / Real.log S) ≤ v / 100 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let k : ℝ := E / Real.log 2
  have hk : 0 < k := div_pos hE hlog2
  have hfirst := eventually_affine_log_le_rpow
    (r * Real.log (1 + k)) r (1 / 300) (1 / 4)
    (by norm_num) (by norm_num)
  have hmiddle := eventually_affine_loglog_le_log
    (2 * r * (1 + Real.log (2 * E))) (2 * r) (1 / 300) (by norm_num)
  have hlast : ∀ᶠ S : ℝ in atTop, 300 * C ≤ S ^ (7 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually
      (eventually_ge_atTop (300 * C))
  filter_upwards [hfirst, hmiddle, hlast,
    eventually_rpow_le_log_range (3 / 4) (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with S hfirst hmiddle hlast hroot hS
  intro v hv
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hvroot : S ^ (3 / 4 : ℝ) ≤ v := hroot.trans hv
  have hvpos : 0 < v := lt_of_lt_of_le (Real.rpow_pos_of_pos hSpos _) hvroot
  have hlogbound : Real.log (1 + E * S / Real.log 2) ≤
      Real.log (1 + k) + Real.log S := by
    have harg : 1 + E * S / Real.log 2 = 1 + k * S := by dsimp [k]; ring
    rw [harg, ← Real.log_mul (by positivity : 1 + k ≠ 0) (ne_of_gt hSpos)]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hfirst' : r * Real.log (1 + E * S / Real.log 2) ≤
      S ^ (1 / 4 : ℝ) / 300 := by
    have h := mul_le_mul_of_nonneg_left hlogbound hr
    nlinarith
  have hterm1 : r * (S ^ (1 / 2 : ℝ) * Real.log (1 + E * S / Real.log 2)) ≤
      v / 300 := by
    have h := mul_le_mul_of_nonneg_left hfirst'
      (le_of_lt (Real.rpow_pos_of_pos hSpos (1 / 2)))
    have heq : S ^ (1 / 2 : ℝ) * S ^ (1 / 4 : ℝ) = S ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hSpos]
      norm_num
    have h' : S ^ (1 / 2 : ℝ) * (S ^ (1 / 4 : ℝ) / 300) =
        S ^ (3 / 4 : ℝ) / 300 := by rw [← mul_div_assoc, heq]
    rw [h'] at h
    nlinarith
  have hB : 1 + Real.log (E * S / v) ≤
      1 + Real.log (2 * E) + Real.log (Real.log S) := by
    have harg : E * S / v ≤ 2 * E * Real.log S := by
      apply (div_le_iff₀ hvpos).2
      have h := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hv
      have h' := mul_le_mul_of_nonneg_left h (le_of_lt hE)
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < E * S / v) harg
    rw [Real.log_mul (by positivity : 2 * E ≠ 0) (ne_of_gt hlogS)] at h
    linarith
  have hmid : 2 * r * (1 + Real.log (E * S / v)) ≤ Real.log S / 300 := by
    have h := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * r)
    nlinarith
  have hterm2 : r * (2 * (1 + Real.log (E * S / v)) * v / Real.log S) ≤
      v / 300 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hlogS).2
    have h := mul_le_mul_of_nonneg_right hmid (le_of_lt hvpos)
    nlinarith
  have hterm3 : C * S ^ (2 / 5 : ℝ) ≤ v / 300 := by
    have h := mul_le_mul_of_nonneg_right hlast
      (le_of_lt (Real.rpow_pos_of_pos hSpos (2 / 5)))
    have heq : S ^ (7 / 20 : ℝ) * S ^ (2 / 5 : ℝ) = S ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hSpos]
      norm_num
    rw [heq] at h
    nlinarith
  linarith

/-- An eventual estimate in `v` holds uniformly throughout the logarithmic
lower range of the divisor-moment lemma. -/
theorem eventually_uniform_in_log_range {P : ℝ → Prop}
    (hP : ∀ᶠ v : ℝ in atTop, P v) :
    ∀ᶠ S : ℝ in atTop, ∀ v : ℝ, S / (2 * Real.log S) ≤ v → P v := by
  obtain ⟨V, hV⟩ := eventually_atTop.1 hP
  have hlarge : ∀ᶠ S : ℝ in atTop, V ≤ S ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop V)
  filter_upwards [hlarge, eventually_rpow_half_le_log_range] with S hlarge hroot
  intro v hv
  exact hV v (hlarge.trans (hroot.trans hv))

/-- Uniform form of the positive logarithmic prefix gap used in both
small- and intermediate-prime ranges. -/
theorem eventually_divisor_prefix_gap :
    ∀ᶠ S : ℝ in atTop, ∀ v : ℝ, S / (2 * Real.log S) ≤ v →
      v / 5 < v / 4 - v ^ (15 / 16 : ℝ) := by
  apply eventually_uniform_in_log_range
  have hlarge : ∀ᶠ v : ℝ in atTop, 20 < v ^ (1 / 16 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).eventually
      (eventually_gt_atTop 20)
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with v hlarge hv
  have h := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hv (15 / 16))
  have heq : v ^ (15 / 16 : ℝ) * v ^ (1 / 16 : ℝ) = v := by
    rw [← Real.rpow_add hv]
    norm_num
  rw [heq] at h
  linarith

/-- The Rankin exponent chosen in each intermediate band stays in the
uniform interval required by the Euler local-factor estimate. -/
theorem eventually_divisor_band_rankin_parameter (D : ℝ) (_hD : 1 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ v t : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      4 * Real.log S ≤ t → t ≤ v ^ (15 / 16 : ℝ) →
      0 < Real.log (v / t) / (10 * t) ∧
        Real.log (v / t) / (10 * t) < 1 / 4 := by
  have hDlog : ∀ᶠ S : ℝ in atTop, D ≤ 4 * Real.log S := by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (D / 4))]
      with S hS
    linarith
  filter_upwards [eventually_uniform_in_log_range (eventually_gt_atTop (1 : ℝ)),
    hDlog, eventually_gt_atTop (1 : ℝ)] with S hvlarge hDlog hS
  intro v t hvlow hvhigh htlow hthigh
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hvone : 1 < v := hvlarge v hvlow
  have hvpos : 0 < v := lt_trans (by norm_num) hvone
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) htlow
  have hqone : 1 < v / t := by
    have hpower : v ^ (15 / 16 : ℝ) < v := by
      conv_rhs => rw [← Real.rpow_one v]
      exact Real.rpow_lt_rpow_of_exponent_lt hvone (by norm_num)
    exact (one_lt_div htpos).2 (hthigh.trans_lt hpower)
  have hqS : v / t ≤ S := by
    apply (div_le_iff₀ htpos).2
    have h := mul_le_mul_of_nonneg_right hDlog (le_of_lt hSpos)
    have h' := mul_le_mul_of_nonneg_right htlow (le_of_lt hSpos)
    nlinarith
  have hlogq : Real.log (v / t) ≤ Real.log S :=
    Real.log_le_log (div_pos hvpos htpos) hqS
  constructor
  · exact div_pos (Real.log_pos hqone) (by positivity)
  · have h : Real.log (v / t) / (10 * t) ≤ 1 / 40 := by
      apply (div_le_iff₀ (by positivity : 0 < 10 * t)).2
      nlinarith
    linarith

/-- Direct interface for combining the small-prime smooth tail with an
arbitrarily small pointwise divisor exponent. -/
theorem eventually_small_rankin_exponent_le (C : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v R : ℝ,
      S / (2 * Real.log S) ≤ v → R ≤ v / 200 →
      -v / 50 + C * S ^ (2 / 5 : ℝ) + R ≤ -v / 100 := by
  have hlarge : ∀ᶠ S : ℝ in atTop, 200 * C ≤ S ^ (7 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually
      (eventually_ge_atTop (200 * C))
  filter_upwards [hlarge, eventually_rpow_le_log_range (3 / 4) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with S hlarge hroot hS
  intro v R hv hR
  have h := mul_le_mul_of_nonneg_right hlarge
    (le_of_lt (Real.rpow_pos_of_pos hS (2 / 5)))
  have heq : S ^ (7 / 20 : ℝ) * S ^ (2 / 5 : ℝ) = S ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hS]
    norm_num
  rw [heq] at h
  have hvroot := hroot.trans hv
  nlinarith

end Problem337

end

end OAI
