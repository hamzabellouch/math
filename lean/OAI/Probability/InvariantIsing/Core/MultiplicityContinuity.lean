import OAI.Probability.InvariantIsing.Spectral.SpectralMultiplicity

namespace OAI

/-! Asymptotic removal of finite-alphabet multiplicity restrictions. The
comparison only uses the limiting positive group proportions. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma eventually_relative_count_bound {A : Type*} [Fintype A]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (a b : ℕ → A → ℕ)
    (rho tau : A → ℝ) (hrho : ∀ v, 0 < rho v) (htau : ∀ v, 0 < tau v)
    (ha : Tendsto (fun k v => (a k v : ℝ) / N k) atTop (𝓝 rho))
    (hb : Tendsto (fun k v => (b k v : ℝ) / N k) atTop (𝓝 tau))
    (R : ℝ) (hR : ∀ v, |rho v - tau v| / min (rho v) (tau v) < R) :
    ∀ᶠ k in atTop, ∀ v,
      |(a k v : ℝ) - b k v| ≤ R * min (a k v : ℝ) (b k v : ℝ) := by
  apply Filter.eventually_all.mpr
  intro v
  have hα := (tendsto_pi_nhds.mp ha) v
  have hβ := (tendsto_pi_nhds.mp hb) v
  have hden := hα.min hβ
  have hpos : 0 < min (rho v) (tau v) := lt_min (hrho v) (htau v)
  have hratio := (hα.sub hβ).abs.div hden (ne_of_gt hpos)
  filter_upwards [hratio.eventually (Iio_mem_nhds (hR v)),
    hden.eventually (Ioi_mem_nhds hpos)] with k hk hdk
  have hfrac : |(a k v : ℝ) / N k - (b k v : ℝ) / N k| ≤
      R * min ((a k v : ℝ) / N k) ((b k v : ℝ) / N k) :=
    ((div_lt_iff₀ (show 0 < min ((a k v : ℝ) / N k) ((b k v : ℝ) / N k) from hdk)).mp hk).le
  have hn : 0 < (N k : ℝ) := by exact_mod_cast hN k
  rw [← sub_div, abs_div, abs_of_pos hn, min_div_div_right hn.le,
    ← mul_div_assoc] at hfrac
  exact (div_le_div_iff_of_pos_right hn).mp hfrac

lemma eventually_surjective_label {N : ℕ → ℕ} {m : ℕ}
    (hN : ∀ k, 0 < N k) (a : (k : ℕ) → Fin (N k) → Fin m)
    (rho : Fin m → ℝ) (hrho : ∀ v, 0 < rho v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k)
      atTop (𝓝 rho)) :
    ∀ᶠ k in atTop, Function.Surjective (a k) := by
  have hall : ∀ v, ∀ᶠ k in atTop,
      0 < ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k :=
    fun v => ((tendsto_pi_nhds.mp ha) v).eventually (Ioi_mem_nhds (hrho v))
  filter_upwards [Filter.eventually_all.mpr hall] with k hk
  intro v
  have hn : 0 < (N k : ℝ) := by exact_mod_cast hN k
  have hp : (0 : ℝ) < (Finset.univ.filter fun i => a k i = v).card :=
    (div_pos_iff_of_pos_right hn).mp (hk v)
  have hcard : 0 < (Finset.univ.filter fun i => a k i = v).card := by exact_mod_cast hp
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- Two spectra with the same finite alphabet and the same positive limiting
proportions have asymptotically equal Haar mean pressures. -/
theorem meanPressure_same_proportions_tendsto {m : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] (hμ : ∀ k, (μ k).IsMulLeftInvariant)
    (a b : (k : ℕ) → Fin (N k) → Fin m)
    (rho : Fin m → ℝ) (hrho : ∀ v, 0 < rho v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i = v).card : ℝ) / N k)
      atTop (𝓝 rho))
    (hb : Tendsto (fun k v => ((Finset.univ.filter fun i => b k i = v).card : ℝ) / N k)
      atTop (𝓝 rho))
    (lam : Fin m → ℝ) (c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L : ℝ) (hL : 0 ≤ L) (hdiam : ∀ v w, |lam v - lam w| ≤ L) :
    Tendsto (fun k =>
      (∫ U, rotatedPressure (fun i => lam (b k i)) (specialRotation U) (c k) ∂μ k) -
        ∫ U, rotatedPressure (fun i => lam (a k i)) (specialRotation U) (c k) ∂μ k)
      atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let R := ε / (L + 1)
  have hR : 0 < R := div_pos hε (by linarith)
  have hc := eventually_relative_count_bound N hN
    (fun k v => (Finset.univ.filter fun i => a k i = v).card)
    (fun k v => (Finset.univ.filter fun i => b k i = v).card)
    rho rho hrho hrho ha hb R (fun v => by simpa only [sub_self, abs_zero, zero_div] using hR)
  filter_upwards [hc, eventually_surjective_label hN a rho hrho ha,
    eventually_surjective_label hN b rho hrho hb] with k hk hka hkb
  let := hμ k
  have hp := meanPressure_multiplicity_comparison (hN k) (μ k)
    (a k) (b k) hka hkb lam (c k) K hK L R hL hR.le hdiam hk
  have he : R * (L + 1) = ε := div_mul_cancel₀ ε (by linarith : L + 1 ≠ 0)
  have hsmall : L * R / 2 < ε := by nlinarith
  simpa only [Real.dist_eq, sub_zero] using hp.trans_lt hsmall

end InvariantIsing

end

end OAI
