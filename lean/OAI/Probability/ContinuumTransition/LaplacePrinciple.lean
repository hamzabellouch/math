import OAI.Probability.ContinuumTransition.LaplaceBounds

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem density_compact_eventually {K : Set ℝ} (hK : IsCompact K)
    {P : ℝ × ℕ → Prop} (hP : ∀ d ∈ K, ∀ᶠ p in densityFilter d, P p) :
    ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ K → P (L,n) := by
  have hp : ∀ᶠ p in Filter.comap
      (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝ˢ K), P p := by
    rw [hK.prod_nhdsSet_eq_biSup, comap_iSup]
    simp only [comap_iSup, eventually_iSup]
    exact hP
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hp
  obtain ⟨T, hT, U, hU, hTU⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [hT] with L hL
  intro n hn
  exact hsub (hTU ⟨hL, (subset_of_mem_nhdsSet hU) hn⟩)

theorem canonicalDensity_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    d*Real.log d-(β*B+1)*d ≤ canonicalDensity φ β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have hlim := finiteCanonical_tendsto hφ ht hβ hstable hcore hd
  have he := ((Real.continuous_mul_log.continuousAt.tendsto).comp
    (densityFilter_density d)).sub ((densityFilter_density d).const_mul (β*B+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  dsimp only [Function.comp_def] at *
  nlinarith only [hh]

theorem entropy_dual_bound (c : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (c+1)*d-d*Real.log d ≤ Real.exp c := by
  obtain rfl | hd := hd.eq_or_lt
  · simp only [mul_zero, zero_mul, sub_self]
    exact (Real.exp_pos c).le
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c-Real.log d)) hd.le
  rw [Real.exp_sub, Real.exp_log hd, div_mul_cancel₀ _ hd.ne'] at hh
  nlinarith only [hh]

noncomputable def canonicalPressure (φ : ℝ → ℝ) (β μ : ℝ) : ℝ :=
  sSup ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)

theorem canonicalPressure_bddAbove {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    BddAbove ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*B), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem laplace_low_sector {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {D S ε : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hD : 0 < D) (hε : 0 < ε)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d))) :
    ∀ᶠ L in atTop, ∀ n : ℕ, n < ⌊D*L^3⌋₊+1 →
      w L n ≤ Real.exp (L^3*(S+ε)) := by
  have he : ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ Icc 0 D →
      Real.log (w L n)/L^3 < S+ε := by
    apply density_compact_eventually (K := Icc 0 D)
      (P := fun p => Real.log (w p.1 p.2)/p.1^3 < S+ε) isCompact_Icc
    intro d hd
    apply (hlim d hd.1).eventually_lt_const
    linarith [hF d hd.1]
  filter_upwards [he, eventually_gt_atTop 0] with L hL hp
  intro n hn
  have hn' : (n : ℝ) ≤ D*L^3 :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn)).trans (Nat.floor_le (by positivity))
  have hr : (n : ℝ)/L^3 ∈ Icc 0 D :=
    ⟨div_nonneg (Nat.cast_nonneg n) (pow_pos hp 3).le, (div_le_iff₀ (pow_pos hp 3)).2 hn'⟩
  apply (Real.log_le_iff_le_exp (hw L hp n)).1
  have hh := (div_lt_iff₀ (pow_pos hp 3)).1 (hL n hr)
  nlinarith only [hh]

theorem laplace_upper_eventually {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ}
    {D S : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hS : 0 ≤ S)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    ∀ q > S, ∀ᶠ L in atTop, Real.log (∑' n, w L n)/L^3 < q := by
  intro q hq
  let ε := (q-S)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := log_affine_cube_div_tendsto_zero (C := 1+∑' n, b n) hD
  have he := hlog.eventually_lt_const hε
  filter_upwards [laplace_low_sector hw hD hε hF hlim, htail, he,
    eventually_gt_atTop 0] with L hlow hhigh hsmall hL
  let M : ℕ := ⌊D*L^3⌋₊+1
  have hV : 0 < L^3 := pow_pos hL 3
  have hpos : 0 < ∑' n, w L n :=
    (hw L hL 0).trans_le ((hsum L hL).le_tsum 0 (fun n _ => (hw L hL n).le))
  have hh := log_tsum_div_le (hsum L hL) hb hb0 hpos (Nat.succ_pos _ : 0 < M)
    hV (show 0 ≤ S+ε by linarith) hlow (fun n hn => hhigh n (by
      apply (le_div_iff₀ hV).2
      have hm : D*L^3 < (M : ℝ) := by simpa [M] using Nat.lt_floor_add_one (D*L^3)
      exact hm.le.trans (Nat.cast_le.mpr hn)))
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hM : (M : ℝ)+∑' n, b n ≤ D*L^3+(1+∑' n, b n) := by
    have hf := Nat.floor_le (mul_nonneg hD.le hV.le)
    dsimp [M]
    push_cast
    linarith
  have hMpos : 0 < (M : ℝ)+∑' n, b n := by
    have hp : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    linarith
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hMpos hM) hV.le
  dsimp [ε] at *
  linarith only [hh, hl, hsmall]

theorem laplace_principle {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  have hnon : (F '' Ici 0).Nonempty := ⟨F 0, ⟨0, by simp, rfl⟩⟩
  have hF : ∀ d, 0 ≤ d → F d ≤ sSup (F '' Ici 0) :=
    fun d hd => le_csSup hbdd ⟨d, hd, rfl⟩
  have hS : 0 ≤ sSup (F '' Ici 0) := by simpa [hF0] using hF 0 le_rfl
  apply tendsto_order.2
  constructor
  · intro q hq
    obtain ⟨_, ⟨d, hd, rfl⟩, hqd⟩ := exists_lt_of_lt_csSup hnon hq
    have hdlim := (hlim d hd).comp (floor_density_tendsto hd)
    filter_upwards [hdlim.eventually_const_lt hqd, eventually_gt_atTop 0] with L hL hp
    have hh := (hsum L hp).le_tsum ⌊d*L^3⌋₊ (fun n _ => (hw L hp n).le)
    exact hL.trans_le (div_le_div_of_nonneg_right (Real.log_le_log (hw L hp _) hh)
      (pow_pos hp 3).le)
  · exact laplace_upper_eventually hw hsum hb hb0 hD hS hF hlim htail

end ContinuumTemperature
end

end OAI
