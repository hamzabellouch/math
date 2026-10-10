import OAI.NumberTheory.EgyptianFractions.CyclicKernel
import OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound
import OAI.NumberTheory.EgyptianFractions.CyclicInterval
import OAI.NumberTheory.EgyptianFractions.FejerBudget
import OAI.NumberTheory.EgyptianFractions.FejerSampleMean

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- The geometric and counting part of cyclic discrepancy. The sampled
spectral-mean input is separated from the exact kernel normalization. -/
theorem initial_interval_count_of_kernel_mean {q h d : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (ε : ℝ)
    (hh : 0 < h) (hhq : h ≤ q) (hd : 0 < d) (hdq : 7 * d < q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((h : ℝ) - 1) * ε) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) :
    (samples.card : ℝ) *
      (((6 * d + 1 : ℕ) : ℝ) / q -
        (((6 * d + 1 : ℕ) : ℝ) / q) * ((h : ℝ) - 1) * ε -
        (((6 * d + 1 : ℕ) : ℝ) / q) / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) ≤
      ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := by
  classical
  let inner : Finset (ZMod q) := Finset.univ.filter (fun y => d ≤ y.val ∧ y.val ≤ 7 * d)
  let outer : Finset (ZMod q) := Finset.univ.filter (fun z => z.val < 8 * d)
  let A : ℝ := (inner.card : ℝ) / q
  let η : ℝ := (1 / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ : 0 < (d : ℝ) / q := div_pos hdR hqR
  have hcard : inner.card = 6 * d + 1 := by
    change (Finset.univ.filter (fun y : ZMod q => d ≤ y.val ∧ y.val ≤ 7 * d)).card = _
    rw [cyclic_interval_card d (7 * d) hdq]
    omega
  have htail : ∀ z : ZMod q, z ∉ outer → ∀ y ∈ inner,
      normalizedKernel h (z - y) ≤ η := by
    intro z hz y hy
    have hz' : 8 * d ≤ z.val := by simpa [outer] using hz
    have hy' : d ≤ y.val ∧ y.val ≤ 7 * d := by simpa [inner] using hy
    obtain ⟨hleft, hright⟩ := cyclic_initial_interval_phase_margin z y d (7 * d)
      (by omega) hy'
    have hb := stdAddChar_fejer_le_middle (z - y) hβ hleft hright hh
    rw [GeometricKernel.cyclic_geometric_sum_eq] at hb
    exact div_le_div_of_nonneg_right hb hqR.le
  have hsampled : (samples.card : ℝ) *
      ((inner.card : ℝ) / Fintype.card (ZMod q) - A * ((h : ℝ) - 1) * ε) ≤
      ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
    have hsum := Finset.sum_le_sum (fun y (_ : y ∈ inner) => hmean y)
    have hdiv := div_le_div_of_nonneg_right hsum hqR.le
    simp only [Finset.sum_const, nsmul_eq_mul] at hdiv
    have hright : (∑ y ∈ inner, ∑ ω ∈ samples,
        GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) / (q : ℝ) =
        ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [window, normalizedKernel, Finset.sum_div]
    rw [hright] at hdiv
    convert hdiv using 1
    simp only [ZMod.card, A]
    ring
  have hcount := count_window_lower (normalizedKernel h) inner outer samples x
    (A * ((h : ℝ) - 1) * ε) η (normalizedKernel_nonneg h)
    (sum_normalizedKernel hh hhq) (by dsimp [η]; positivity) htail hsampled
  have hfilter : samples.filter (fun ω => x ω ∈ outer) =
      samples.filter (fun ω => (x ω).val < 8 * d) := by simp [outer]
  rw [hfilter] at hcount
  convert hcount using 1
  simp only [ZMod.card, A, η, hcard]
  ring

/-- With the explicit low-degree choice, the smoothing errors leave half of
the desired interval mass. This lemma isolates the sampled kernel mean. -/
theorem cyclic_small_interval_of_kernel_mean {q : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((⌊1 / (64 * δ ^ 3)⌋₊ : ℝ) - 1) * δ ^ 3) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel ⌊1 / (64 * δ ^ 3)⌋₊
          (ZMod.stdAddChar (x ω - y))) :
    (δ / 2) * (samples.card : ℝ) ≤
      ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  let h : ℕ := ⌊1 / (64 * δ ^ 3)⌋₊
  let d : ℕ := ⌊δ * q / 8⌋₊
  obtain ⟨hd1, hdq, hdouter, hdmargin, hinnerLo, hinnerHi⟩ :=
    cyclic_interval_floor_budget δ q hδ (by linarith) hscale
  obtain ⟨hh1, hhLo, hhHi, hleak, herror⟩ := fejer_degree_floor_budget δ hδ hsmall
  change 1 ≤ h at hh1
  change 1 ≤ d at hd1
  have hh : 0 < h := by omega
  have hd : 0 < d := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hhR1 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  let A : ℝ := ((6 * d + 1 : ℕ) : ℝ) / q
  let β : ℝ := (d : ℝ) / q
  have hβ : 0 < β := by dsimp [β]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAhi : A ≤ δ := hinnerHi
  have hAlo : 11 * δ / 16 ≤ A := hinnerLo
  have hβlo : δ / 16 ≤ β := hdmargin
  have hE : A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ / 32 := by
    calc
      A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ * (h : ℝ) * δ ^ 3 := by gcongr; linarith
      _ ≤ 2 * (h : ℝ) * δ * δ ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hδ.le hhR.le) (show 0 ≤ δ ^ 3 by positivity)]
      _ ≤ δ / 32 := herror
  have hL : A / (4 * (h : ℝ) * β ^ 2) ≤ δ / 8 := by
    calc
      A / (4 * (h : ℝ) * β ^ 2) ≤ δ / (4 * (h : ℝ) * β ^ 2) := by
        exact div_le_div_of_nonneg_right hAhi (by positivity)
      _ ≤ δ / (4 * (h : ℝ) * (δ / 16) ^ 2) := by
        apply div_le_div_of_nonneg_left hδ.le (by positivity)
        gcongr
      _ = 64 / ((h : ℝ) * δ) := by field_simp; ring
      _ ≤ δ / 8 := hleak
  have hbudget : δ / 2 ≤ A - A * ((h : ℝ) - 1) * δ ^ 3 -
      A / (4 * (h : ℝ) * β ^ 2) :=
    fejer_localization_budget δ _ A _ _ hδ.le hAlo hE hL le_rfl
  have hcount := initial_interval_count_of_kernel_mean samples x (δ ^ 3)
    hh hdegree hd hdq hmean
  have hsubset : samples.filter (fun ω => (x ω).val < 8 * d) ⊆
      samples.filter (fun ω => ((x ω).val : ℝ) < δ * q) := by
    intro ω hω
    obtain ⟨hω, hval⟩ := Finset.mem_filter.mp hω
    refine Finset.mem_filter.mpr ⟨hω, ?_⟩
    have hv : ((x ω).val : ℝ) < (8 * d : ℕ) := by exact_mod_cast hval
    exact hv.trans_le hdouter
  calc
    (δ / 2) * (samples.card : ℝ) ≤ (samples.card : ℝ) *
        (A - A * ((h : ℝ) - 1) * δ ^ 3 - A / (4 * (h : ℝ) * β ^ 2)) := by
      simpa only [mul_comm (δ / 2)] using
        mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg samples.card)
    _ ≤ ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := hcount
    _ ≤ ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

/-- Genuine finite cyclic low-frequency discrepancy, with no sampled-kernel
hypothesis remaining. Repeated samples are allowed. -/
theorem cyclic_small_interval_of_fourier {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hh : 0 < ⌊1 / (64 * δ ^ 3)⌋₊ := by
      have hb := (fejer_degree_floor_budget δ hδ hsmall).1
      omega
    have hfreq := fejer_degree_frequency_bound δ hδ hsmall
    apply cyclic_small_interval_of_kernel_mean Finset.univ x δ hδ hsmall hscale hdegree
    intro y
    have hm := FejerSampleMean.fejer_sample_mean_lower hh x y (δ ^ 3)
      (fun l hl hlh => hfourier l hl (by omega))
    have hm' := (le_div_iff₀ hN).mp hm
    simpa only [Finset.card_univ, mul_comm] using hm'

/-- Finset-indexed version of the same discrepancy bound. -/
theorem cyclic_small_interval_of_fourier_finset {q : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω ∈ samples, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (samples.card : ℝ) * δ ^ 3) :
    (δ / 2) * (samples.card : ℝ) ≤
      ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  have hF : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : samples, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card samples : ℝ) * δ ^ 3 := by
    intro l hl hlH
    rw [Finset.sum_coe_sort samples (fun ω => ZMod.stdAddChar ((l : ZMod q) * x ω)),
      Fintype.card_coe]
    exact hfourier l hl hlH
  have hc := cyclic_small_interval_of_fourier (fun ω : samples => x ω) δ
    hδ hsmall hscale hdegree hF
  have hcard : (Finset.univ.filter (fun ω : samples =>
      ((x ω).val : ℝ) < δ * q)).card =
      (samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort samples (fun ω => if ((x ω).val : ℝ) < δ * q then 1 else 0)
  simpa only [Fintype.card_coe, hcard] using hc

end Problem337.CyclicSmoothing

end

end OAI
