import OAI.Dynamics.EntropyCounterexample.EntropySparseCover

namespace OAI

noncomputable section

open Set SetRel Filter Function Dynamics
open scoped Topology Uniformity

namespace Problem340

lemma ereal_le_of_sparse_block_bounds {H : EReal} {A B m : ℝ}
    (h : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      H ≤ (((A + τ * B + C / n) / m : ℝ) : EReal)) :
    H ≤ ((A / m : ℝ) : EReal) := by
  have hτ : ∀ τ : ℝ, 0 < τ → H ≤ (((A + τ * B) / m : ℝ) : EReal) := by
    intro τ hτ
    obtain ⟨C, hC⟩ := h τ hτ
    have hlim : Tendsto (fun n : ℕ => (A + τ * B + C / n) / m)
        atTop (𝓝 ((A + τ * B) / m)) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_const_div_atTop_nhds_zero_nat C)).div_const m
    apply ge_of_tendsto (EReal.tendsto_coe.mpr hlim)
    exact eventually_atTop.mpr ⟨1, fun n hn => hC n (by omega)⟩
  have hlim : Tendsto (fun n : ℕ => (A + (1 / ((n : ℝ) + 1)) * B) / m)
      atTop (𝓝 (A / m)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const B)).div_const m
  apply ge_of_tendsto (EReal.tendsto_coe.mpr hlim)
  exact Eventually.of_forall fun n => hτ _ (by positivity)

lemma IsDynCoverOf.entropy_le_real_log_card_div {X : Type*}
    {T : X → X} {F : Set X} {U : SetRel X X} [U.IsSymm]
    (hF : MapsTo T F F) {s : Finset X} {n : ℕ}
    (hn : 0 < n) (hs : 0 < s.card) (hcover : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) ≤
      ((Real.log (s.card : ℝ) / n : ℝ) : EReal) := by
  have h := hcover.coverEntropyEntourage_le_log_card_div hF (Nat.ne_of_gt hn)
  have hlog : ENNReal.log (s.card : ENNReal) = (Real.log (s.card : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast Nat.ne_of_gt hs) (by simp)]
    simp
  rw [hlog] at h
  simpa only [EReal.coe_div, EReal.coe_natCast] using h

lemma log_sparse_word_bound {P Q m r k J : ℕ} {τ : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hm : 0 < m) (hr : 0 < r)
    (hk : (k : ℝ) ≤ τ * r + J) :
    Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) / (m * r) ≤
      (Real.log 2 + Real.log P + τ * Real.log Q +
        ((J : ℝ) * Real.log Q) / r) / m := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
  have hlog : Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) =
      (r : ℝ) * Real.log 2 + r * Real.log P + k * Real.log Q := by
    push_cast
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ hP'.ne')) (pow_ne_zero _ hQ'.ne'),
      Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hP'.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hlog]
  apply (div_le_div_iff₀ (mul_pos hm' hr') hm').mpr
  have hcost := mul_le_mul_of_nonneg_right hk hlogQ
  have hcancel : ((J : ℝ) * Real.log Q / r) * r = J * Real.log Q :=
    div_mul_cancel₀ _ hr'.ne'
  nlinarith

theorem coverEntropyEntourage_le_of_sparse_block_covers {X : Type*}
    {T : X → X} {F : Set X} {U : SetRel X X} [U.IsSymm]
    (hF : MapsTo T F F) (hFne : F.Nonempty) {P Q m : ℕ}
    (hP : 0 < P) (hQ : 0 < Q) (hm : 0 < m)
    (hcodes : ∀ τ : ℝ, 0 < τ → ∃ J : ℕ, ∀ r : ℕ,
      ∃ s : Finset X, ∃ k : ℕ, IsDynCoverOf T F U (m * r) s ∧
        s.card ≤ 2 ^ r * P ^ r * Q ^ k ∧ (k : ℝ) ≤ τ * r + J) :
    coverEntropyEntourage T F (U ○ U) ≤
      (((Real.log 2 + Real.log P) / m : ℝ) : EReal) := by
  apply ereal_le_of_sparse_block_bounds (B := Real.log Q)
  intro τ hτ
  obtain ⟨J, hJ⟩ := hcodes τ hτ
  refine ⟨(J : ℝ) * Real.log Q, ?_⟩
  intro r hr
  obtain ⟨s, k, hcover, hcard, hk⟩ := hJ r
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    simpa only [Finset.coe_nonempty] using hcover.nonempty hFne)
  have hlog : Real.log (s.card : ℝ) ≤
      Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hs)
    exact_mod_cast hcard
  have hdiv : Real.log (s.card : ℝ) / (m * r) ≤
      (Real.log 2 + Real.log P + τ * Real.log Q +
        ((J : ℝ) * Real.log Q) / r) / m :=
    (div_le_div_of_nonneg_right hlog (by positivity)).trans
      (log_sparse_word_bound hP hQ hm hr hk)
  exact (IsDynCoverOf.entropy_le_real_log_card_div hF (Nat.mul_pos hm hr) hs hcover).trans
    (by exact_mod_cast hdiv)

lemma exists_small_log_dynCover_of_zero_entropy {X : Type*} [UniformSpace X]
    {T : X → X} {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (hInv : MapsTo T K K) (hzero : coverEntropy T K = 0)
    {U : SetRel X X} (hU : U ∈ 𝓤 X) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ s : Finset X,
      IsDynCoverOf T K U m s ∧ 0 < s.card ∧
        (Real.log 2 + Real.log (s.card : ℝ)) / m < ε := by
  have hrate : ExpGrowth.expGrowthSup (fun n => (coverMincard T K U n).toENNReal) <
      ((ε / 2 : ℝ) : EReal) := by
    have hh := coverEntropyEntourage_le_coverEntropy T K hU
    rw [hzero] at hh
    exact hh.trans_lt (by exact_mod_cast (half_pos hε))
  have hbound := ExpGrowth.eventually_le_exp hrate
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log 2 / n < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).eventually_lt_const (half_pos hε)
  have hex : ∀ᶠ m : ℕ in atTop, N ≤ m ∧ 0 < m ∧ ∃ s : Finset X,
      IsDynCoverOf T K U m s ∧ 0 < s.card ∧
        (Real.log 2 + Real.log (s.card : ℝ)) / m < ε := by
    filter_upwards [hbound, hsmall, eventually_ge_atTop N, eventually_ge_atTop 1]
      with m hm hsmall hmN hm1
    obtain ⟨s, hcover, hcard⟩ := (coverMincard_finite_iff T K U m).mp
      (coverMincard_finite_of_isCompact_invariant hK hInv hU m)
    have hs : 0 < s.card := Finset.card_pos.mpr (by
      simpa only [Finset.coe_nonempty] using hcover.nonempty hKne)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    refine ⟨hmN, by omega, s, hcover, hs, ?_⟩
    rw [← hcard, ENat.toENNReal_coe] at hm
    have hlog := ENNReal.log_monotone hm
    rw [EReal.log_exp, ENNReal.log_pos_real (by exact_mod_cast Nat.ne_of_gt hs)
      (by simp)] at hlog
    have hreal : Real.log (s.card : ℝ) ≤ (ε / 2) * m := by
      simpa only [ENNReal.toReal_natCast, ← EReal.coe_natCast,
        ← EReal.coe_mul, EReal.coe_le_coe_iff] using hlog
    have hdiv : Real.log (s.card : ℝ) / m ≤ ε / 2 :=
      (div_le_iff₀ hmpos).mpr hreal
    rw [add_div]
    linarith
  exact hex.exists

theorem entropy_le_of_neighborhood_attracting_dynCover {X : Type*}
    [UniformSpace X] [CompactSpace X] [Nonempty X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (_hK : IsCompact K) (hKne : K.Nonempty)
    (hattract : ∀ V : Set X, IsOpen V → K ⊆ V →
      ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {U : SetRel X X} [U.IsSymm] (hU : U ∈ 𝓤 X) (hUopen : IsOpen U)
    {m : ℕ} (hm : 0 < m) {p : Finset X}
    (hp : IsDynCoverOf T K U m p) :
    coverEntropyEntourage T Set.univ ((U ○ U) ○ (U ○ U)) ≤
      (((Real.log 2 + Real.log p.card) / m : ℝ) : EReal) := by
  classical
  obtain ⟨V, hV, hKV, hpV⟩ :=
    EntropyCoding.exists_open_neighborhood_dynCover hT hUopen hp
  obtain ⟨q, hq⟩ := exists_isDynCoverOf_of_isCompact_invariant
    isCompact_univ (show MapsTo T Set.univ Set.univ from fun _ _ => mem_univ _) hU m
  have hpne : p.Nonempty := by
    simpa only [Finset.coe_nonempty] using hp.nonempty hKne
  have hqne : q.Nonempty := by
    simpa only [Finset.coe_nonempty] using hq.nonempty (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
  apply coverEntropyEntourage_le_of_sparse_block_covers
    (show MapsTo T Set.univ Set.univ from fun _ _ => mem_univ _)
    Set.univ_nonempty (Finset.card_pos.mpr hpne) (Finset.card_pos.mpr hqne) hm
  intro τ hτ
  obtain ⟨J, hJ⟩ := exists_sparse_sampled_visits_bound
    hT hV (hattract V hV hKV) hm hτ
  refine ⟨J, ?_⟩
  intro r
  let k := ⌊τ * (r : ℝ) + J⌋₊
  have hbound : coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * p.card ^ r * q.card ^ k : ℕ) := by
    apply EntropyCoding.coverMincard_le_of_sparse_visits_finset
      T U m r k V p q hpne hqne hpV hq
    intro x
    exact Nat.le_floor (hJ r x)
  have hfinite : coverMincard T Set.univ (U ○ U) (m * r) < ⊤ :=
    hbound.trans_lt (WithTop.coe_lt_top _)
  obtain ⟨s, hs, hscard⟩ :=
    (coverMincard_finite_iff T Set.univ (U ○ U) (m * r)).mp hfinite
  refine ⟨s, k, hs, ?_, Nat.floor_le (by positivity)⟩
  rw [← hscard] at hbound
  exact_mod_cast hbound

theorem coverEntropy_eq_zero_of_neighborhood_attraction {X : Type*}
    [UniformSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hInv : MapsTo T K K)
    (hzero : coverEntropy T K = 0)
    (hattract : ∀ V : Set X, IsOpen V → K ⊆ V →
      ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V) :
    coverEntropy T Set.univ = 0 := by
  let : Nonempty X := hKne.nonempty
  apply le_antisymm ?_ (coverEntropy_nonneg T Set.univ_nonempty)
  apply iSup₂_le
  intro U hU
  obtain ⟨V, hV, hVopen, hVsymm, hVU⟩ := comp_open_symm_mem_uniformity_sets hU
  obtain ⟨W, hW, hWopen, hWsymm, hWV⟩ := comp_open_symm_mem_uniformity_sets hV
  let : SetRel.IsSymm W := hWsymm
  have hsub : ((W ○ W) ○ (W ○ W)) ⊆ U :=
    (SetRel.comp_subset_comp hWV hWV).trans hVU
  have hsmall : ∀ ε : ℝ, 0 < ε → coverEntropyEntourage T Set.univ U ≤ (ε : EReal) := by
    intro ε hε
    obtain ⟨m, hm1, hm, p, hp, hpne, hlog⟩ :=
      exists_small_log_dynCover_of_zero_entropy hK hKne hInv hzero hW hε 1
    have hlocal := entropy_le_of_neighborhood_attracting_dynCover hT hK hKne hattract hW hWopen hm hp
    exact (coverEntropyEntourage_antitone T Set.univ hsub).trans
      (hlocal.trans (EReal.coe_le_coe hlog.le))
  have hlim : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : EReal))
      atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto' hlim fun n => hsmall _ (by positivity)

theorem entropy_le_of_attracting_dynCover {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [Nonempty X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hattract : ∀ x, Tendsto (fun n => Metric.infDist (T^[n] x) K) atTop (𝓝 0))
    {U : SetRel X X} [U.IsSymm] (hU : U ∈ 𝓤 X) (hUopen : IsOpen U)
    {m : ℕ} (hm : 0 < m) {p : Finset X}
    (hp : IsDynCoverOf T K U m p) :
    coverEntropyEntourage T Set.univ ((U ○ U) ○ (U ○ U)) ≤
      (((Real.log 2 + Real.log p.card) / m : ℝ) : EReal) := by
  apply entropy_le_of_neighborhood_attracting_dynCover hT hK hKne ?_ hU hUopen hm hp
  intro V hV hKV x
  exact eventually_mem_of_tendsto_infDist hK hKne hV hKV (hattract x)

theorem coverEntropy_eq_zero_of_pointwise_attraction {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hInv : MapsTo T K K)
    (hzero : coverEntropy T K = 0)
    (hattract : ∀ x, Tendsto (fun n => Metric.infDist (T^[n] x) K) atTop (𝓝 0)) :
    coverEntropy T Set.univ = 0 := by
  apply coverEntropy_eq_zero_of_neighborhood_attraction hT hK hKne hInv hzero
  intro V hV hKV x
  exact eventually_mem_of_tendsto_infDist hK hKne hV hKV (hattract x)

end Problem340

end

end OAI
