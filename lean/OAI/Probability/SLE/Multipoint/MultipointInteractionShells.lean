import OAI.Probability.SLE.Multipoint.MultipointInteraction
import OAI.Probability.SLE.Multipoint.MultipointRegularizer

namespace OAI

/-! The Green drop bounds the mass of every clock shell.  The first point
of the closed clock tail gives the bound even when a clock is constant on
an interval.  Disjoint measurable shells then give the manuscript's
weighted interaction budget. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal Function

namespace SLEExactGauge.Multipoint

def clockTail (s T : ℝ) (q : ℝ → ℝ) (k : ℕ) : Set ℝ :=
  Icc s T ∩ q ⁻¹' Ici (k : ℝ)

def clockShell (s T : ℝ) (q : ℝ → ℝ) (k : ℕ) : Set ℝ :=
  clockTail s T q k \ clockTail s T q (k + 1)

lemma clockTail_isClosed {s T : ℝ} {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc s T)) (k : ℕ) : IsClosed (clockTail s T q k) :=
  hq.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici

lemma clockTail_isCompact {s T : ℝ} {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc s T)) (k : ℕ) : IsCompact (clockTail s T q k) :=
  isCompact_Icc.of_isClosed_subset (clockTail_isClosed hq k) inter_subset_left

lemma clockShell_measurableSet {s T : ℝ} {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc s T)) (k : ℕ) : MeasurableSet (clockShell s T q k) :=
  (clockTail_isClosed hq k).measurableSet.diff
    (clockTail_isClosed hq (k + 1)).measurableSet

lemma mem_clockShell {s T : ℝ} {q : ℝ → ℝ} {k : ℕ} {t : ℝ} :
    t ∈ clockShell s T q k ↔ t ∈ Icc s T ∧ (k : ℝ) ≤ q t ∧ q t < k + 1 := by
  simp only [clockShell, clockTail, Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_Ici,
    Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨⟨hI, hlo⟩, hn⟩
    exact ⟨hI, hlo, lt_of_not_ge (fun hh => hn ⟨hI, hh⟩)⟩
  · rintro ⟨hI, hlo, hhi⟩
    exact ⟨⟨hI, hlo⟩, fun hh => (not_le_of_gt hhi) hh.2⟩

lemma clockShell_pairwise (s T : ℝ) (q : ℝ → ℝ) :
    Pairwise (Disjoint on clockShell s T q) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  have hi' := mem_clockShell.mp hi
  have hj' := mem_clockShell.mp hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

lemma iUnion_clockShell {s T : ℝ} {q : ℝ → ℝ}
    (h0 : ∀ t ∈ Icc s T, 0 ≤ q t) :
    (⋃ k : ℕ, clockShell s T q k) = Icc s T := by
  ext t
  constructor
  · intro ht
    obtain ⟨k, hk⟩ := mem_iUnion.mp ht
    exact (mem_clockShell.mp hk).1
  · intro ht
    refine mem_iUnion.mpr ⟨⌊q t⌋₊, mem_clockShell.mpr ⟨ht, Nat.floor_le (h0 t ht), ?_⟩⟩
    exact Nat.lt_floor_add_one (q t)

/-- A future Green-drop bound and the exponential interaction decay give
the exact mass bound for a single shell of the increasing clock. -/
theorem interaction_shell_mass_bound
    {s T a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (q R L : ℝ → ℝ)
    (hq : ContinuousOn q (Icc s T)) (hR : ContinuousOn R (Icc s T))
    (hR0 : ∀ t ∈ Icc s T, 0 ≤ R t)
    (hdrop : ∀ t ∈ Icc s T, (∫ v in t..T, R v) ≤ L t / (2 * a))
    (hdecay : ∀ t ∈ Icc s T, L t ≤ M * Real.exp (-a * q t)) (k : ℕ) :
    (∫ t in clockShell s T q k, R t) ≤ M * Real.exp (-a * k) / (2 * a) := by
  classical
  by_cases hne : (clockTail s T q k).Nonempty
  · obtain ⟨τ, hτ⟩ := (clockTail_isCompact hq k).exists_isLeast hne
    have hτI : τ ∈ Icc s T := hτ.1.1
    have hτq : (k : ℝ) ≤ q τ := hτ.1.2
    have hsub : clockShell s T q k ⊆ Icc τ T := by
      intro t ht
      exact ⟨hτ.2 ht.1, ht.1.1.2⟩
    have hI : Icc τ T ⊆ Icc s T := Icc_subset_Icc hτI.1 le_rfl
    have hnonneg : 0 ≤ᵐ[volume.restrict (Icc τ T)] R := by
      change ∀ᵐ t ∂volume.restrict (Icc τ T), 0 ≤ R t
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall (fun t ht => hR0 t (hI ht))
    calc
      _ ≤ ∫ t in Icc τ T, R t :=
        setIntegral_mono_set (hR.mono hI).integrableOn_Icc hnonneg
          (Eventually.of_forall hsub)
      _ = ∫ t in τ..T, R t := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hτI.2]
      _ ≤ L τ / (2 * a) := hdrop τ hτI
      _ ≤ M * Real.exp (-a * k) / (2 * a) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (hdecay τ hτI).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hM)
  · have hs : clockShell s T q k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hne ⟨t, ht.1⟩
    rw [hs]
    simp only [Measure.restrict_empty, integral_zero_measure]
    positivity

lemma weighted_shell_sum_le_prefactor {a c M : ℝ}
    (ha : 0 < a) (hc : 2 * c < a) (_hM : 0 ≤ M)
    (mass : ℕ → ℝ) (h0 : ∀ k, 0 ≤ mass k)
    (hmass : ∀ k : ℕ, mass k ≤ M * Real.exp (-a * k) / (2 * a)) :
    Summable (fun k : ℕ => Real.exp (2 * c * ((k : ℝ) + 1)) * mass k) ∧
      (∑' k : ℕ, Real.exp (2 * c * ((k : ℝ) + 1)) * mass k) ≤
        M * interactionBudget a c := by
  have hs := (interaction_shell_series ha hc).mul_left M
  have hnonneg (k : ℕ) : 0 ≤ Real.exp (2 * c * ((k : ℝ) + 1)) * mass k :=
    mul_nonneg (Real.exp_pos _).le (h0 k)
  have hle (k : ℕ) : Real.exp (2 * c * ((k : ℝ) + 1)) * mass k ≤
      M * (Real.exp (2 * c * ((k : ℝ) + 1)) * Real.exp (-a * k) / (2 * a)) := by
    calc
      _ ≤ Real.exp (2 * c * ((k : ℝ) + 1)) *
          (M * Real.exp (-a * k) / (2 * a)) :=
        mul_le_mul_of_nonneg_left (hmass k) (Real.exp_pos _).le
      _ = _ := by ring
  have hsum := Summable.of_nonneg_of_le hnonneg hle hs.summable
  exact ⟨hsum, hs.tsum_eq ▸ hsum.tsum_le_tsum hle hs.summable⟩

/-- The full weighted interaction bound, derived from the Green drop;
no shell-mass estimate is assumed. -/
theorem weighted_interaction_integral_le
    {s T a c M : ℝ} (hsT : s ≤ T) (ha : 0 < a) (hM : 0 ≤ M)
    (hc : 0 ≤ c) (hca : 2 * c < a)
    (u v R L : ℝ → ℝ)
    (hu : ContinuousOn u (Icc s T)) (hv : ContinuousOn v (Icc s T))
    (hu0 : ∀ t ∈ Icc s T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc s T, 0 ≤ v t)
    (hR : ContinuousOn R (Icc s T)) (hR0 : ∀ t ∈ Icc s T, 0 ≤ R t)
    (hdrop : ∀ t ∈ Icc s T, (∫ x in t..T, R x) ≤ L t / (2 * a))
    (hdecay : ∀ t ∈ Icc s T, L t ≤ M * Real.exp (-a * max (u t) (v t))) :
    (∫ t in s..T, Real.exp (c * (u t + v t)) * R t) ≤ M * interactionBudget a c := by
  let q := fun t => max (u t) (v t)
  let F := fun t => Real.exp (c * (u t + v t)) * R t
  let mass := fun k => ∫ t in clockShell s T q k, R t
  have hq : ContinuousOn q (Icc s T) := hu.sup hv
  have hcov : (⋃ k : ℕ, clockShell s T q k) = Icc s T :=
    iUnion_clockShell (fun t ht => (le_min (hu0 t ht) (hv0 t ht)).trans min_le_max)
  have hFm : ContinuousOn F (Icc s T) :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hu.add hv))).mul hR
  have hmass0 (k : ℕ) : 0 ≤ mass k := by
    apply setIntegral_nonneg (clockShell_measurableSet hq k)
    intro t ht
    exact hR0 t (mem_clockShell.mp ht).1
  have hmass (k : ℕ) : mass k ≤ M * Real.exp (-a * k) / (2 * a) :=
    interaction_shell_mass_bound ha hM q R L hq hR hR0 hdrop hdecay k
  obtain ⟨hsum, hsumle⟩ := weighted_shell_sum_le_prefactor ha hca hM mass hmass0 hmass
  have hFint : IntegrableOn F (⋃ k : ℕ, clockShell s T q k) := by
    rw [hcov]
    exact hFm.integrableOn_Icc
  have hpieces := hasSum_integral_iUnion (clockShell_measurableSet hq)
    (clockShell_pairwise s T q) hFint
  have hpiece (k : ℕ) : (∫ t in clockShell s T q k, F t) ≤
      Real.exp (2 * c * ((k : ℝ) + 1)) * mass k := by
    have hsub : clockShell s T q k ⊆ Icc s T := fun t ht => (mem_clockShell.mp ht).1
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hFm.integrableOn_Icc.mono_set hsub)
      ((hR.integrableOn_Icc.mono_set hsub).const_mul _)
      (clockShell_measurableSet hq k)
    intro t ht
    have hkt := mem_clockShell.mp ht
    apply mul_le_mul_of_nonneg_right _ (hR0 t hkt.1)
    apply Real.exp_le_exp.mpr
    have hsumq : u t + v t ≤ 2 * q t := by
      have h₁ := le_max_left (u t) (v t)
      have h₂ := le_max_right (u t) (v t)
      dsimp only [q]
      linarith
    have hbound : u t + v t ≤ 2 * ((k : ℝ) + 1) := by linarith [hkt.2.2]
    nlinarith
  calc
    _ = ∫ t in Icc s T, F t := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hsT]
    _ = ∑' k : ℕ, ∫ t in clockShell s T q k, F t := by
      rw [← hcov]
      exact hpieces.tsum_eq.symm
    _ ≤ ∑' k : ℕ, Real.exp (2 * c * ((k : ℝ) + 1)) * mass k :=
      hpieces.summable.tsum_le_tsum hpiece hsum
    _ ≤ M * interactionBudget a c := hsumle

end SLEExactGauge.Multipoint

namespace SLEExactGauge

/-- The weighted-shell estimate for the actual capacity-two Loewner maps.
The pair drop is supplied by the proved Green-kernel identity.  Its sole
remaining geometric premise is the interaction decay during joint activity. -/
theorem IsCapacityTwoWitness.weighted_interaction_integral_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T) (hne : z ≠ w)
    {c M : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hca : 2 * c < 2) (u v : ℝ → ℝ)
    (hu : ContinuousOn u (Icc (s : ℝ) (T : ℝ)))
    (hv : ContinuousOn v (Icc (s : ℝ) (T : ℝ)))
    (hu0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ u t)
    (hv0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ v t)
    (hdecay : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      halfPlaneGreen (G t.toNNReal z) (G t.toNNReal w) ≤
        M * Real.exp (-2 * max (u t) (v t))) :
    (∫ t in (s : ℝ)..(T : ℝ), Real.exp (c * (u t + v t)) *
      (chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w)) ≤
        M * Multipoint.interactionBudget 2 c := by
  let R := fun t : ℝ => chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w
  let L := fun t : ℝ => halfPlaneGreen (G t.toNNReal z) (G t.toNNReal w)
  have hI : Icc (s : ℝ) (T : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  have hR : ContinuousOn R (Icc (s : ℝ) (T : ℝ)) :=
    ((hw.poissonRate_continuousOn hU T z hz).mul
      (hw.poissonRate_continuousOn hU T w hw')).mono hI
  have hR0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ R t := by
    intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    exact mul_nonneg
      (hw.poissonRate_nonneg _ z (survivingDomain_antitone γ htT hz))
      (hw.poissonRate_nonneg _ w (survivingDomain_antitone γ htT hw'))
  have hdrop : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      (∫ x in t..(T : ℝ), R x) ≤ L t / (2 * 2) := by
    intro t ht
    have ht0 : 0 ≤ t := s.coe_nonneg.trans ht.1
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hb := hw.green_pair_bound hU t.toNNReal T htT z w hz hw' hne
    simpa only [R, L, Real.coe_toNNReal _ ht0, show (2 : ℝ) * 2 = 4 by norm_num] using hb
  exact Multipoint.weighted_interaction_integral_le hsT (by norm_num) hM hc hca
    u v R L hu hv hu0 hv0 hR hR0 hdrop hdecay

end SLEExactGauge

end

end OAI
