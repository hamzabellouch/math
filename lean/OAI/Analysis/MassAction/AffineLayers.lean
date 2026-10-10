import OAI.Analysis.MassAction.LayerSequence
import OAI.Analysis.MassAction.FixedMinimumEstimates

namespace OAI

open Filter Topology

noncomputable section
namespace Problem326.Affine

/-- The lower-dimensional induction hypothesis, transported to one support. -/
def ApproximatesOnSupport {d : ℕ} (F : Finset (Label d)) (L : Label d)
    (U : Finset (Fin d)) (t b β : ℝ) (E : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube t b p₀ →
    (∀ i ∈ U, β ≤ p₀ i) →
    (∀ n, Active F L (h n) (powerPoint (h n) (p n))) →
    ∀ i ∈ U, |p₀ i - L.slope i| < E L.slope

/-- Exactly the information needed from one recursively constructed type family.
The zero type is the constant baseline; positive types have normalized offset -1.
No continuity of offsets or tolerances is assumed. -/
structure LayerCertificate {d : ℕ} (t b : ℝ) (E : (Fin d → ℝ) → ℝ)
    (k : ℕ) (β : ℝ) (F : Finset (Label d)) : Prop where
  tolerance_pos : ∀ L ∈ F, 0 < E L.slope
  support_data : ∀ L ∈ F, ∃ U : Finset (Fin d),
    U.card = k ∧
    (∀ i ∈ U, β ≤ L.slope i ∧ L.slope i ≤ b) ∧
    (∀ i ∉ U, L.slope i = t) ∧
    (k = 0 → ∀ h, L.offset h = 0) ∧
    (0 < k → Tendsto (fun h : ℝ => L.offset h / h ^ β)
      (𝓝[>] (0 : ℝ)) (𝓝 (-1))) ∧
    ApproximatesOnSupport F L U t b β E
  supported_competitor : ∀ U : Finset (Fin d), U.card = k →
    ∃ L ∈ F, ∀ i ∉ U, L.slope i = t

def baselineLabel (d : ℕ) (t : ℝ) : Label d := ⟨fun _ => t, fun _ => 0⟩

lemma baseline_layer_certificate {d : ℕ} {t b β : ℝ}
    (E : (Fin d → ℝ) → ℝ) (hE : 0 < E (fun _ => t)) :
    LayerCertificate t b E 0 β {baselineLabel d t} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    have hL' : L = baselineLabel d t := by simpa using hL
    subst L
    exact hE
  · intro L hL
    have hL' : L = baselineLabel d t := by simpa using hL
    subst L
    refine ⟨∅, rfl, by simp, ?_, ?_, ?_, ?_⟩
    · simp [baselineLabel]
    · simp [baselineLabel]
    · simp
    · intro h p p₀ hh hh0 hp hp₀ hU ha i hi
      simp at hi
  · intro U hU
    have hU' : U = ∅ := Finset.card_eq_zero.mp hU
    refine ⟨baselineLabel d t, by simp, ?_⟩
    simp [baselineLabel]

lemma relativeValue_le_iff {d : ℕ} (t : ℝ) (L J : Label d)
    (h : ℝ) (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) ≤
      FixedMinimum.relativeValue t J.slope p h (J.offset h) ↔
    L.value h (powerPoint h p) ≤ J.value h (powerPoint h p) := by
  unfold FixedMinimum.relativeValue Label.value powerPoint
  simp only [sub_mul, Finset.sum_sub_distrib]
  constructor <;> intro hle <;> linarith

lemma relativeValue_baseline {d : ℕ} (t h : ℝ) (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t (baselineLabel d t).slope p h
      ((baselineLabel d t).offset h) = 0 := by
  simp [FixedMinimum.relativeValue, baselineLabel]

/-- The union of all types, numbered from zero through `d - 1`. -/
def layerUnion (d : ℕ) (F : ℕ → Finset (Label d)) : Finset (Label d) := by
  classical
  exact (Finset.range d).biUnion F

lemma subset_layerUnion {d k : ℕ} (F : ℕ → Finset (Label d)) (hk : k < d) :
    F k ⊆ layerUnion d F := by
  classical
  intro L hL
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hL⟩

theorem layerUnion_approximatesAtMinimum {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (E : (Fin d → ℝ) → ℝ)
    (β : ℕ → ℝ) (F : ℕ → Finset (Label d))
    (hF₀ : F 0 = {baselineLabel d t})
    (hβ : ∀ k < d, t < β k)
    (hcert : ∀ k < d, LayerCertificate t b E k (β k) (F k))
    (hstep : ∀ k, k + 1 < d → β (k + 1) < β k ∧
      ∀ L ∈ F k, β (k + 1) - t < E L.slope) :
    ApproximatesAtMinimum (layerUnion d F) a b t E := by
  classical
  intro L hLall h p p₀ hh hh0 hp hp₀ hm ha
  obtain ⟨k, hk, hL⟩ := Finset.mem_biUnion.mp hLall
  have hkd : k < d := Finset.mem_range.mp hk
  have hc := hcert k hkd
  obtain ⟨U, hUcard, hUin, hUout, hzero, hoffset, hind⟩ := hc.support_data L hL
  have hε : 0 < E L.slope := hc.tolerance_pos L hL
  have hhwithin : Tendsto h atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh0, Filter.Eventually.of_forall hh⟩
  have hbaseMem : baselineLabel d t ∈ layerUnion d F := by
    apply subset_layerUnion F hd
    rw [hF₀]
    simp
  have hbase : ∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤ 0 := by
    intro n
    have hv := (ha n).2 (baselineLabel d t) hbaseMem
    have hr := (relativeValue_le_iff t L (baselineLabel d t) (h n) (p n)).mpr hv
    simpa only [relativeValue_baseline] using hr
  have hOff : (U = ∅ ∧ ∀ n, L.offset (h n) = 0) ∨
      Tendsto (fun n => L.offset (h n) / h n ^ β k) atTop (𝓝 (-1)) := by
    by_cases hk0 : k = 0
    · exact Or.inl ⟨Finset.card_eq_zero.mp (hUcard.trans hk0), fun n => hzero hk0 (h n)⟩
    · exact Or.inr ((hoffset (Nat.pos_of_ne_zero hk0)).comp hhwithin)
  have hInd : (∀ i ∈ U, β k ≤ p₀ i) →
      ∀ i ∈ U, |p₀ i - L.slope i| < E L.slope := by
    intro hraised
    apply hind h p p₀ hh hh0 hp (fun i => ⟨hm.1 i, (hp₀ i).2⟩) hraised
    intro n
    exact active_mono (subset_layerUnion F hkd) hL (ha n)
  have hNext : (∀ i ∉ U, ∀ j ∉ U, i = j) ∨
      ∃ γ : ℝ, γ < β k ∧ γ - t < E L.slope ∧
        ∀ j, j ∉ U → ∃ s : Fin d → ℝ, ∃ c : ℕ → ℝ,
          Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ U → i ≠ j → s i = t) ∧
          (∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤
            FixedMinimum.relativeValue t s (p n) (h n) (c n)) := by
    by_cases hkNext : k + 1 < d
    · right
      refine ⟨β (k + 1), (hstep k hkNext).1, (hstep k hkNext).2 L hL, ?_⟩
      intro j hj
      have hC := hcert (k + 1) hkNext
      obtain ⟨J, hJ, hJout⟩ := hC.supported_competitor (insert j U) (by simp [hj, hUcard])
      obtain ⟨V, hVcard, hVin, hVout, hVzero, hVoffset, hVind⟩ := hC.support_data J hJ
      refine ⟨J.slope, fun n => J.offset (h n), (hVoffset (by omega)).comp hhwithin, ?_, ?_⟩
      · intro i hi hij
        apply hJout i
        simp [hi, hij]
      · intro n
        apply (relativeValue_le_iff t L J (h n) (p n)).mpr
        exact (ha n).2 J (subset_layerUnion F hkNext hJ)
    · left
      have hcard : (Finset.univ \ U).card ≤ 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U)]
        simp only [Finset.card_univ, Fintype.card_fin, hUcard]
        omega
      intro i hi j hj
      exact (Finset.card_le_one.mp hcard) i (by simp [hi]) j (by simp [hj])
  have hbound := FixedMinimum.fixed_minimum_label_bound hh hh0
    (fun i => (tendsto_pi_nhds.mp hp) i) hm.1 hm.2 (hβ k hkd) hε
    (fun i hi => (hUin i hi).1) hUout hOff hbase hInd hNext
  apply (pi_norm_lt_iff hε).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hbound i

/-- A normalized leading power is negligible relative to each strictly lower
power. This yields the stronger local offset decay, not merely decay at `t`. -/
lemma offset_isLittleO_of_normalized_limit {c : ℝ → ℝ} {β q A : ℝ}
    (hqβ : q < β)
    (hc : Tendsto (fun h : ℝ => c h / h ^ β) (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) c (fun h : ℝ => h ^ q) := by
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id
  have hpow : Tendsto (fun h : ℝ => h ^ β / h ^ q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlim := hid.rpow_const_nhds_zero (sub_pos.mpr hqβ)
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh β q
  have hlim := hc.mul hpow
  simp only [mul_zero] at hlim
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
  · apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hne : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
    field_simp [hne]
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun hzero => (ne_of_gt (Real.rpow_pos_of_pos hh q) hzero).elim

/-- The actual finite dependent construction at one fixed minimum, separated
from the lower-dimensional embedding used to produce each positive-type layer.
The returned decay has a strictly higher exponent than `t`, allowing localization. -/
theorem exists_fixed_minimum_family_of_layers {d : ℕ} (hd : 0 < d)
    {a t b : ℝ} (htb : t < b) (E : (Fin d → ℝ) → ℝ)
    (hE₀ : 0 < E (fun _ => t))
    (hmake : ∀ k : ℕ, 0 < k → k < d → ∀ β : ℝ, t < β → β < b →
      ∃ F : Finset (Label d), LayerCertificate t b E k β F) :
    ∃ Λ : Finset (Label d), baselineLabel d t ∈ Λ ∧
      ApproximatesAtMinimum Λ a b t E ∧
      ∀ L ∈ Λ, Cube t b L.slope ∧ HasMinimum L.slope t ∧
        ∃ q : ℝ, t < q ∧
          Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) L.offset (fun h : ℝ => h ^ q) := by
  classical
  obtain ⟨β, F, hβ₀, hF₀, hvalid, hnext⟩ :=
    exists_layer_sequence (d - 1) htb (fun L : Label d => E L.slope)
      {baselineLabel d t}
      (by intro L hL; have hL' : L = baselineLabel d t := by simpa using hL
          subst L; exact hE₀)
      (fun k β F => LayerCertificate t b E k β F)
      (by
        intro k hk hkd β htβ hβb
        obtain ⟨F, hF⟩ := hmake k hk (by omega) β htβ hβb
        exact ⟨F, hF, hF.tolerance_pos⟩)
  have hcert : ∀ k < d, LayerCertificate t b E k (β k) (F k) := by
    intro k hkd
    by_cases hk0 : k = 0
    · subst k
      rw [hF₀]
      exact baseline_layer_certificate E hE₀
    · have hkpred : k - 1 < d - 1 := by omega
      have hgood := (hnext (k - 1) hkpred).2.2
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] using hgood
  have hstep : ∀ k, k + 1 < d → β (k + 1) < β k ∧
      ∀ L ∈ F k, β (k + 1) - t < E L.slope := by
    intro k hk
    exact ⟨(hnext k (by omega)).1, (hnext k (by omega)).2.1⟩
  refine ⟨layerUnion d F, ?_, ?_, ?_⟩
  · apply subset_layerUnion F hd
    rw [hF₀]
    simp
  · exact layerUnion_approximatesAtMinimum hd E β F hF₀
      (fun k _ => (hvalid k).1) hcert hstep
  · intro L hLall
    obtain ⟨k, hk, hL⟩ := Finset.mem_biUnion.mp hLall
    have hkd : k < d := Finset.mem_range.mp hk
    obtain ⟨U, hUcard, hUin, hUout, hzero, hoffset, hind⟩ :=
      (hcert k hkd).support_data L hL
    have hlow : ∀ i, t ≤ L.slope i := by
      intro i
      by_cases hi : i ∈ U
      · exact (hvalid k).1.le.trans (hUin i hi).1
      · rw [hUout i hi]
    have hcube : Cube t b L.slope := by
      intro i
      refine ⟨hlow i, ?_⟩
      by_cases hi : i ∈ U
      · exact (hUin i hi).2
      · rw [hUout i hi]
        exact htb.le
    have hnotall : ¬ ∀ i, i ∈ U := by
      intro hall
      have hUuniv : U = Finset.univ := Finset.eq_univ_of_forall hall
      rw [hUuniv, Finset.card_univ, Fintype.card_fin] at hUcard
      omega
    obtain ⟨i, hi⟩ := not_forall.mp hnotall
    refine ⟨hcube, ⟨hlow, i, hUout i hi⟩, ?_⟩
    let q := (t + β k) / 2
    have htq : t < q := by dsimp [q]; linarith [(hvalid k).1]
    have hqβ : q < β k := by dsimp [q]; linarith [(hvalid k).1]
    refine ⟨q, htq, ?_⟩
    by_cases hk0 : k = 0
    · have hz : L.offset = fun _ => 0 := funext (hzero hk0)
      rw [hz]
      exact Asymptotics.isLittleO_zero _ _
    · exact offset_isLittleO_of_normalized_limit hqβ (hoffset (Nat.pos_of_ne_zero hk0))

end Problem326.Affine

end

end OAI
