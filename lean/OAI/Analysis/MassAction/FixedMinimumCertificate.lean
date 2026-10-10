import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.FixedMinimumEstimates

namespace OAI

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Problem326.Affine

/-- The unshifted constant-slope label used at a fixed minimum level. -/
def constantLabel (d : ℕ) (t : ℝ) : Label d :=
  ⟨fun _ => t, fun _ => 0⟩

/-- Finite construction data for one label. The `inner_bound` field is exactly
what the lower-dimensional induction supplies after restricting activity to the
lifted family. All remaining fields concern finite choices or offset asymptotics. -/
structure FixedMinimumLabelCertificate {d : ℕ} (Λ : Finset (Label d))
    (a b t : ℝ) (E : (Fin d → ℝ) → ℝ) (L : Label d) where
  support : Finset (Fin d)
  threshold : ℝ
  threshold_gt : t < threshold
  error_pos : 0 < E L.slope
  slope_in : ∀ i ∈ support, threshold ≤ L.slope i
  slope_out : ∀ i ∉ support, L.slope i = t
  offset_behavior :
    (support = ∅ ∧ ∀ h, L.offset h = 0) ∨
    Tendsto (fun h => L.offset h / h ^ threshold) (𝓝[>] 0) (𝓝 (-1))
  inner_bound : ∀ (h : ℕ → ℝ) (p : ℕ → (Fin d → ℝ)) (p₀ : Fin d → ℝ),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    Tendsto p atTop (𝓝 p₀) → Cube a b p₀ →
    (∀ n, Active Λ L (h n) (powerPoint (h n) (p n))) →
    (∀ i ∈ support, threshold ≤ p₀ i) →
    ∀ i ∈ support, |p₀ i - L.slope i| < E L.slope
  successor :
    (∀ i ∉ support, ∀ j ∉ support, i = j) ∨
    ∃ γ : ℝ, γ < threshold ∧ γ - t < E L.slope ∧
      ∀ j, j ∉ support → ∃ J ∈ Λ,
        Tendsto (fun h => J.offset h / h ^ γ) (𝓝[>] 0) (𝓝 (-1)) ∧
        (∀ i, i ∉ support → i ≠ j → J.slope i = t)

lemma relativeValue_eq_value_sub {d : ℕ} (L : Label d) (t h : ℝ)
    (p : Fin d → ℝ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) =
      L.value h (powerPoint h p) - ∑ i, t * h ^ p i := by
  simp only [FixedMinimum.relativeValue, Label.value, powerPoint,
    sub_mul, Finset.sum_sub_distrib]
  ring

lemma active_relativeValue_le {d : ℕ} {Λ : Finset (Label d)}
    {L J : Label d} {h t : ℝ} {p : Fin d → ℝ}
    (hactive : Active Λ L h (powerPoint h p)) (hJ : J ∈ Λ) :
    FixedMinimum.relativeValue t L.slope p h (L.offset h) ≤
      FixedMinimum.relativeValue t J.slope p h (J.offset h) := by
  rw [relativeValue_eq_value_sub, relativeValue_eq_value_sub]
  exact sub_le_sub_right (hactive.2 J hJ) _

theorem approximatesAtMinimum_of_certificates {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hbaseline : constantLabel d t ∈ Λ)
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    ApproximatesAtMinimum Λ a b t E := by
  intro L hL h p p₀ hh hh0 hp hcube hm ha
  let C := hcert L hL
  have hhGT : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh0, Filter.Eventually.of_forall hh⟩
  have hpcoord : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (p₀ i)) :=
    tendsto_pi_nhds.mp hp
  have hbase : ∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n)
      (L.offset (h n)) ≤ 0 := by
    intro n
    have hv := active_relativeValue_le (t := t) (ha n) hbaseline
    simpa only [constantLabel, FixedMinimum.relativeValue, sub_self,
      zero_mul, Finset.sum_const_zero, add_zero] using hv
  have hoffset : (C.support = ∅ ∧ ∀ n, L.offset (h n) = 0) ∨
      Tendsto (fun n => L.offset (h n) / h n ^ C.threshold) atTop (𝓝 (-1)) := by
    rcases C.offset_behavior with ⟨hU, hc⟩ | hc
    · exact Or.inl ⟨hU, fun n => hc (h n)⟩
    · exact Or.inr (hc.comp hhGT)
  have hnext : (∀ i ∉ C.support, ∀ j ∉ C.support, i = j) ∨
      ∃ γ : ℝ, γ < C.threshold ∧ γ - t < E L.slope ∧
        ∀ j, j ∉ C.support → ∃ s : Fin d → ℝ, ∃ c : ℕ → ℝ,
          Tendsto (fun n => c n / h n ^ γ) atTop (𝓝 (-1)) ∧
          (∀ i, i ∉ C.support → i ≠ j → s i = t) ∧
          (∀ n, FixedMinimum.relativeValue t L.slope (p n) (h n) (L.offset (h n)) ≤
            FixedMinimum.relativeValue t s (p n) (h n) (c n)) := by
    rcases C.successor with hlast | ⟨γ, hγ, hE, hcomp⟩
    · exact Or.inl hlast
    · refine Or.inr ⟨γ, hγ, hE, ?_⟩
      intro j hj
      obtain ⟨J, hJ, hc, hs⟩ := hcomp j hj
      exact ⟨J.slope, fun n => J.offset (h n), hc.comp hhGT, hs,
        fun n => active_relativeValue_le (ha n) hJ⟩
  have hcoord := FixedMinimum.fixed_minimum_label_bound hh hh0 hpcoord
    hm.1 hm.2 C.threshold_gt C.error_pos C.slope_in C.slope_out hoffset hbase
    (C.inner_bound h p p₀ hh hh0 hp hcube ha) hnext
  rw [pi_norm_lt_iff C.error_pos]
  intro i
  exact hcoord i

theorem normalized_shifted_offset {c : ℝ → ℝ} {β : ℝ}
    (hc : c =o[𝓝[>] 0] (fun h : ℝ => h ^ β)) :
    Tendsto (fun h : ℝ => (-h ^ β + c h) / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hlim : Tendsto (fun h : ℝ => -1 + c h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hc.tendsto_div_nhds_zero :
        Tendsto (fun h : ℝ => -1 + c h / h ^ β) (𝓝[>] 0) (𝓝 (-1 + 0)))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hne : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
  simp only [add_div, neg_div, div_self hne]

/-- A normalized type offset decays faster than every smaller power. -/
theorem offset_isLittleO_of_normalized {c : ℝ → ℝ} {s β : ℝ}
    (hc : Tendsto (fun h : ℝ => c h / h ^ β) (𝓝[>] 0) (𝓝 (-1)))
    (hsβ : s < β) : c =o[𝓝[>] 0] (fun h : ℝ => h ^ s) := by
  have hi : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hpow := hi.rpow_const_nhds_zero (sub_pos.mpr hsβ)
  have hratio : Tendsto (fun h : ℝ => h ^ β / h ^ s) (𝓝[>] 0) (𝓝 0) := by
    apply hpow.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh β s
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with h hh hz
    exact False.elim ((ne_of_gt (Real.rpow_pos_of_pos hh s)) hz)
  · have hlim : Tendsto (fun h : ℝ => (c h / h ^ β) * (h ^ β / h ^ s))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hc.mul hratio
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hh β)]

/-- Finitely many type certificates have one common exponent strictly above
the fixed minimum at which all their offsets are little-o. This decay allows
localization and inter-family gluing. -/
theorem exists_common_offset_decay {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    ∃ s : ℝ, t < s ∧ ∀ L ∈ Λ, L.offset =o[𝓝[>] 0] (fun h : ℝ => h ^ s) := by
  classical
  let β : {L // L ∈ Λ} → ℝ := fun L => (hcert L.1 L.2).threshold
  obtain ⟨s, hts, _, hs⟩ := exists_threshold Finset.univ (fun L => β L - t)
    (fun L _ => sub_pos.mpr (hcert L.1 L.2).threshold_gt)
    (show t < t + 1 by linarith)
  refine ⟨s, hts, ?_⟩
  intro L hL
  have hsβ : s < (hcert L hL).threshold := by
    have h := hs ⟨L, hL⟩ (Finset.mem_univ _)
    dsimp [β] at h
    linarith
  rcases (hcert L hL).offset_behavior with ⟨_, hc⟩ | hc
  · have hc0 : L.offset = fun _ => 0 := funext hc
    rw [hc0]
    exact Asymptotics.isLittleO_zero _ _
  · exact offset_isLittleO_of_normalized hc hsβ

end Problem326.Affine

end

end OAI
