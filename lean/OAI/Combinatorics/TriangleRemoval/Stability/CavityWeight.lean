import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixMessageEnvelopeSmall
import OAI.Combinatorics.TriangleRemoval.Coupling.GridUniformError

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def cavityWeight (D t : ℝ) : ℝ := 1/(1+2*D*t)

lemma cavityReference_sq {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    cavityReference D t ^ 2 = cavityWeight D t := by
  have hx : 0 ≤ 1+2*D*t := by positivity
  unfold cavityReference cavityWeight
  rw [← Real.rpow_mul_natCast hx]
  norm_num [Real.rpow_neg_one]

lemma cavityWeight_pos {D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    0 < cavityWeight D t := by unfold cavityWeight; positivity

lemma cavityWeight_lower {D t : ℝ} (hD : 0 ≤ D) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    cavityWeight D 1 ≤ cavityWeight D t := by
  unfold cavityWeight
  have ht0 := ht.1
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [ht.2]

theorem goodPrefix_continuous_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < prefixD n ∧
      ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          messageIntegral (activeHypergraph G) (cavityLimit (activeHypergraph G)) e T t ≤ 1/16) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          (∏ f ∈ (activeHypergraph G T).erase e,
            cavityLimit (activeHypergraph G) f (some T) t) ≤
              (17/16 : ℝ)*cavityWeight (prefixD n) t) := by
  obtain ⟨a,ha,hrel⟩ := goodPrefix_cavity_relative hc
  filter_upwards [goodPrefix_cavity_stability hc (by norm_num : (0 : ℝ) < 1/64),
    hrel,prefix_message_envelope_small (by norm_num : (0 : ℝ) < 1/16),
    prefix_scales_eventually_pos] with n hs hr hi hp
  have hD : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hp.2
  refine ⟨hD,?_⟩
  intro C G h t ht
  refine ⟨fun e T he => ((hr.2 C G h t ht).2 e T he).1.trans hi.2,?_⟩
  intro e T he
  have hcard : ((activeHypergraph G T).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem he,activeHypergraph_card]
  have href := cavityReference_pos hD ht.1
  have hprod : (∏ f ∈ (activeHypergraph G T).erase e,
      cavityLimit (activeHypergraph G) f (some T) t) ≤
      ((65/64 : ℝ)*cavityReference (prefixD n) t)^2 := by
    calc
      _ ≤ ∏ _f ∈ (activeHypergraph G T).erase e,
          (65/64 : ℝ)*cavityReference (prefixD n) t := by
        apply Finset.prod_le_prod₀
        · intro f _; exact (cavityLimit_mem_unit _ _ _ _).1
        · intro f hf
          have hh := (abs_le.mp ((hs C G h t ht).2 f T (Finset.mem_of_mem_erase hf))).2
          apply (div_le_iff₀ href).mp
          linarith
      _ = _ := by simp [hcard]
  calc
    _ ≤ ((65/64 : ℝ)*cavityReference (prefixD n) t)^2 := hprod
    _ = (65/64 : ℝ)^2*cavityWeight (prefixD n) t := by
      rw [mul_pow,cavityReference_sq hD.le ht.1]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (cavityWeight_pos hD.le ht.1).le

theorem goodPrefix_grid_rows {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : ℝ) (G : Graph n), GoodPrefixGraph n c C G →
      ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ k ≤ N,
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          (7/8 : ℝ) ≤ gridCandidateFailure (activeHypergraph G) N k e T) ∧
        (∀ (e : G) (T : triangles G), e ∈ activeHypergraph G T →
          gridAnswerProbability (activeHypergraph G) N N k
            ((activeHypergraph G T).erase e) (some T) ≤
              (9/8 : ℝ)*cavityWeight (prefixD n) ((k : ℝ)/N)) := by
  filter_upwards [goodPrefix_continuous_rows hc] with n hn
  intro C G h
  let H := activeHypergraph G
  let A : ℝ := (Fintype.card G : ℝ)*gridUniformError H +
    (Fintype.card G : ℝ)*Fintype.card (triangles G)
  let B : ℝ := 2*gridUniformError H
  have hA : Tendsto (fun N : ℕ => A/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB : Tendsto (fun N : ℕ => B/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ N : ℕ in atTop, A/(N : ℝ) ≤ 1/16 ∧
      B/(N : ℝ) ≤ cavityWeight (prefixD n) 1/16 := by
    filter_upwards [hA.eventually_le_const (by norm_num : (0 : ℝ) < 1/16),
      hB.eventually_le_const (show 0 < cavityWeight (prefixD n) 1/16 from
        div_pos (cavityWeight_pos hn.1.le zero_le_one) (by norm_num))]
      with N ha hb
    exact ⟨ha,hb⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hsmall
  refine ⟨N₀,?_⟩
  intro N _ hN k hk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ht : (k : ℝ)/N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one hNpos).mpr (by exact_mod_cast hk)⟩
  obtain ⟨hi,hpair⟩ := hn.2 C G h _ ht
  obtain ⟨ha,hb⟩ := hN₀ N hN
  constructor
  · intro e T he
    have herr := gridCandidateFailure_error H N k hk e T
    have herr' := (abs_le.mp herr).1
    have hh := hi e T he
    change _ ≤ A/(N : ℝ) at herr
    dsimp only [A] at ha
    dsimp only [H] at herr'
    linarith
  · intro e T he
    have hcard : ((H T).erase e).card = 2 := by
      rw [Finset.card_erase_of_mem he,activeHypergraph_card]
    have herr := gridAnswer_uniform_error H N k hk ((H T).erase e) (some T)
    rw [hcard] at herr
    have herr' := (abs_le.mp herr).2
    have hp := hpair e T he
    have hbl := cavityWeight_lower hn.1.le ht
    dsimp only [B,H] at hb herr'
    norm_num only [Nat.cast_ofNat] at herr'
    linarith

end SharpTerminalLeave

end

end OAI
