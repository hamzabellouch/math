import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Probability.LogTail

namespace OAI

open scoped BigOperators
open Filter Topology

namespace Balanced.Local

noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_event_union_le {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s : Finset ι) (E : ι → Ω → Prop)
    [∀ i, DecidablePred (E i)] :
    (∑ ω, if ∃ i ∈ s, E i ω then w ω else 0) ≤
      ∑ i ∈ s, ∑ ω, if E i ω then w ω else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hEi⟩ := h
    rw [ite_eq_left ⟨i, hi, hEi⟩]
    have hterm := Finset.single_le_sum
      (s := s) (f := fun i => if E i ω then w ω else 0)
      (fun i _ => by split_ifs; exact hw ω; exact le_rfl) hi
    simpa only [ite_eq_left hEi] using hterm
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hw ω; exact le_rfl)

lemma sum_event_mono_of_pos {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (E G : Ω → Prop)
    [DecidablePred E] [DecidablePred G]
    (hEG : ∀ ω, 0 < w ω → E ω → G ω) :
    (∑ ω, if E ω then w ω else 0) ≤ ∑ ω, if G ω then w ω else 0 := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · by_cases hp : 0 < w ω
    · simp only [ite_eq_left hE, ite_eq_left (hEG ω hp hE), le_refl]
    · have hz : w ω = 0 := le_antisymm (le_of_not_gt hp) (hw ω)
      simp [hz]
  · simp only [ite_eq_right hE]
    split_ifs; exact hw ω; exact le_rfl

lemma sum_event_at_least_le {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (s : Finset ι)
    (E : ι → Ω → Prop) [∀ i, DecidablePred (E i)] (m : ℕ) (δ : ℝ)
    (hcyl : ∀ t ∈ s.powersetCard m,
      (∑ ω, if ∀ i ∈ t, E i ω then w ω else 0) ≤ δ ^ m) :
    (∑ ω, if m ≤ (s.filter (fun i => E i ω)).card then w ω else 0) ≤
      (s.card.choose m : ℝ) * δ ^ m := by
  have hsub : ∀ ω : Ω, 0 < w ω →
      m ≤ (s.filter (fun i => E i ω)).card →
      ∃ t ∈ s.powersetCard m, ∀ i ∈ t, E i ω := by
    intro ω _ hω
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hω
    refine ⟨t, Finset.mem_powersetCard.mpr ⟨ht.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (ht hi)).2
  calc
    (∑ ω, if m ≤ (s.filter (fun i => E i ω)).card then w ω else 0)
        ≤ ∑ ω, if ∃ t ∈ s.powersetCard m, ∀ i ∈ t, E i ω then w ω else 0 :=
      sum_event_mono_of_pos w hw _ _ hsub
    _ ≤ ∑ t ∈ s.powersetCard m, ∑ ω, if ∀ i ∈ t, E i ω then w ω else 0 :=
      sum_event_union_le w hw (s.powersetCard m) (fun t ω => ∀ i ∈ t, E i ω)
    _ ≤ ∑ _t ∈ s.powersetCard m, δ ^ m := Finset.sum_le_sum hcyl
    _ = (s.card.choose m : ℝ) * δ ^ m := by
      simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma retained_choice_eq_of_onLine (Q : RetentionRule F)
    (M : MergedPairs F) (g : Direction F) (p : Point F)
    (c d : ChoiceCode F) (hc : c ∈ Q.candidates M g) (hd : d ∈ Q.candidates M g)
    (hpc : OnLine p c.1) (hpd : OnLine p d.1) : c = d := by
  have hcdir : c.1.1 = g := (Q.valid M g c hc).1
  have hddir : d.1.1 = g := (Q.valid M g d hd).1
  apply Q.uniqueLine M g c d hc hd
  apply Prod.ext
  · exact hcdir.trans hddir.symm
  · unfold OnLine at hpc hpd
    rw [hcdir] at hpc
    rw [hddir] at hpd
    exact hpc.symm.trans hpd

theorem fixed_offset_incident_cylinder_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F)
    (p : Point F) (S : Finset (Slot F)) :
    (∑ v : Output F, if (∀ s ∈ S, OnLine p (v s).1) then w M v else 0) ≤
      (K / Fintype.card F) ^ S.card := by
  by_cases hex : ∃ v : Output F, 0 < w M v ∧ ∀ s ∈ S, OnLine p (v s).1
  · obtain ⟨v₀, hv₀, hp₀⟩ := hex
    have hv₀mem := (hw.2.2.1 M v₀ hv₀).2.2.1
    have hsub : ∀ v : Output F, 0 < w M v →
        (∀ s ∈ S, OnLine p (v s).1) → ∀ s ∈ S, (v s).2 = (v₀ s).2 := by
      intro v hv hp s hs
      have hvmem := (hw.2.2.1 M v hv).2.2.1
      have heq := retained_choice_eq_of_onLine Q M s.1 p
        (v s) (v₀ s) (hvmem s) (hv₀mem s) (hp s hs) (hp₀ s hs)
      exact congrArg Prod.snd heq
    have hmono := sum_event_mono_of_pos (w M) (hw.1 M)
      (fun v : Output F => ∀ s ∈ S, OnLine p (v s).1)
      (fun v : Output F => ∀ s ∈ S, (v s).2 = (v₀ s).2) hsub
    have hcyl := hw.2.2.2 M S (fun s => (v₀ s).2)
    exact le_trans hmono hcyl
  · have hz : (∑ v : Output F,
        if (∀ s ∈ S, OnLine p (v s).1) then w M v else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      split_ifs with hv
      · have hnp : ¬ 0 < w M v := fun hp => hex ⟨v, hp, hv⟩
        exact le_antisymm (le_of_not_gt hnp) (hw.1 M v)
      · rfl
    rw [hz]
    exact pow_nonneg (div_nonneg hK (Nat.cast_nonneg _)) _

omit [Field F] [DecidableEq F] in

lemma card_slot : Fintype.card (Slot F) = 2 * (Fintype.card F + 1) := by
  simp only [Slot, Direction, Fintype.card_prod, Fintype.card_option, Fintype.card_bool]
  omega

lemma splitMultiplicity_le_incident_slots (M : MergedPairs F) (v : Output F)
    (p : Point F) :
    (configuration M v).splitMultiplicity p ≤
      (Finset.univ.filter (fun s : Slot F => OnLine p (v s).1)).card := by
  change ((Finset.univ.image (fun s : Slot F => (v s).1)).filter (OnLine p)).card ≤ _
  rw [Finset.filter_image]
  exact Finset.card_image_le

theorem fixed_offset_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F) (p : Point F) (m : ℕ) :
    (∑ v : Output F, if m ≤ (configuration M v).splitMultiplicity p then w M v else 0) ≤
      ((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m := by
  have hmono := sum_event_mono_of_pos (w M) (hw.1 M)
    (fun v : Output F => m ≤ (configuration M v).splitMultiplicity p)
    (fun v : Output F => m ≤ (Finset.univ.filter (fun s : Slot F => OnLine p (v s).1)).card)
    (fun v _ hv => hv.trans (splitMultiplicity_le_incident_slots M v p))
  have hcount := sum_event_at_least_le (w M) (hw.1 M) Finset.univ
    (fun s v => OnLine p (v s).1) m (K / Fintype.card F) (by
      intro S hS
      have hc := fixed_offset_incident_cylinder_le Q w K hK hw M p S
      rw [(Finset.mem_powersetCard.mp hS).2] at hc
      convert hc using 1
      apply Finset.sum_congr rfl
      intro v _
      simp only [ite_eq_ite])
  rw [Finset.card_univ, card_slot] at hcount
  exact hmono.trans hcount

theorem fixed_offset_some_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (M : MergedPairs F) (m : ℕ) :
    (∑ v : Output F, if ∃ p : Point F, m ≤ (configuration M v).splitMultiplicity p
      then w M v else 0) ≤
      (Fintype.card F : ℝ) ^ 2 *
        (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) := by
  have hu := sum_event_union_le (w M) (hw.1 M) (Finset.univ : Finset (Point F))
    (fun p v => m ≤ (configuration M v).splitMultiplicity p)
  simp only [Finset.mem_univ, true_and] at hu
  refine hu.trans ?_
  calc
    (∑ p : Point F, ∑ v : Output F,
        if m ≤ (configuration M v).splitMultiplicity p then w M v else 0)
        ≤ ∑ _p : Point F,
          ((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m :=
      Finset.sum_le_sum (fun p _ => fixed_offset_large_pencil_le Q w K hK hw M p m)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
        Nat.cast_mul, nsmul_eq_mul, pow_two]

omit [Field F] in

lemma selectedProbability_eq_sum (w : Kernel F) (E : Configuration F → Prop)
    [DecidablePred E] :
    selectedProbability w E =
      (∑ M : MergedPairs F, ∑ v : Output F,
        if E (configuration M v) then w M v else 0) / Fintype.card (MergedPairs F) := by
  unfold selectedProbability
  apply congrArg (fun x : ℝ => x / Fintype.card (MergedPairs F))
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro v _
  simp only [ite_eq_ite]

omit [Field F] in

lemma selectedProbability_nonneg (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : Configuration F → Prop) : 0 ≤ selectedProbability w E := by
  unfold selectedProbability
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro M _
    apply Finset.sum_nonneg
    intro v _
    split_ifs; exact hw M v; exact le_rfl
  · exact Nat.cast_nonneg _

theorem selected_some_large_pencil_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (m : ℕ) :
    selectedProbability w (fun C => ∃ p : Point F, m ≤ C.splitMultiplicity p) ≤
      (Fintype.card F : ℝ) ^ 2 *
        (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) := by
  rw [selectedProbability_eq_sum]
  have hcard : (0 : ℝ) < Fintype.card (MergedPairs F) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  calc
    (∑ M : MergedPairs F, ∑ v : Output F,
        if ∃ p : Point F, m ≤ (configuration M v).splitMultiplicity p then w M v else 0)
        ≤ ∑ _M : MergedPairs F, (Fintype.card F : ℝ) ^ 2 *
          (((2 * (Fintype.card F + 1)).choose m : ℝ) * (K / Fintype.card F) ^ m) :=
      Finset.sum_le_sum (fun M _ => fixed_offset_some_large_pencil_le Q w K hK hw M m)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem large_pencil_uniform_error (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F]
        (Q : RetentionRule F) (w : Kernel F), KernelConditions Q w K →
        selectedProbability w (fun C => ∃ p : Point F, logBudget F ≤ C.splitMultiplicity p) ≤
          ε (Fintype.card F) := by
  refine ⟨fun q => (q : ℝ) ^ 2 *
      (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
        (K / q) ^ Nat.ceil (Real.log (q : ℝ))), ?_, ?_, ?_⟩
  · exact BalancedRyser.tendsto_polynomial_mul_slot_choose_tail 2 K hK
  · intro q
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg hK (Nat.cast_nonneg _)) _))
  · intro F _ _ _ Q w hw
    exact selected_some_large_pencil_le Q w K hK hw (logBudget F)

end
end Balanced.Local

end OAI
