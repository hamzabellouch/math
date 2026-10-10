import OAI.Combinatorics.BalancedRyser.Local.LocalEndpointCompletion

namespace OAI

namespace Balanced.Local.SourceRate

noncomputable section
open scoped BigOperators
open Filter
open scoped Topology

def factorialMoment (a : ℕ) (A : ℝ) : ℝ :=
  ∑' b : ℕ, (b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)

def largeTail (K : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) ^ 2 * (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
    (K / q) ^ Nat.ceil (Real.log (q : ℝ)))

theorem factorialMoment_nonneg (a : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ factorialMoment a A := by
  unfold factorialMoment
  exact tsum_nonneg (fun b => by positivity)

theorem plane_sum_le (q B A : ℝ) (hq : 0 < q) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (a : ℕ) (s : Finset ℕ) :
    q ^ 2 * (∑ b ∈ s, ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
      (B ^ 3 / q ^ 3)) ≤ factorialMoment a A * (B ^ 3 / q) := by
  rw [← Finset.sum_mul]
  calc
    q ^ 2 * ((∑ b ∈ s, (b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
        (B ^ 3 / q ^ 3)) =
        (∑ b ∈ s, (b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) * (B ^ 3 / q) := by
      field_simp
    _ ≤ factorialMoment a A * (B ^ 3 / q) :=
      mul_le_mul_of_nonneg_right
        (LocalAsymptotics.sum_polynomial_mul_pow_div_factorial_le a A hA s)
        (by positivity)

theorem tendsto_largeTail (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (largeTail K) atTop (𝓝 0) := by
  unfold largeTail
  exact BalancedRyser.tendsto_polynomial_mul_slot_choose_tail 2 K hK

theorem tendsto_source_error (K C : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun q : ℕ => largeTail K q +
      C * ((Nat.ceil (Real.log (q : ℝ)) : ℝ) ^ 3 / (q : ℝ))) atTop (𝓝 0) := by
  simpa using (tendsto_largeTail K hK).add
    (LocalAsymptotics.tendsto_ceil_log_cube_div_nat.const_mul C)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in

theorem one_le_logBudget : 1 ≤ logBudget F := by
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  exact Nat.ceil_pos.mpr (Real.log_pos hq)

theorem small_bad_local_probability_le_rate
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (a : ℕ) (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hsmall : ∀ (p : Point F) b, b ∈ Finset.Icc 3 (logBudget F) →
      ∀ κ ∈ Finset.range 3,
        selectedProbability w (fun C => C.splitMultiplicity p = b ∧
          reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
          L * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
            ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))) :
    selectedProbability w SmallBadLocalEvent ≤
      (3 * L * factorialMoment a A) *
        ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ)) := by
  have hs := small_bad_local_probability_le_envelope w hw L
    (fun b => ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
      ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3)) hsmall
  have hp := plane_sum_le (Fintype.card F : ℝ) (logBudget F : ℝ) A
    (by positivity) (Nat.cast_nonneg _) hA a (Finset.Icc 3 (logBudget F))
  exact hs.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * L by positivity))

theorem local_failure_probability_le_rate
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK : 0 ≤ K)
    (hw : KernelConditions Q w K) (a : ℕ) (A L C : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hhigh : ∀ p : Point F,
      selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3)
    (hsmall : ∀ (p : Point F) b, b ∈ Finset.Icc 3 (logBudget F) →
      ∀ κ ∈ Finset.range 3,
        selectedProbability w (fun X => X.splitMultiplicity p = b ∧
          reuseCount X p = κ ∧ BadLocalCoverAt b p X) ≤
          L * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
            ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))) :
    selectedProbability w (fun X => ¬ X.LocalCondition) ≤
      largeTail K (Fintype.card F) +
        (C + 3 * L * factorialMoment a A) *
          ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ)) := by
  have hlarge : selectedProbability w LargePencilEvent ≤ largeTail K (Fintype.card F) := by
    apply (KernelBridge.selectedProbability_mono w hw.1 ?_).trans
      (selected_some_large_pencil_le Q w K hK hw (logBudget F))
    intro X hX
    obtain ⟨p, hp⟩ := hX
    exact ⟨p, hp.le⟩
  have hB : (1 : ℝ) ≤ logBudget F := by exact_mod_cast (one_le_logBudget (F := F))
  have hhigh' : selectedProbability w HighReuseEvent ≤
      C * ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ)) := by
    refine (high_reuse_probability_le w hw.1 C hhigh).trans ?_
    calc
      C / (Fintype.card F : ℝ) = C * (1 / (Fintype.card F : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact one_le_pow₀ hB
  have hsmall' := small_bad_local_probability_le_rate w hw.1 a A L hA hL hsmall
  have hcases := selectedProbability_le_three_of_positive_imp w hw.1
    (fun X => ¬ X.LocalCondition) LargePencilEvent HighReuseEvent SmallBadLocalEvent
    (fun _ _ _ hbad => local_failure_cases _ hbad)
  refine hcases.trans ((add_le_add (add_le_add hlarge hhigh') hsmall').trans_eq ?_)
  ring

universe u

theorem local_source_rate_of_two_reuses (hTwo : PencilTwoReusesResult.{u}) :
    ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
          KernelConditions Q w K →
          selectedProbability w (fun X => ¬ X.LocalCondition) ≤
            largeTail K (Fintype.card F) +
              C * ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ)) := by
  intro K hK
  obtain ⟨R, hR, qR, hhigh⟩ := pencilReuse_proof.{u} K hK
  obtain ⟨D, hD, qT, htwo⟩ := hTwo
  let L : ℝ := 2048 * (148 : ℝ) ^ 3 + 256 * D
  let A : ℝ := 1024 * K
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨R + 3 * L * factorialMoment 16 A, ?_, max qR qT, ?_⟩
  · have hm := factorialMoment_nonneg 16 A hA
    exact add_pos_of_pos_of_nonneg hR (by positivity)
  · intro F _ _ _ hq Q w hw
    apply local_failure_probability_le_rate Q w K hK.le hw 16 A L R hA hL hR.le
    · exact hhigh F ((le_max_left qR qT).trans hq) Q w hw
    · intro p b hb κ hk
      obtain ⟨hb, hB⟩ := Finset.mem_Icc.mp hb
      have hk2 : κ ≤ 2 := by have := Finset.mem_range.mp hk; omega
      have hqR : (0 : ℝ) < Fintype.card F := by positivity
      have hBR : (1 : ℝ) ≤ logBudget F := by exact_mod_cast (one_le_logBudget (F := F))
      let W : ℝ := (((b : ℝ) ^ 16 * A ^ b / (b.factorial : ℝ)) *
        ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))
      have hW : 0 ≤ W := by dsimp [W]; positivity
      by_cases hkexact : κ = 2
      · subst κ
        have hraw := bad_pencil_probability_le_common_factor Q w K hK.le hw p
          (by omega : 2 ≤ b) (by omega : 2 ≤ 2)
          (D * (b : ℝ) ^ 3 / Fintype.card F) (by positivity) (by
            intro P bits
            exact htwo F ((le_max_right qR qT).trans hq) b hb hB P bits p)
        have harith := two_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
          D A b 16 hqR hBR (by omega) hD.le hA (by omega)
        refine hraw.trans (harith.trans ?_)
        change (256 * D) * W ≤ L * W
        apply mul_le_mul_of_nonneg_right _ hW
        dsimp [L]
        linarith
      · have hk1 : κ ≤ 1 := by omega
        have hraw := bad_pencil_probability_le_of_conditioned Q w K hK.le hw p
          (by omega : 2 ≤ b) hk2
          ((148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
            (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ)) (by positivity)
          (fun P a ha bits => alignmentNormalization_proof F b κ hb hB hk2 P a ha bits p)
          (fun P a ha bits =>
            AlignedGlobal.smallReuse_badCover_probability_bound P a bits p hb hB hk1 ha)
        have harith := small_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
          ((148 : ℝ) ^ 3) A b 9 16 κ hqR hBR (by omega) (by positivity) hA
          (by omega) (by omega)
        refine hraw.trans (harith.trans ?_)
        change (2048 * (148 : ℝ) ^ 3) * W ≤ L * W
        apply mul_le_mul_of_nonneg_right _ hW
        dsimp [L]
        linarith

end
end Balanced.Local.SourceRate

end OAI
