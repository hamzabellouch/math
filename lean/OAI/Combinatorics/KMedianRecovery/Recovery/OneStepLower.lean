import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BlindUpdate
import OAI.Combinatorics.KMedianRecovery.Encoding.PrecisionBits

namespace OAI

namespace MetricKMedianRecovery.Sampling.Precision
open RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

lemma one_step_lower (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ : ℝ) (hΔ : 1 ≤ Δ) (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (s : Option (State V)) (hs : Good s)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (a : Action D M E J) (hp : 0 < transitionWeight D S Δ M E J s a) :
    1/(6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J) ≤ transitionWeight D S Δ M E J s a := by
  let A : ℝ := 2*(D.card:ℝ)*Δ
  let B : ℝ := 3*((M:ℝ)+E+1)*2^J
  have hn : (1:ℝ) ≤ D.card := by exact_mod_cast hD.card_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith
  have hQ : (1:ℝ) ≤ (M:ℝ)+E+1 := by
    linarith [Nat.cast_nonneg (α := ℝ) M,Nat.cast_nonneg (α := ℝ) E]
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    have hpow : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    dsimp [B]
    nlinarith
  have hAB : A*B = 6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J := by dsimp [A,B]; ring
  have hOne : 1/(A*B) ≤ (1:ℝ) := by
    apply (div_le_iff₀ (mul_pos hA hB)).mpr
    nlinarith
  rw [← hAB]
  cases s with
  | none =>
    by_cases ha : a = Sum.inl ()
    · simpa only [transitionWeight,ite_eq_left ha] using hOne
    · simp only [transitionWeight,ite_eq_right ha,lt_self_iff_false] at hp
  | some s =>
    by_cases hw : 0 < totalWeight D S Δ s
    · have hR (w : D) : 1/A ≤ clientWeight S Δ s w/(2*totalWeight D S Δ s) := by
        apply (div_le_div_iff₀ hA (by positivity)).mpr
        have hh := client_lower D F S hSF Δ hΔ s (hs s rfl) hsep w w.property
        have ht := total_upper D S Δ (by linarith) s
        dsimp [A]
        nlinarith
      rcases a with u | (w | ⟨w,e⟩)
      · simp only [transitionWeight,ite_eq_left hw,lt_self_iff_false] at hp
      · simp only [transitionWeight,ite_eq_left hw]
        apply le_trans _ (hR w)
        apply one_div_le_one_div_of_le hA
        nlinarith
      · simp only [transitionWeight,ite_eq_left hw]
        calc
          1/(A*B) = (1/A)*(1/B) := by simp only [one_div,mul_inv_rev]; ring
          _ ≤ _ := mul_le_mul (hR w) (menuWeight_uniform_lower M E J hM hJ e)
            (by positivity) (div_nonneg (le_max_left _ _) (by positivity))
    · by_cases ha : a = Sum.inl ()
      · simpa only [transitionWeight,ite_eq_right hw,ite_eq_left ha] using hOne
      · simp only [transitionWeight,ite_eq_right hw,ite_eq_right ha,lt_self_iff_false] at hp

lemma one_step_accuracy (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ : ℝ) (hΔ : 1 ≤ Δ) (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (s : Option (State V)) (hs : Good s)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (a : Action D M E J) (hp : 0 < transitionWeight D S Δ M E J s a) :
    2 ≤ (2:ℝ)^(precisionBits D.card (Nat.ceil Δ) M E J) *
      transitionWeight D S Δ M E J s a := by
  have hn : (0:ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hden : 0 < 6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J := by positivity
  have hl := (div_le_iff₀ hden).mp
    (one_step_lower D F S hD hSF Δ hΔ M E J hM hJ s hs hsep a hp)
  have hu : 12*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J ≤
      (2:ℝ)^(precisionBits D.card (Nat.ceil Δ) M E J) := by
    apply le_trans _ (precision_power D.card (Nat.ceil Δ) M E J)
    gcongr
    exact Nat.le_ceil Δ
  have hm := mul_le_mul_of_nonneg_right hu hp.le
  nlinarith only [hl,hm]

lemma precise_every_history (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ P kappa : ℝ) (hΔ : 1 ≤ Δ) (m M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) (n : ℕ)
    (s : Option (State V)) (hs : Good s) :
    Precise (update D F S hD Δ P kappa m M E J) (actualKernel D S Δ M E J hM hJ)
      (precisionBits D.card (Nat.ceil Δ) M E J) n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih _ (good_update D F S hD Δ P kappa m M E J s a hsep hs)⟩
    exact one_step_accuracy D F S hD hSF Δ hΔ M E J hM hJ s hs hsep

end MetricKMedianRecovery.Sampling.Precision

end OAI
