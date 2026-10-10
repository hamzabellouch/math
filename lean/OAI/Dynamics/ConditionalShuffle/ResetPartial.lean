import OAI.Dynamics.ConditionalShuffle.ResetEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter Topology
namespace Thorp.Conditional
theorem prefix_test_energy (d t m : ℕ) (ε : ℝ)
    (hE : ∀ (B : Position (d+2) → Bool) (tag) (ht : B tag = true),
      m ≤ freeCount B → expectedEnergy (d+1) (initialState (d+2) B tag ht) t ≤ ε)
    (k : ℕ) (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e)
    (f : (Fin k → Position (d + 2)) → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 2) t => f ((run (d + 2) t ω) ∘ e)) -
      mean (fun g : State (d + 2) => f (g ∘ e))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ε) := by
  induction k with
  | zero =>
    have hz (g : State (d + 2)) : g ∘ e = e := by funext i; exact Fin.elim0 i
    simp only [hz, mean_const, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    have he0 : Function.Injective (Fin.init e) := by
      intro i j hij
      exact Fin.castSucc_inj.mp (he hij)
    have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
      apply (freeOf_true _ _).mpr
      intro i hi
      exact Fin.castSucc_ne_last i (he hi)
    have hcount : m ≤ freeCount (freeOf (Fin.init e)) := by
      rw [freeCount_freeOf _ he0]
      omega
    have henergy := hE (freeOf (Fin.init e)) (e (Fin.last k)) ht hcount
    have hz := prefix_one_step_bound (d + 1) t k e he f hf
    have hestimate :
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          expectedEnergy (d + 1) (initialState (d + 2) (freeOf (Fin.init e)) (e (Fin.last k)) ht)
            t) ≤
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          ε) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact henergy
    have hnext := ih (by omega) (Fin.init e) he0 (completeTest f) (completeTest_bound f hf)
    rw [uniform_prefix_step k e he f]
    have htri := abs_sub_le
      (mean (fun ω : History (d + 2) t => f ((run (d + 2) t ω) ∘ e)))
      (mean (fun ω : History (d + 2) t => completeTest f ((run (d + 2) t ω) ∘ Fin.init e)))
      (mean (fun g : State (d + 2) => completeTest f (g ∘ Fin.init e)))
    have hz' := hz.trans hestimate
    push_cast
    nlinarith

lemma reset_sqrt_bound (D : ℕ) :
    Real.sqrt ((2^D : ℝ)*(1/2 : ℝ)^(20*D)) ≤ (1/2 : ℝ)^(9*D) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  have he : (2^D : ℝ)*(1/2 : ℝ)^(20*D) = (1/2 : ℝ)^(19*D) := by
    rw [pow_mul, ← mul_pow, pow_mul]; norm_num
  rw [he, ← pow_mul]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  omega

theorem reset_partial_mixing (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    ∀ᶠ d : ℕ in atTop, ∀ (b : ℕ) (e : Fin b → Position (d+2)),
      Function.Injective e → (b : ℝ) ≤ (1-ρ)*(2^(d+2) : ℝ) →
      tv (fairMass (fun ω : History (d+2) (2*resetS ρ*(d+2)) =>
        run (d+2) (2*resetS ρ*(d+2)) ω ∘ e))
        (fairMass (fun g : State (d+2) => g ∘ e)) ≤ (1/2 : ℝ)^(8*(d+2)) := by
  filter_upwards [reset_energy_eventually ρ hρ hρ₁] with d hd
  intro b e he hb
  have hbN : b ≤ Fintype.card (Position (d+2)) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he
  let m := Fintype.card (Position (d+2)) - b
  have hm : ρ * Fintype.card (Position (d+2)) ≤ (m : ℝ) := by
    dsimp [m]; rw [Nat.cast_sub hbN]
    rw [card_position] at *; push_cast at *; nlinarith
  have hE (B : Position (d+2) → Bool) (tag) (ht : B tag = true) (hB : m ≤ freeCount B) :
      expectedEnergy (d+1) (initialState (d+2) B tag ht) (2*resetS ρ*(d+2)) ≤
        (1/2 : ℝ)^(20*(d+2)) := by
    apply hd
    exact hm.trans (by exact_mod_cast hB)
  have hh := fairMass_tv_le_of_test
    (fun ω : History (d+2) (2*resetS ρ*(d+2)) => run (d+2) (2*resetS ρ*(d+2)) ω ∘ e)
    (fun g : State (d+2) => g ∘ e)
    ((b : ℝ)*Real.sqrt ((Fintype.card (Position (d+2)) : ℝ)*(1/2 : ℝ)^(20*(d+2))))
    (prefix_test_energy d (2*resetS ρ*(d+2)) m _ hE b (by dsimp [m]; omega) e he)
  have hbN' : (b : ℝ) ≤ (2^(d+2) : ℝ) := by simpa only [card_position, Nat.cast_pow, Nat.cast_ofNat] using
    (show (b : ℝ) ≤ (Fintype.card (Position (d+2)) : ℝ) by exact_mod_cast hbN)
  have hmul : (2^(d+2) : ℝ)*(1/2 : ℝ)^(9*(d+2)) = (1/2 : ℝ)^(8*(d+2)) := by
    rw [pow_mul, ← mul_pow, pow_mul]; norm_num
  apply hh.trans
  rw [card_position, Nat.cast_pow, Nat.cast_ofNat]
  have hsq := reset_sqrt_bound (d+2)
  have hproduct := mul_le_mul hbN' hsq (Real.sqrt_nonneg _) (by positivity)
  rw [hmul] at hproduct
  linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (8*(d+2))]

end Thorp.Conditional

end

end OAI
