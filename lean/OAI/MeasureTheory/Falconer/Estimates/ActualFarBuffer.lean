import OAI.MeasureTheory.Falconer.Angular.AngularFarDepth
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

namespace PlanarFalconer

noncomputable def sourceFarBuffer (N L : ℕ) (sig : ℝ) : ℕ :=
  max L ⌈10*sig*(N:ℝ)⌉₊

theorem sourceFarBuffer_ge_length (N L : ℕ) (sig : ℝ) : L ≤ sourceFarBuffer N L sig :=
  le_max_left _ _

theorem sourceFarBuffer_ge_slack (N L : ℕ) (sig : ℝ) :
    10*sig*(N:ℝ) ≤ (sourceFarBuffer N L sig:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem uniform_source_far_buffer {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L v a : ℕ,
      let L₀ := sourceFarBuffer N L sig
      let h := v-2*L₀
      a < h →
      let d := h-a
      a+d = h ∧ a+d+5 < v ∧
      (v:ℝ)-(a+d:ℕ) = 2*(L₀:ℝ) ∧ (L:ℝ) ≤ (L₀:ℝ) ∧
      10*sig*(N:ℝ) ≤ (L₀:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨N₀,?_⟩
  intro N hN L v a
  dsimp only
  intro hah
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr hN)
  have hsigN : 1 < sig*(N:ℝ) := by
    have ht := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hslack := sourceFarBuffer_ge_slack N L sig
  have hbuf : 5 < 2*sourceFarBuffer N L sig := by
    have hb : (5:ℝ) < 2*(sourceFarBuffer N L sig:ℝ) := by linarith
    exact_mod_cast hb
  have h2 : 2*sourceFarBuffer N L sig ≤ v := by omega
  have he : a+(v-2*sourceFarBuffer N L sig-a) = v-2*sourceFarBuffer N L sig := by omega
  refine ⟨he,by omega,?_,Nat.cast_le.mpr (sourceFarBuffer_ge_length N L sig),hslack⟩
  rw [he,Nat.cast_sub h2,Nat.cast_mul,Nat.cast_ofNat]
  ring

end PlanarFalconer

end OAI
