import OAI.Probability.InvariantIsing.Fields.FieldBounds
import OAI.Probability.InvariantIsing.Spectral.SpectralEnergy

namespace OAI

/-! Finiteness and finite-entropy approximate minimizers of the finite-spectrum
variational problem. These justify taking the infimum in the pressure bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem finiteSpectralFunctional_abs_le {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) (p : OverlapPath) :
    |spectralFunctional (finiteR ρ eig hρ hρsum) p| ≤ K / 2 := by
  have hb x : |finiteR ρ eig hρ hρsum x - 0| ≤ K := by
    simpa only [sub_zero] using abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  simpa only [spectralFunctional_constant, zero_div, sub_zero] using
    abs_spectralFunctional_sub_le (finiteR ρ eig hρ hρsum) (fun _ => 0)
      (continuous_finiteR ρ eig hρ hρsum) continuous_const K (fun x _ => hb x) p

theorem finiteVariational_mem_interval {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) :
    (-(K / 2) : ℝ) ≤ variationalFunctional (finiteR ρ eig hρ hρsum) ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≤ (K / 2 : ℝ) := by
  constructor
  · apply le_iInf
    intro p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).1
    have he : ((-(K / 2) : ℝ) : EReal) ≤
        (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) := by exact_mod_cast hs
    have hadd := add_le_add (entropyFunctional_nonneg p)
      (le_rfl : (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) ≤ _)
    exact he.trans (by simpa only [zero_add] using hadd)
  · let p := constantPath 0 (by constructor <;> norm_num)
    have hi := iInf_le (fun p : OverlapPath => entropyFunctional p +
      (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal)) p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).2
    simp only [p, entropyFunctional_zero, zero_add] at hi
    exact hi.trans (by exact_mod_cast hs)

theorem finiteVariational_ne_top_bot {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) :
    variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊤ ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊥ := by
  let K := ∑ a, |eig a|
  have heig a : |eig a| ≤ K := Finset.single_le_sum
    (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hb := finiteVariational_mem_interval ρ eig hρ hρsum K heig
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hb.2,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb.1⟩

theorem exists_finiteEntropy_trial_near_finiteVariational {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : OverlapPath, ∃ S : ℝ, entropyFunctional p = (S : EReal) ∧
      S + spectralFunctional (finiteR ρ eig hρ hρsum) p <
        (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε := by
  have hf := finiteVariational_ne_top_bot ρ eig hρ hρsum
  have hlt : variationalFunctional (finiteR ρ eig hρ hρsum) <
      ((variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε : ℝ) := by
    rw [← EReal.coe_toReal hf.1 hf.2]
    exact_mod_cast (show (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal <
      (variationalFunctional (finiteR ρ eig hρ hρsum)).toReal + ε by linarith)
  obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
  have htop : entropyFunctional p ≠ ⊤ := by
    intro he
    simp only [he, EReal.top_add_coe, not_top_lt] at hp
  have hbot : entropyFunctional p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (entropyFunctional_nonneg p)
  refine ⟨p, (entropyFunctional p).toReal, (EReal.coe_toReal htop hbot).symm, ?_⟩
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_add] at hp
  exact_mod_cast hp

end InvariantIsing

end

end OAI
