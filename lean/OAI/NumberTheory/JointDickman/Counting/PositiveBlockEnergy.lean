import OAI.NumberTheory.JointDickman.Counting.BlockEnergyApproximation
import OAI.NumberTheory.JointDickman.Amplification.SubsequencePositiveGraph

namespace OAI

/-! # Positive graph energy survives the exact passage to blocks -/

namespace JointDickman
open Filter
open scoped Topology

theorem block_scale_error_le (A T : ℕ) (hT : 0 < T) :
    (((T/A : ℕ) : ℝ)/(T : ℝ)+(T : ℝ)/(A*T : ℕ)) ≤ 2/(A : ℝ) := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hfloor := div_le_div_of_nonneg_right
    (Nat.cast_div_le (m := T) (n := A) : ((T/A : ℕ) : ℝ) ≤ (T : ℝ)/A)
    (Nat.cast_nonneg T)
  have he1 : ((T : ℝ)/A)/T = 1/(A : ℝ) := by field_simp
  have he2 : (T : ℝ)/(A*T : ℕ) = 1/(A : ℝ) := by push_cast; field_simp
  rw [he1] at hfloor
  rw [he2]
  rw [show (2 : ℝ)/(A : ℝ) = 1/(A : ℝ)+1/(A : ℝ) by ring]
  linarith only [hfloor]

theorem positive_blocks_of_graph
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {e : ℝ} (he : 0 < e) :
    ∃ A : ℕ, 0 < A ∧ ∀ (L : ℕ) (τ C : ℝ) (r : ℕ → ℕ), StrictMono r →
      ∀ F : ℕ → ℕ → ℂ, (∀ N n, ‖F N n‖ ≤ 2) →
      (∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r N) (F (r N)) /
          ((B : ℝ)*amplificationMultiplier B)) →
      ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        e/2 ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r N)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) (F (r N)) := by
  obtain ⟨K,hK,happrox⟩ := arithmetic_block_energy_approximation hFord hMertens
  obtain ⟨A,hA⟩ := exists_nat_gt (max (1 : ℝ) (8*K/e))
  have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hApos : 0 < A := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hA1)
  have hAlarge : 8*K/e < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
  have herror : K*(2/(A : ℝ)) < e/4 := by
    have hAreal : (0 : ℝ) < A := by exact_mod_cast hApos
    have hprod := (div_lt_iff₀ he).mp hAlarge
    have hh : 8*K/(A : ℝ) < e := (div_lt_iff₀ hAreal).mpr (by nlinarith only [hprod])
    calc
      _ = (8*K/(A : ℝ))/4 := by ring
      _ < e/4 := div_lt_div_of_pos_right hh (by norm_num)
  refine ⟨A,hApos,?_⟩
  intro L τ C r hr F hF hgraph
  filter_upwards [happrox,hgraph,amplificationMultiplier_valid,
    amplificationMultiplier_le_cutoff] with B hB hGraph hT hTc
  let T := amplificationMultiplier B
  have hTM : T ≤ A*T := by nlinarith [hApos]
  have happ := hB T hT.1 hT.2 hTc (T/A) (A*T) (Nat.div_le_self _ _) hTM
    (e/4) (by positivity)
  filter_upwards [hr.tendsto_atTop.eventually happ,hGraph] with N hN hGN
  have hbound := hN L τ C (F (r N)) (hF (r N))
  have hscale := mul_le_mul_of_nonneg_left (block_scale_error_le A T hT.1) hK.le
  have hdiff := (le_abs_self
    (arithmeticOffDiagonalGraph B L τ C T (r N) (F (r N))/((B : ℝ)*T) -
      arithmeticBlockAverage B L τ C T (r N) (T/A) (A*T) (F (r N)))).trans hbound
  change e ≤ arithmeticOffDiagonalGraph B L τ C T (r N) (F (r N))/((B : ℝ)*T) at hGN
  linarith only [hdiff,hGN,hscale,herror]

end JointDickman

end OAI
