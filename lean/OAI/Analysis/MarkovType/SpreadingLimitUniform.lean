import OAI.Analysis.MarkovType.CoefficientGrid
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

theorem coefficient_limit_lipschitz {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (a b : Fin m → ℝ) : |f a - f b| ≤ ∑ i, |a i - b i| := by
  apply abs_le.mpr
  constructor
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).1)
  · exact le_of_tendsto' ((hlim a).sub (hlim b))
      (fun n => (abs_le.mp (hlip n a b)).2)

theorem uniform_coefficients_of_pointwise {m : ℕ}
    (v : ℕ → (Fin m → ℝ) → ℝ) (f : (Fin m → ℝ) → ℝ)
    (hlip : ∀ n a b, |v n a - v n b| ≤ ∑ i, |a i - b i|)
    (hlim : ∀ a, Tendsto (fun n => v n a) atTop (𝓝 (f a)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : Fin m → ℝ,
      (∀ i, |a i| ≤ 1) → |v n a - f a| < ε := by
  classical
  have hmpos : 0 < (m : ℝ) + 1 := by positivity
  have hethird : 0 < ε / 3 := by positivity
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt
    (show 0 < ε / (3 * ((m : ℝ) + 1)) by positivity)
  let k : ℕ := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsmall : 1 / (k : ℝ) < ε / (3 * ((m : ℝ) + 1)) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using hj
  have hmesh : 1 / (k : ℝ) ^ 2 ≤ 1 / (k : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hkR _) hkR).mpr
    nlinarith
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) < ε / 3 := by
    have hmul := mul_lt_mul_of_pos_left hsmall hmpos
    have hcancel : ((m : ℝ) + 1) * (ε / (3 * ((m : ℝ) + 1))) = ε / 3 := by
      field_simp [hmpos.ne']
    rw [hcancel] at hmul
    have hstep := mul_le_mul_of_nonneg_left hmesh (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hinv : 0 ≤ 1 / (k : ℝ) := by positivity
    nlinarith
  let Grid := Fin m → Fin (2 * k ^ 2 + 1)
  let coeff : Grid → Fin m → ℝ := fun g i => coefficientGridValue k (g i)
  have hpoint (g : Grid) :
      ∃ N : ℕ, ∀ n ≥ N, |v n (coeff g) - f (coeff g)| < ε / 3 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hlim (coeff g)) (ε / 3) hethird
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn⟩
  choose cutoff hcutoff using hpoint
  let N : ℕ := Finset.univ.sup cutoff
  refine ⟨N, ?_⟩
  intro n hn a ha
  choose g hg using fun i : Fin m => exists_coefficientGrid_approx k hk (a i) (ha i)
  have hsum : (∑ i, |a i - coeff g i|) ≤ (m : ℝ) * (1 / (k : ℝ) ^ 2) := by
    calc
      (∑ i, |a i - coeff g i|) ≤ ∑ _i : Fin m, 1 / (k : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hg i)
      _ = (m : ℝ) * (1 / (k : ℝ) ^ 2) := by simp
  have hleft : |v n a - v n (coeff g)| < ε / 3 :=
    (hlip n a (coeff g)).trans_lt (hsum.trans_lt hbudget)
  have hright : |f a - f (coeff g)| < ε / 3 :=
    (coefficient_limit_lipschitz v f hlip hlim a (coeff g)).trans_lt
      (hsum.trans_lt hbudget)
  have hgN : cutoff g ≤ N := Finset.le_sup (Finset.mem_univ g)
  have hmiddle := hcutoff g n (hgN.trans hn)
  obtain ⟨hl0, hl1⟩ := abs_lt.mp hleft
  obtain ⟨hr0, hr1⟩ := abs_lt.mp hright
  obtain ⟨hm0, hm1⟩ := abs_lt.mp hmiddle
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end MarkovSuperreflexivity

end

end OAI
