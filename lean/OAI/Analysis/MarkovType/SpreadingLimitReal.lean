import OAI.Analysis.MarkovType.C00FiniteCoordinates
import OAI.Analysis.MarkovType.SpreadingLimitCauchy
import OAI.Analysis.MarkovType.SpreadingLimitDiagonal
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Countable.Basic
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

abbrev RationalCoefficients := Σ m : ℕ, Fin m → ℚ

theorem exists_rational_coefficients {m : ℕ} (a : Fin m → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Fin m → ℚ, (∑ i, |a i - (q i : ℝ)|) < ε := by
  classical
  let δ : ℝ := ε / ((m : ℝ) + 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  choose q hq using fun i : Fin m => exists_rat_near (a i) hδ
  refine ⟨q, ?_⟩
  have hsum : (∑ i, |a i - (q i : ℝ)|) ≤ (m : ℝ) * δ := by
    calc
      (∑ i, |a i - (q i : ℝ)|) ≤ ∑ _i : Fin m, δ :=
        Finset.sum_le_sum (fun i _ => (hq i).le)
      _ = (m : ℝ) * δ := by simp
  have hcancel : δ * ((m : ℝ) + 1) = ε :=
    div_mul_cancel₀ ε hden.ne'
  nlinarith

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_cauchy_subsequence
    (L : ℕ → C00 →ₗ[ℝ] Y)
    (hunit : ∀ n i, ‖L n (C00.basis i)‖ ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ x : C00, CauchySeq (fun n => ‖L (σ n) x‖) := by
  let v : ℕ → RationalCoefficients → ℝ :=
    fun n q => ‖L n (C00.ofArray (fun i => (q.2 i : ℝ)))‖
  let b : RationalCoefficients → ℝ := fun q => ∑ i, |(q.2 i : ℝ)|
  have hbound : ∀ n q, v n q ∈ Set.Icc 0 (b q) := by
    intro n q
    exact ⟨norm_nonneg _, C00.norm_linearMap_ofArray_le (L n) (hunit n) _⟩
  obtain ⟨σ, hσ, hlimit⟩ := exists_common_subsequence_of_bounded v b hbound
  have hrat (m : ℕ) (q : Fin m → ℚ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray (fun i => (q i : ℝ)))‖) := by
    obtain ⟨l, hl⟩ := hlimit ⟨m, q⟩
    exact hl.cauchySeq
  have hreal (m : ℕ) (a : Fin m → ℝ) :
      CauchySeq (fun n => ‖L (σ n) (C00.ofArray a)‖) := by
    apply cauchySeq_of_dense_lipschitz
      (fun n a => ‖L (σ n) (C00.ofArray a)‖)
      (fun q : Fin m → ℚ => fun i => (q i : ℝ))
      (fun a b : Fin m → ℝ => ∑ i, |a i - b i|)
      (fun n a b => C00.abs_norm_linearMap_ofArray_sub_le (L (σ n)) (hunit (σ n)) a b)
      (fun a ε hε => exists_rational_coefficients a ε hε)
      (hrat m) a
  refine ⟨σ, hσ, ?_⟩
  intro x
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha]
  exact hreal m a

end MarkovSuperreflexivity

end

end OAI
