import Mathlib
import OAI.Analysis.Commutator.DyadicDimensionNormal
import OAI.Analysis.Commutator.ProjectionJoin
import OAI.Analysis.Commutator.ProjectionStrong

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def finiteJoin (P : ℕ → H →L[ℂ] H) : ℕ → H →L[ℂ] H
  | 0 => 0
  | n+1 => join (finiteJoin P n) (P n)

lemma finiteJoin_projection (P : ℕ → H →L[ℂ] H) (n : ℕ) : IsStarProjection (finiteJoin P n) := by
  induction n with
  | zero => exact IsStarProjection.zero _
  | succ n ih => exact join_projection ih _

lemma finiteJoin_mem (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H) (hP : ∀ n,P n∈M) (n : ℕ) :
    finiteJoin P n∈M := by
  induction n with
  | zero => exact M.zero_mem
  | succ n ih => exact join_mem M ih (hP n)

lemma finiteJoin_mono (P : ℕ → H →L[ℂ] H) : Monotone (finiteJoin P) :=
  monotone_nat_of_le_succ fun n => left_le (finiteJoin_projection P n) _

lemma le_finiteJoin_succ (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n)) (n : ℕ) :
    P n≤finiteJoin P (n+1) := right_le (finiteJoin_projection P n) (hP n)

lemma finiteJoin_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    {Q : H →L[ℂ] H} (hQ : IsStarProjection Q) (hle : ∀ n,P n≤Q) (n : ℕ) : finiteJoin P n≤Q := by
  induction n with
  | zero => exact hQ.nonneg
  | succ n ih => exact join_le (finiteJoin_projection P n) (hP n) hQ ih (hle n)

theorem exists_countable_sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) :
    ∃ W : H →L[ℂ] H,W∈M ∧ IsStarProjection W ∧ (∀ n,P n≤W) ∧
      (∀ x,Tendsto (fun n => finiteJoin P n x) atTop (𝓝 (W x))) ∧
      ∀ Q : H →L[ℂ] H,IsStarProjection Q → (∀ n,P n≤Q) → W≤Q := by
  obtain ⟨W,hWM,hW,hPW,hlim,hle⟩ := ProjectionChains.exists_strong_sup M (finiteJoin P)
    (finiteJoin_projection P) (finiteJoin_mem M P hPM) (finiteJoin_mono P)
  exact ⟨W,hWM,hW,fun n => (le_finiteJoin_succ P hP n).trans (hPW (n+1)),hlim,
    fun Q hQ hPQ => hle Q hQ (finiteJoin_le P hP hQ hPQ)⟩

def sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : H →L[ℂ] H :=
  (exists_countable_sup M P hP hPM).choose

lemma sup_mem (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : sup M P hP hPM∈M :=
  (exists_countable_sup M P hP hPM).choose_spec.1

lemma sup_projection (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : IsStarProjection (sup M P hP hPM) :=
  (exists_countable_sup M P hP hPM).choose_spec.2.1

lemma le_sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) (n : ℕ) : P n≤ sup M P hP hPM :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.1 n

lemma sup_strong (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) (x : H) :
    Tendsto (fun n => finiteJoin P n x) atTop (𝓝 (sup M P hP hPM x)) :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.2.1 x

lemma sup_le (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M)
    {Q : H →L[ℂ] H} (hQ : IsStarProjection Q) (hle : ∀ n,P n≤Q) : sup M P hP hPM≤Q :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.2.2 Q hQ hle

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

omit [TopologicalSpace.SeparableSpace H] in
lemma dimension_finiteJoin_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    (hPM : ∀ n,P n∈M) (n : ℕ) :
    dimension M hfac hd (finiteJoin P n)≤∑ k∈Finset.range n,dimension M hfac hd (P k) := by
  induction n with
  | zero => simpa only [finiteJoin,Finset.range_zero,Finset.sum_empty] using dimension_zero M hfac hd hfin |>.le
  | succ n ih =>
    rw [finiteJoin,Finset.sum_range_succ]
    exact (dimension_join_le M hfac hd hfin (finiteJoin_mem M P hPM n) (hPM n)
      (finiteJoin_projection P n) (hP n)).trans (by linarith)

theorem dimension_sup_le (P : ℕ → H →L[ℂ] H) (hP : ∀ n,IsStarProjection (P n))
    (hPM : ∀ n,P n∈M) (b : ℕ → ℝ) (hb : Summable b)
    (hPb : ∀ n,dimension M hfac hd (P n)≤b n) :
    dimension M hfac hd (sup M P hP hPM)≤∑' n,b n := by
  have hlim := dimension_tendsto_of_strong_increasing M hfac hd hfin (sup_mem M P hP hPM)
    (sup_projection M P hP hPM) (finiteJoin P) (finiteJoin_mem M P hPM) (finiteJoin_projection P)
    (finiteJoin_mono P) (finiteJoin_le P hP (sup_projection M P hP hPM) (le_sup M P hP hPM))
    (sup_strong M P hP hPM)
  apply le_of_tendsto_of_tendsto hlim hb.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun n => (dimension_finiteJoin_le M hfac hd hfin P hP hPM n).trans
    (Finset.sum_le_sum fun k _ => hPb k)

end Kadison.ProjectionJoin

end

end
end

end OAI
