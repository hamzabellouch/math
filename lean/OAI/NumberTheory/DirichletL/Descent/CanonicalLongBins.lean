import OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_family_binned
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(hWc:HasCompactSupport W)
    (b X H₀ K:ℝ)(hX:0<X)(hK:0<K)(hW:∀t,W t≠0→t≤b)(hD:b*X≤D)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    rowFamilyEnergy labels (fun I z=>outsideCanonicalMarkedRow S D hbad Ψ m
      (idealGenerator I) z slots lists a W X) K ≤
    2*X*(rowFamilyEnergy labels (fun I z=>
      markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)) K+
      (cubeLogRange b X).card*∑j∈cubeLogRange b X,
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a) K) := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK]
  have he:∀I z,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W X‖^2 ≤
      2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2) := by
    intro I z
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b X H₀ slots lists a
      hbad hSp hWc hX hW hD
    have hs:(∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)=
        ∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [marked_long_filter S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a]
    rw [hs] at hh
    exact hh
  calc
    _≤∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
      (rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re *
      (2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (he I z) (rowMajorant_nonneg _)
    _=_ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_left_comm _ _ _
      · simp_rw [Finset.sum_comm (s:=(firstFrequencyDisk (2*K)).erase 0) (t:=cubeLogRange b X)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        ring

end SevenEighths.InverseMoment

end

end OAI
