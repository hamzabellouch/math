import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCaller

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

 theorem actual_marked_bin_empty
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (he:¬(progressingCubes S D H₀ Q).Nonempty) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a=0 := by
  rw [marked_long_filter,Finset.not_nonempty_iff_eq_empty.mp he]
  simp only [markedReopenedCubeBin,Finset.sum_empty]

theorem actual_large_bins_aggregate
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(b X H₀ R Z V E:ℝ)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (hbin:∀j∈cubeLogRange b X,
      (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty→
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E)
    (hE:0≤E) :
    Z^(-V)*((cubeLogRange b X).card*∑j∈cubeLogRange b X,
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R)≤
      ((cubeLogRange b X).card:ℝ)^2*E := by
  have hj (j:ℕ)(hj:j∈cubeLogRange b X) :
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E := by
    by_cases hn:(progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · exact hbin j hj hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simpa only [markedReopenedCubeBin,Finset.sum_empty,rowFamilyEnergy,
        nonzeroRowMajorantSum,norm_zero,zero_pow (by decide:2≠0),Complex.ofReal_zero,
        mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hE
  calc
    _=(cubeLogRange b X).card*∑j∈cubeLogRange b X,
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R := by rw [←Finset.mul_sum];ring
    _≤(cubeLogRange b X).card*∑_j∈cubeLogRange b X,E := by
      gcongr
      exact hj _ ‹_›
    _=_ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end SevenEighths.InverseMoment

end

end OAI
