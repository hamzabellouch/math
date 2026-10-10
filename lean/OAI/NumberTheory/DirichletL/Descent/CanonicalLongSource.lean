import OAI.NumberTheory.DirichletL.Descent.ReopenedBins
import OAI.NumberTheory.DirichletL.Descent.FirstDyadicFullEnergy

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation FourierBridge CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

theorem long_frequency_profile
    {ι:Type*}(p:ι→O)(hp:∀i,p i≠0)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)
    (Z r ξ:ℝ)(hZ:0<Z)(T:Finset ι) :
    frequencyTwist V ξ (columnLog p (Z^r) T)=
      normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
        (primeProductNorm p T/Z^r) := by
  rw [normTwistedSource,radialFromLog_column p hp V (V.smooth ⊤) A hV _ (Real.rpow_pos_of_pos hZ r)]
  simp only [frequencyTwist_apply,columnLog]

theorem long_marked_source_eq
    {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(β:(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m f z:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)(Z r ξ:ℝ)(hZ:0<Z) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (T∪v.support)*
        frequencyTwist V ξ (columnLog p (Z^r) T)) z =
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (v.support∪T)*
        normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
          (primeProductNorm p T/Z^r)) z := by
  congr 1
  funext v T
  rw [long_frequency_profile p hp V A hV Z r ξ hZ T,Finset.union_comm T v.support]

theorem marked_long_filter
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights=
      markedReopenedCubeBin S D (progressingCubes S D H₀ Q) Ψ m f z W X H₀ slots lists weights := by
  unfold markedReopenedCubeBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hz:largeCubeCoefficient H₀ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hv,(largeCubeCoefficient_support H₀ _ hh).2⟩)
  simp only [hz,zero_mul]

theorem long_cube_progress
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell:ℝ)(hZ:1<Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-1/Real.log Z≤ell+V := by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨hv,hlower⟩:=Finset.mem_filter.mp hv
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:=Real.log_le_log (Real.rpow_pos_of_pos hz _) (hlower.trans (hupper v hv))
  rw [Real.log_rpow hz,Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz] at he
  have hlog:=Real.log_pos hZ
  have hd: (cutoff-ell-V)*Real.log Z≤1:=by nlinarith
  have hh:cutoff-ell-V≤1/Real.log Z:=(le_div_iff₀ hlog).mpr hd
  linarith

theorem long_cube_progress_with_slack
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell eta:ℝ)(hZ:1<Z)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-eta≤ell+V := by
  have h:=long_cube_progress S D Q Z cutoff V ell hZ hne hupper
  have hh:1/Real.log Z≤eta:=(div_le_iff₀ (Real.log_pos hZ)).mpr (by simpa only [mul_comm] using hlog)
  linarith

theorem short_sum_zero_of_label_large
    (Ψ:O→*ℂ)(W:ℝ→ℂ)(mark:Ideal O→ℂ)(X Z cutoff V:ℝ)
    (hZ:1≤Z)(hV:cutoff≤V) :
    markedShortCompletedSum Ψ W X (Z^(cutoff-V)) mark=0 := by
  have ht:Z^(cutoff-V)≤1:=by
    have he:=Real.rpow_le_rpow_of_exponent_le hZ (show cutoff-V≤0 by linarith)
    simpa only [Real.rpow_zero] using he
  unfold markedShortCompletedSum
  trans ∑' _ : Ideal O,(0:ℂ)
  · apply tsum_congr
    intro I
    by_cases hi:I=0
    · subst I
      simp
    rw [ite_eq_right (not_lt.mpr (ht.trans (norm_at_least_one I hi)))]
  · exact tsum_zero

end SevenEighths.InverseMoment

end

end OAI
