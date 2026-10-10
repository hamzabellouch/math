import OAI.NumberTheory.DirichletL.Descent.ReopenedSeparation

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_separated {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u,|u|≤columnWindowRadius a b→V u=1)
    (B ell X H₀ : ℝ) (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell)
    (hD : b*X≤D)
    (hn : ∀ v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀ v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights =
      ((B*Real.sqrt ell:ℝ):ℂ)⁻¹ * ∫ ξ:ℝ,reopeningCoefficient W a b ha hs hW ξ*
        varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
          (separatedCubeCoefficient β n B ξ) Ψ m f
          (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  have hXp : 0<X := hX ▸ mul_pos (pow_pos hB _) hell
  have hupper : ∀ t,W t≠0→t≤b := fun t ht=>(hs ht).2
  dsimp only
  rw [←varying_canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n (fun v T=>primeMark slots lists weights (T∪v.support))
    Ψ m f z B ell X hB hell hX hn hn']
  unfold markedReopenedCubeBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hXp hupper hD slots lists weights v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hc' : β v*(n v:ℂ)⁻¹=largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  ring

end
end SevenEighths.InverseMoment

end OAI
