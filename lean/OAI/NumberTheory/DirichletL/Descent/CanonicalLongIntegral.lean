import OAI.NumberTheory.DirichletL.Descent.CanonicalLongFull

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem actual_long_bin_normalized_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Z r cubeLength Vheight H₀ K E : ℝ) (d : ℕ)
    (hZ : 0 < Z) (hD : b*(Z^(r+3*cubeLength))≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, (Z^cubeLength) ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*(Z^cubeLength))
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, Z^(-r-2*cubeLength-Vheight)*rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    Z^(-Vheight)*rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W (Z^(r+3*cubeLength)) H₀ slots lists weights) K ≤
      E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β:=fun I v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hcancel:Z^(r+2*cubeLength+Vheight)*Z^(-r-2*cubeLength-Vheight)=1 := by
    rw [←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hpoint:∀ξ:ℝ,rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ)
        Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K≤
      (Z^(r+2*cubeLength+Vheight)*E)*(1+|ξ|)^(2*d) := by
    intro ξ
    have hh:=mul_le_mul_of_nonneg_left (hsource ξ) (Real.rpow_nonneg hZ.le (r+2*cubeLength+Vheight))
    rw [←mul_assoc,hcancel,one_mul] at hh
    simpa only [mul_assoc] using hh
  have hX:Z^(r+3*cubeLength)=(Z^cubeLength)^3*Z^r := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  have hbnd:=markedReopenedCubeBin_energy S D hbad hSp Q labels Ψ m W a b ha hb hs hW V hV
    (Z^cubeLength) (Z^r) (Z^(r+3*cubeLength)) H₀ K (Z^(r+2*cubeLength+Vheight)*E) d
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hX hD hK (by positivity)
    hn hn' slots lists weights hpoint
  have hc:Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight)=1 := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ,←Real.rpow_neg hZ.le,
      ←Real.rpow_add hZ,←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hh:=mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hZ.le (-Vheight))
  apply hh.trans_eq
  calc
    _=(Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight))*
      E*(∫ξ:ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by ring
    _=_:=by rw [hc,one_mul]

end
end SevenEighths.InverseMoment

end OAI
