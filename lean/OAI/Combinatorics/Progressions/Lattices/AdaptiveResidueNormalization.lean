import OAI.Combinatorics.Progressions.Estimates.AdaptiveRatioNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
  (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
  (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
  (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
  (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (c : ∀ i, FiniteProbabilityCoupling (primeCoordinateReference (σ := σ) q i)
    (primeCoordinateReference (σ := τ) q i))
  (tree : CoordinateDecisionTree ι (fun i => τ → ZMod (q i)))
  (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
  {Good : Finset ι → (∀ i, τ → ZMod (q i)) → Prop} {d A : ℕ}
  (htree : CoordinateDecisionTree.Valid Good ∅ baseY tree d) (hA : d ≤ A)

include htree hA hneX hneY

theorem adaptive_residue_normalization_close {eta theta : ℝ}
    (hsource : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity loX NX MX aX hneX q (fun _ => 1)) eta A)
    (hsite : ProductMarginalsClose (primeCoordinateReference (σ := τ) q)
      (residuePrimeCoordinateDensity loY NY MY aY hneY q (fun _ => 1)) theta A) :
    |(adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z =>
      residuePrimeCoordinateMassRatio loX NX MX aX q z.val.1.1
        (productSubtypePoint z.val.1.1 z.val.2 baseX) *
      residuePrimeCoordinateMassRatio loY NY MY aY q z.val.1.1 (z.val.1.assignment baseY)) - 1| ≤
      eta + theta + eta * theta := by
  have hA' : (∅ : Finset ι).card + d ≤ A := by simpa only [Finset.card_empty, zero_add] using hA
  have hsize (z) (hz : z ∈ CoordinateDecisionTree.leafSourceAssignments
      (fun i => σ → ZMod (q i)) tree ∅ baseY) : z.1.1.card ≤ A :=
    (htree.leaf_card_le z.1 ((CoordinateDecisionTree.mem_leafSourceAssignments (fun i => σ → ZMod (q i)) tree ∅ baseY z).mp hz)).trans hA'
  apply adaptive_ratio_product_close c tree baseX baseY
    (fun z => residuePrimeCoordinateMassRatio loX NX MX aX q z.1.1
      (productSubtypePoint z.1.1 z.2 baseX))
    (fun z => residuePrimeCoordinateMassRatio loY NY MY aY q z.1.1 (z.1.assignment baseY))
  · intro z hz
    exact residuePrimeCoordinateMassRatio_close_of_marginals loX NX MX aX hneX q hsource
      z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX)
  · intro z hz
    exact residuePrimeCoordinateMassRatio_close_of_marginals loY NY MY aY hneY q hsite
      z.1.1 (hsize z hz) (z.1.assignment baseY)

theorem adaptive_residue_normalization_of_lengths {eta theta : ℝ}
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i, MX.Coprime (q i)) (hcopY : ∀ i, MY.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (modLog dimX dimY accX accY : ℝ) (hmodLog : 0 ≤ modLog)
    (heta : eta ≤ 1) (htheta : theta ≤ 1)
    (haccX : Real.exp (-accX) ≤ eta) (haccY : Real.exp (-accY) ≤ theta)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * A + accX + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) MX (aX k) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * A + accY + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) MY (aY k) : ℝ)) :
    |(adaptiveLeafCouplingWeights c tree baseX baseY).mean (fun z =>
      residuePrimeCoordinateMassRatio loX NX MX aX q z.val.1.1
        (productSubtypePoint z.val.1.1 z.val.2 baseX) *
      residuePrimeCoordinateMassRatio loY NY MY aY q z.val.1.1 (z.val.1.assignment baseY)) - 1| ≤
      eta + theta + eta * theta := by
  have hx := residuePrimeDensity_close_of_lengths loX NX MX aX hneX q hMX hcopX hpair
    A modLog dimX accX eta hmodLog heta haccX hmoduli hdimX hlengthX
  have hy := residuePrimeDensity_close_of_lengths loY NY MY aY hneY q hMY hcopY hpair
    A modLog dimY accY theta hmodLog htheta haccY hmoduli hdimY hlengthY
  exact adaptive_residue_normalization_close loX NX MX aX hneX loY NY MY aY hneY q c
    tree baseX baseY htree hA hx hy

end Erdos3

end

end OAI
