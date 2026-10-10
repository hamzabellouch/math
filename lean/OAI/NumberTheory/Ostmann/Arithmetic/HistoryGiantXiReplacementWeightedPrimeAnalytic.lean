import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open HistoryGiantXiPriorReplacement HistoryGiantWeightedPriorReplacement
open Construction SourcePriorGridDeletion HistorySignedResidues
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryGiantPriorGrid
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators

theorem exists_weighted_corrected_sourcePrimeMean_replacement_constants :
    ∃ δ K L₀ : ℝ, 0 < δ ∧ 0 < K ∧ 1 ≤ L₀ ∧
    ∀ (d : Decomposition) (b s k₀ : ℕ) (X tb td G Δ E₀ : ℝ)
      (center : ℕ → ℝ) (outside : List ℕ),
      0 < X → (∀ q ∈ outside, q.Prime) → outside.length = 2*s →
    ∀ (l : ℕ) (V : ℕ → ℕ) (h k : History l)
      (hs : h.Supported V outside) (ks : k.Supported V outside),
      l ≤ k₀ → TreeSourceLabels (Template.initial (2*b) k₀) h →
      TreeSourceLabels (Template.initial (2*b) k₀) k →
    ∀ (τ : Type) [Fintype τ] (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
      (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k),
      SourceBounds b k₀ G center h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => G-1) (fun _ => G+1) →
      SourceBounds b k₀ G center k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => G-1) (fun _ => G+1) →
      CounterpartBounds T U WH Wu Hkeys Ukeys (giantCoordinates h k) (pairBackground h k)
        (fun _ => G-1) (fun _ => G+1) →
      Real.log X+Δ-E₀ ≤ 2*G+2*tb+2*td+
        (∑ a,∑ i,topCenters b center a i)+
        (∑ a,∑ j : Fin k₀,∑ i,compensationCenters b center a j i) →
    ∀ (E : Finset ℕ) (hZ : 0 < logCellMass G E) (M : ℕ) [NeZero M]
      (hd : pairModulus h k outside ∣ M)
      (W : ZMod M × ZMod M → ℂ) (BW : ℝ), 0 ≤ BW → (∀ z, ‖W z‖ ≤ BW) → (M : ℝ) < Real.exp (G-1) →
    ∀ (η : Bool → ℝ), L₀ ≤ G-1 → (∀ i, 0 < η i ∧ η i ≤ 1) →
      (M : ℝ) ≤ Real.exp (δ*(G-1)^(1/3 : ℝ)) →
    ∀ ε B mesh : ℝ, 0 ≤ ε → 1 ≤ B → 0 ≤ mesh → (∀ i, η i ≤ mesh) →
      (∀ (j : GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η) i,
        (K/logCellMass G E)*Real.exp (-δ*(boxLower (fun _ => G-1) (fun _ => G+1) η j i)^(1/3 : ℝ))+
          (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j i))⁻¹ ≤ ε) →
      (∀ (j : GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η) i,
        |harmonicIntegral M (boxLower (fun _ => G-1) (fun _ => G+1) η j i)
          (boxUpper (fun _ => G-1) (fun _ => G+1) η j i)/logCellMass G E|+
          ((K/logCellMass G E)*Real.exp (-δ*(boxLower (fun _ => G-1) (fun _ => G+1) η j i)^(1/3 : ℝ))+
            (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j i))⁻¹) ≤ B) →
      let f := reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
        Finset.univ cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)
      let D := correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length
        (Fintype.card (τ ⊕ Fin ([false,true] : List Bool).length)) h k V b k₀ tb Δ E₀ center
      let A := Real.exp (WH+Wu)*Real.exp (-((2^l : ℕ) : ℝ)*Δ+sourceXiConstant l k₀ E₀)
      ‖periodicSourcePrimeMean G E hZ M
        (weightedResidueTest (residueTransform d) V outside h k M hd W) f -
        principalIntegral M (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => logCellMass G E) (primeCutoff G f) *
          ∑ u : Bool → (ZMod M)ˣ, primeTest (weightedResidueTest (residueTransform d) V outside h k M hd W) u‖ ≤
      deletionCap G E*(1+fullMassRatio G E)*(BW*((outside.prod : ℝ)^(2^(l+1))*A)) +
        (2*(2*D*mesh)*principalMass M (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => logCellMass G E) +
          (2*D*mesh+A)*(Fintype.card (GridBoxIndex (fun _ : Bool => G-1) (fun _ => G+1) η)*
            (2*ε*B^2))) *
          ∑ u : Bool → (ZMod M)ˣ, ‖primeTest (weightedResidueTest (residueTransform d) V outside h k M hd W) u‖ := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_periodicSourcePrimeMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro d b s k₀ X tb td G Δ E₀ center outside hX houtprime hout l V h k hs ks
    hlk hl₁ hl₂ τ _ T U WH Wu Hkeys Ukeys cellCenter cellKey hsrc₁ hsrc₂ hcorr hcenter
    E hZ M _ hd W BW hBW hW hsize η hlo hη hM ε B mesh hε hB hmesh hwidth herror hmass
  have houtpos : ∀ q ∈ outside, 0 < q := fun q hq => (houtprime q hq).pos
  have hb := corrected_rectangle_bounds b s k₀ X tb td G Δ E₀ center hX houtpos hout h k hs ks
    hlk hl₁ hl₂ T U WH Wu Hkeys Ukeys Finset.univ cellCenter cellKey
    (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)
    (fun _ => G-1) (fun _ => G+1) hsrc₁ hsrc₂ hcorr hcenter
  have hb' := corrected_rectangle_bounds b s k₀ X tb td G Δ E₀ center hX houtpos hout h k hs ks
    hlk hl₁ hl₂ T U WH Wu Hkeys Ukeys
    (Finset.univ : Finset (τ ⊕ Fin ([false,true] : List Bool).length))
    (priorCellCenter cellCenter G [false,true]) (priorCellKey h k cellKey [false,true])
    (giantCoordinates h k) (pairBackground h k) (boolEquiv h k)
    (fun _ => G-1) (fun _ => G+1) hsrc₁ hsrc₂ hcorr hcenter
  rw [← primeCutoff_corrected b s X tb td G h k hs ks T U Hkeys Ukeys cellCenter cellKey] at hb'
  apply hreplace G E hZ M (weightedResidueTest (residueTransform d) V outside h k M hd W) hsize η hlo hη hM
    ε B hε hB herror hmass _ _ mesh _ _
    (correctedPairDerivativeBound_nonneg WH Wu Hkeys.length Ukeys.length _ h k V b k₀ tb Δ E₀ center)
    hmesh (by positivity) hwidth
  · intro z hz
    exact hb'.1.differentiable (by simp) z
  · intro z hz i
    simpa only [Finset.card_univ] using hb'.2.1 z hz i
  · exact hb'.2.2
  · exact weighted_prime_sample_bound d V outside h k M hd houtprime W BW hBW hW G _ _ hb.2.2

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
