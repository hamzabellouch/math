import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorReplacementMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiPriorReplacement
open Construction SourcePriorGridDeletion HistorySignedResidues
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryGiantPriorGrid
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open Characters.RationalHistory
open scoped BigOperators

theorem exists_corrected_sourceMixedMean_replacement_constants :
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
      (hd : pairModulus h k outside ∣ M), (M : ℝ) < Real.exp (G-1) →
    ∀ (ηI : ℝ) (η : Unit → ℝ), 0 ≤ G → L₀ ≤ G-1 → 0 < ηI →
      (∀ i, 0 < η i ∧ η i ≤ 1) → (M : ℝ) ≤ Real.exp (δ*(G-1)^(1/3 : ℝ)) →
    ∀ ε B error mesh : ℝ, 0 ≤ ε → 1 ≤ B → 0 ≤ error → 0 ≤ mesh →
      ηI ≤ mesh → (∀ i, η i ≤ mesh) →
      (∀ (j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η) i,
        (K/logCellMass G E)*Real.exp (-δ*(boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)^(1/3 : ℝ))+
          (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i))⁻¹ ≤ ε) →
      (∀ (j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η) i,
        |harmonicIntegral M (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)
          (boxUpper (fun _ => G-1) (fun _ => G+1) η j.2 i)/logCellMass G E|+
          ((K/logCellMass G E)*Real.exp (-δ*(boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i)^(1/3 : ℝ))+
            (logCellMass G E*Real.exp (boxLower (fun _ => G-1) (fun _ => G+1) η j.2 i))⁻¹) ≤ B) →
      (∀ j : MixedGridIndex (G-1) (G+1) ηI (fun _ : Unit => G-1) (fun _ => G+1) η,
        mixedGridError (ι := Unit) M (G-1) (G+1) ηI G 1 partitionDerivativeConstant
          smoothPartition ε B j.1 ≤ error) →
      let f := reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
        Finset.univ cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)
      let D := correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length
        (Fintype.card (τ ⊕ Fin ([true] : List Bool).length)) h k V b k₀ tb Δ E₀ center
      let A := Real.exp (WH+Wu)*Real.exp (-((2^l : ℕ) : ℝ)*Δ+sourceXiConstant l k₀ E₀)
      ‖sourceMixedMean (residueTransform d) V outside h k G E hZ M hd f -
        mixedPrincipalIntegral M (G-1) (G+1) G smoothPartition
          (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G E)
          (mixedGiantPrimeTest G f) *
          ∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ,
            mixedResidueTest (residueTransform d) V outside h k M hd r u‖ ≤
      (Real.exp 1+1)*deletionCap G E*((outside.prod : ℝ)^(2^(l+1))*A) +
        (2*(2*D*mesh)*mixedPrincipalMass M (G-1) (G+1) G smoothPartition
          (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G E) +
          (2*D*mesh+A)*(Fintype.card (MixedGridIndex (G-1) (G+1) ηI
            (fun _ : Unit => G-1) (fun _ => G+1) η)*error)) *
          ∑ r : ZMod M, ∑ u : Unit → (ZMod M)ˣ,
            ‖mixedResidueTest (residueTransform d) V outside h k M hd r u‖ := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_sourceMixedMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro d b s k₀ X tb td G Δ E₀ center outside hX houtprime hout l V h k hs ks
    hlk hl₁ hl₂ τ _ T U WH Wu Hkeys Ukeys cellCenter cellKey hsrc₁ hsrc₂ hcorr hcenter
    E hZ M _ hd hsize ηI η hG hlo hηI hη hM ε B error mesh hε hB herr0 hmesh hwidthI hwidth
    herror hmass herr
  have houtpos : ∀ q ∈ outside, 0 < q := fun q hq => (houtprime q hq).pos
  have helo : (Option.elim' (G-1) (fun _ : Unit => G-1)) = (fun _ => G-1) := by
    funext i
    cases i <;> rfl
  have hehi : (Option.elim' (G+1) (fun _ : Unit => G+1)) = (fun _ => G+1) := by
    funext i
    cases i <;> rfl
  have hb := corrected_rectangle_bounds b s k₀ X tb td G Δ E₀ center hX houtpos hout h k hs ks
    hlk hl₁ hl₂ T U WH Wu Hkeys Ukeys Finset.univ cellCenter cellKey
    (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)
    (fun _ => G-1) (fun _ => G+1) hsrc₁ hsrc₂ hcorr hcenter
  have hb' := corrected_rectangle_bounds b s k₀ X tb td G Δ E₀ center hX houtpos hout h k hs ks
    hlk hl₁ hl₂ T U WH Wu Hkeys Ukeys
    (Finset.univ : Finset (τ ⊕ Fin ([true] : List Bool).length))
    (priorCellCenter cellCenter G [true]) (priorCellKey h k cellKey [true])
    (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)
    (fun _ => G-1) (fun _ => G+1) hsrc₁ hsrc₂ hcorr hcenter
  let fcut := reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
    (Finset.univ : Finset (τ ⊕ Fin ([true] : List Bool).length))
    (priorCellCenter cellCenter G [true]) (priorCellKey h k cellKey [true])
    (giantCoordinates h k) (pairBackground h k) (optionEquiv h k)
  have hcut := mixedCutoff_corrected b s X tb td G h k hs ks T U Hkeys Ukeys cellCenter cellKey
  apply hreplace l (residueTransform d) V outside h k G E hZ M hd hsize ηI η hG hlo hηI hη hM
    ε B error hε hB herr0 herror hmass herr _ _ mesh _ _
    (correctedPairDerivativeBound_nonneg WH Wu Hkeys.length Ukeys.length _ h k V b k₀ tb Δ E₀ center)
    hmesh (by positivity) hwidthI hwidth
  · intro z hz
    have he : (fun y : Option Unit → ℝ => mixedGiantPrimeTest G
        (reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys Finset.univ
          cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (optionEquiv h k))
        (fun i => Real.exp (y i))) = (fun y => fcut (fun i => Real.exp (y i))) := by
      funext y
      exact hcut _ (Real.exp_pos _)
    rw [he]
    exact hb'.1.differentiable (by simp) z
  · intro z hz i
    have he : (fun t => mixedGiantPrimeTest G
        (reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys Finset.univ
          cellCenter cellKey (giantCoordinates h k) (pairBackground h k) (optionEquiv h k))
        (Expr.logCurve (fun q => Real.exp (z q)) i t)) =
        (fun t => fcut (Expr.logCurve (fun q => Real.exp (z q)) i t)) := by
      funext t
      apply hcut
      unfold Expr.logCurve
      split_ifs <;> positivity
    rw [he]
    simpa only [Finset.card_univ] using hb'.2.1 z (by simpa only [helo, hehi] using hz) i
  · intro z hz
    rw [hcut _ (Real.exp_pos _)]
    exact hb'.2.2 z (by simpa only [helo, hehi] using hz)
  · apply mixed_sample_bound d V outside h k M hd houtprime G
    simpa only [helo, hehi] using hb.2.2

end Ostmann.Arithmetic.HistoryGiantXiPriorReplacement

end

end OAI
