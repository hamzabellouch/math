import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedRecurrence
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathProduct

namespace OAI

/-! The path-product theorem applied to original packet amplitudes.
The remaining analytic inputs are explicit square sums and propagated
residual bounds; no path-product estimate is assumed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem source_active_packet_prefix_product {Kb : ℕ} {F : Type*} [NormedAddCommGroup F]
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hprecision : ∀ t ∈ tops, 0 ≤ precision t)
    (hweight : ∀ t x, 0 < weight t x) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a α p μ : ℝ)
    (hphase : ∀ k, 0 ≤ (phase k).re) (hrelation : p*μ = α-1)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X)
    (count H : ℕ) (hH : ShiftedBlocks.endpoint tag count ≤ H)
    (marked : ℕ → Prop) (profile : ℕ → F) (c M B V C ε Q Cex : ℝ)
    (hp : 1 ≤ p) (hα : 1 ≤ α) (hαp : α ≤ p) (hc : 0 < c) (hc1 : c ≤ 1)
    (hM : 4 ≤ M) (hμ : (α-1)/p ≤ 1/12)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCex : 0 ≤ Cex) :
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let level := ShiftedBlocks.endpoint tag
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let residual := fun j => g.packetResidual packets (fun q => slope (assigned q)) stop base
      transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let keep := fun j q => assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) (slope top))
    let U := fun j => g.packetResidual (packets.filter (keep j)) (fun q => slope (assigned q))
      stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let W := fun j => g.packetAmplitude (packets.filter fun q => ¬keep j q)
      (fun q => slope (assigned q)) stop base transition (level j) (g.index (level j) (slope top))
    let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
    (∀ j < count, M < n j) →
    (∀ j < count, marked j → c ≤ n j-n (j+1)) →
    (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2 →
    (∀ j < count, n j^((α-1)/p) ≤ Q) →
    finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤ V^3 →
    (∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖W j‖ ≤ ε*(n j-n (j+1))) →
    (∀ e f, e < f → f ≤ count → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f, ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
        C*intervalOscillation profile H (level e) (level f)) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    (∏ j ∈ Finset.range count, g.sourceShiftedPathRatio tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p tag top x j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(α-1)/p)*B+
        (4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(α-1)/p)*V)+
          4*p*ε*(Q*∑ j ∈ (Finset.range count).filter
            (fun j => ¬marked j ∧ n j-n (j+1) < 1), pathDrop n j))+
        Real.log (1+Cex^p*(M+1)^(α-1)))*
      ∏ j ∈ Finset.range count, if marked j then
        g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
          value phase a p μ tag top x j else 1 := by
  dsimp only
  let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
  let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
    packets assigned stop value phase a tag top x
  let level := ShiftedBlocks.endpoint tag
  let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
  let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
  let residual := fun j => g.packetResidual packets (fun q => slope (assigned q)) stop base
    transition (level j) (level (j+1)) (g.index (level j) (slope top))
  let keep := fun j q => assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
    (g.index (level (j+1)) (slope top))
  let U := fun j => g.packetResidual (packets.filter (keep j)) (fun q => slope (assigned q))
    stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
  let W := fun j => g.packetAmplitude (packets.filter fun q => ¬keep j q)
    (fun q => slope (assigned q)) stop base transition (level j) (g.index (level j) (slope top))
  let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
  let den := g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap
    packets assigned stop value phase a α p tag top x
  intro hactive hmarked hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have he (j : ℕ) (hj : j < count) :
      g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) :=
    g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x j
      (ne_of_gt (by have := hactive j hj; linarith))
  have hden (j : ℕ) (hj : j < count) : n j ≤ den j := by
    have h := sourceNodeDenominator_ge_mass
      (g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
      (fun i : g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1))
        (g.index (level j) (slope top)) =>
        g.mass tops slope precision cutoff weight (level (j+1)) i.val x)
      (fun i => g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (level (j+1)) i.val) α p
      (fun i => g.mass_nonnegative tops slope precision cutoff weight
        (fun t z => (hweight t z).le) _ i.val x)
    simpa only [n,den,shiftedPathMass,sourceShiftedPathDenominator,ite_eq_left (he j hj)] using h
  have hrec (j : ℕ) (hj : j < count) (_hm : ¬marked j) (hd : n j-n (j+1) < 1) :
      ‖coeff j‖ ≤ 1 ∧ amp j = coeff j • amp (j+1)+U j+W j :=
    g.source_stopped_unary_recurrence tops slope precision cutoff weight hprecision hweight
      hK gap packets assigned stop value phase a hphase hassigned heligible hKb tag top htop x j
      (by linarith : 1 ≤ M) (hactive j hj) hd
  have hprod := source_path_product_from_propagated_residuals count n amp U W residual coeff den
    marked profile level (ShiftedBlocks.endpoint_strictMono hKb tag) H hH
    (g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision
      (fun t z => (hweight t z).le) hKb tag top htop x)
    hp hα hαp hc hc1 hM hμ hB hV hC hε hCex hactive hden hmarked hsquare hQ hvariation
    (fun j hj _ _ => g.source_shifted_path_denominator_ge_next tops slope precision cutoff weight
      hprecision (fun t z => (hweight t z).le) K gap packets assigned stop value phase a α p
      (by linarith : 0 < p) hKb tag top htop x j (he j hj))
    (fun j hj hm hd => (hrec j hj hm hd).1)
    (fun j hj hm hd => (hrec j hj hm hd).2) hW hU hexstop hexmass hexamp
  have hleft : (∏ j ∈ Finset.range count,
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j) =
      ∏ j ∈ Finset.range count, vertexAmount (n j) (amp j) α p/den j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact g.source_shifted_ratio_eq_amount_div_denominator tops slope precision cutoff weight
      K gap packets assigned stop value phase a α p tag top x j (he j (Finset.mem_range.mp hj))
  have hright : (∏ j ∈ Finset.range count,
      if marked j then vertexAmount (n j) (amp j-residual j) α p/den j else 1) =
      ∏ j ∈ Finset.range count, if marked j then
        g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
          value phase a p μ tag top x j else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    split_ifs with hm
    · exact (g.source_stopped_residual_free_ratio tops slope precision cutoff weight hprecision hweight
        K gap packets assigned stop value phase a α p μ hrelation hassigned heligible hKb tag top htop
        x j (he j (Finset.mem_range.mp hj))).symm
    · rfl
  rw [hleft]
  exact hprod.trans_eq (congrArg (fun z => _*z) hright)

end LipschitzHilbert.AngularGrid

end

end OAI
