import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryPairKernelReplacement
open HistoryPairVariableBSquareErrorSelectedKernel HistoryPairVariableBSquareErrorSelectedSum
open HistoryPairRepresentatives Conclusion Filter
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_originalDecodedBErrorSum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ)
        {spectator : PrimeSource}, C.CrossRoleSeparation spectator →
      (∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) →
      ∀ (refs : ∀p:Pattern (pairedHistoryType seed l),
        (b:Block p → CommonSample C.sources (pairedInternalOrigin seed l)) →
          Option (DecodedSquareReference C (pairedInternalOrigin seed l)
            (pairedHistoryType seed l) p b V outside l))
        (mask : ∀p:Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      ‖originalDecodedBErrorSum C (pairedInternalOrigin seed l) (pairedHistoryType seed l)
        mixed V outside l refs mask‖ ≤
        ((4*k*2^k:ℕ)*Real.exp (-Real.exp ((39/10000:ℝ)*L))) *
          Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_decoded_B_probability_error_eventually d Bs BD Bz (by omega : 0<k),
    selected_optionalDrawActualKernelSum_eventually d Bs BD Bz hk] with L hpoint hkernel
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro mixed V outside spectator hsep hV refs mask hm
  let seed := Template.initial (2*(bulkSize k L/2)) k
  let origin := pairedInternalOrigin seed l
  let τ := pairedHistoryType seed l
  let R := sourceReferences C origin τ V outside l refs
  let K := optionalDrawActualPatternKernel C origin τ mixed V outside l R
  let δ : ℝ := (4*k*2^k:ℕ)*Real.exp (-Real.exp ((39/10000:ℝ)*L))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hK := optionalDrawActualPatternKernel_bounds C hsep origin τ mixed V outside l hV R
  have he : ∀p:Pattern τ,∀b:BlockDraw p (CommonSample C.sources origin),
      ‖optionalDecodedBError C origin τ mixed V outside l refs p b.val‖ ≤
        δ*∏q,K p b.val q := by
    intro p b
    cases hr : refs p b.val with
    | none =>
      simp only [optionalDecodedBError,hr,norm_zero]
      exact mul_nonneg hδ (Finset.prod_nonneg (fun q _ => (hK p b.val q).1))
    | some r =>
      have hpt := hpoint E C hG hGu hcl hcu hb hd l hl V outside
        r.leftDraw r.rightDraw r.leftMass r.rightMass hsep hV r.sample r.sourceSamples
        r.sample_representative r.admissible mixed
      have hp : (∏q,K p b.val q) = ∏q : Representative r.leftDraw.history r.rightDraw.history,
          actualProbability mixed r.leftDraw.history r.rightDraw.history
            r.leftDraw.supported r.rightDraw.supported q
            (prime r.leftDraw.history r.rightDraw.history q) r.sample := by
        simp only [K,R,optionalDrawActualPatternKernel,sourceReferences,hr,Option.map_some,
          DecodedSquareReference.toSourceReference]
        exact r.probability_product_eq mixed
      rw [hp]
      simpa only [optionalDecodedBError,hr,δ] using hpt
  have hsum := original_error_sum_norm_le_biasedKernelSum C.sources origin τ K mask δ
    (fun p b => optionalDecodedBError C origin τ mixed V outside l refs p b.val)
    hδ (fun p b q => (hK p b q).1) (fun p b => (hm p b).1) he
  have hkern := hkernel E C hG hGu hcl hcu hb hd l hl mixed V outside hsep hV R mask hm
  exact hsum.trans (mul_le_mul_of_nonneg_left hkern hδ)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
