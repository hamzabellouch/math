import Mathlib
import OAI.Computability.MaxCut.Encoding.ActualAdviceSampling
import OAI.Computability.MaxCut.Games.StageData

namespace OAI

/-! The actual matrix reduction assembled from the gadget and decoder.
The dimension-uniform shortcode inverse is the sole explicit mathematical
input here. This intermediate theorem is not an unconditional endpoint until
that input is supplied by the independently proved KMS foundation. -/

namespace MaxCutGames.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
    (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) := by
  obtain ⟨rstar, hrstar, hgadget⟩ := Gadget.exists_split_gadget p hp
  obtain ⟨P⟩ := MatrixGapChoice.exists_inverse_parameters hinverse rstar
  obtain ⟨d, g, hstable, hkernel⟩ := hgadget P.s P.s_large
  let en := NoiseEnumeration.ofFintype g
  let T := NoiseTables.Table.ofEnumeration g en
  let gT := T.gadget g.f g.equivariant
  have hstableT : gT.stabilityError ≤ p := by
    exact (NoiseTables.Table.stabilityError_ofEnumeration g en).trans_le hstable
  have hkernelT : ∀ (Q : Type) [AddCommGroup Q] [Module F2 Q]
      (L : Ambient P.s d →ₗ[F2] Q),
      rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding P.s d)).range →
        Integration.SplitGadget.kernelProbability gT L ≤ 7 / 8 := by
    intro Q _ _ L hL
    exact (NoiseTables.Table.kernelProbability_ofEnumeration g en L).trans_le (hkernel Q L hL)
  obtain ⟨m, hm, hlarge, hβ, hβ', htv, hrate⟩ := MatrixGapChoice.exists_cube P d
  refine ⟨{
    k := m ^ 3
    s := P.s
    d := d
    k_pos := Nat.succ_le_iff.mpr (pow_pos hm _)
    s_pos := hrstar.trans P.s_large
    T := T
    f := g.f
    equivariant := g.equivariant
    stability := hstableT
    sound := ?_ }⟩
  intro S hdistinct hopt
  apply address_value_le_of_semantic_acceptance S (m ^ 3) T g.f g.equivariant
  intro labeling
  apply le_of_lt
  by_contra hnot
  have haccept : (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S (m ^ 3) gT labeling :=
    le_of_not_gt hnot
  have hgood := P.advice (m ^ 3) hlarge S d gT labeling
    (fun L hL => hkernelT (ActualHomogeneous.E (m ^ 3)) L hL) haccept
  exact ActualMatrixContradiction.contradiction S labeling P.α
    (ActualGoodRows.goodRowMass rstar P.s P.r) (1 / (m : ℝ) ^ 2)
    P.positive P.trivial_small hβ hβ' hgood htv hrate hdistinct hopt

end
end MaxCutGames.Decoder.MatrixGap

end OAI
