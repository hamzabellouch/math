import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceBounds
import OAI.Analysis.LipschitzHilbert.Packets.VariationPacketL1
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement

namespace OAI

/-! Reference moments with distinct analyzing and synthesizing profiles.
The selector is frozen only in the analyzing coefficient; it is not
multiplied into the synthesis a second time. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def mixedReferenceLine (y : ℝ) : LinePacketFamily N κ ι :=
  let A := (P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y
  let S := (P.withProfile alt hAlt).referenceAnalyzedLine d v hv g hg hg1 y
  { S with coeff := A.coeff, coeff_norm := A.coeff_norm }

@[simp] theorem mixedReferenceLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  (P.frozenProfile c hc).referenceAnalyzedLine_coeff d v hv g hg hg1 y j u

@[simp] theorem mixedReferenceLine_wave (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).wave j u k x =
      (P.withProfile alt hAlt).raw 0 j u k y (P.topLength*x) := rfl

theorem mixedReferenceLine_budget_iff (y B : ℝ) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).HasLocalBudget B ↔
      ((P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y).HasLocalBudget B :=
  Iff.rfl

/-- The actual mixed synthesis band, with the original integral
coefficient and no repeated frozen selector in the synthesis profile. -/
def mixedReferenceBand (j : Fin N) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ u : ι j,
    (P.frozenProfile c hc).family.mainCoefficient d v g j u k *
      (P.withProfile alt hAlt).raw 0 j u k y x)

theorem mixedReferenceLine_partial (y x : ℝ) (n : ℕ) :
    hilbertPartialBandSum (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).packets n x =
      (P.constant*Real.pi^2)⁻¹ • packetPartialSum
        (fun j => P.mixedReferenceBand c hc alt hAlt d v g j y (P.topLength*x)) n := by
  ext k
  simp only [hilbertPartialBandSum,partialBandSum,packetPartialSum,
    LinePacketFamily.packets,packetSynthesis_apply,mixedReferenceBand,
    WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [P.mixedReferenceLine_coeff,P.mixedReferenceLine_wave,PiLp.smul_apply]
    simp only [Complex.real_smul]
    ring
  · simp only [ite_eq_right hj,WithLp.ofLp_zero,Pi.zero_apply,smul_zero]

theorem mixedReferenceBand_variation (y x : ℝ) :
    cubicVariation (packetPartialSum
      (fun j => P.mixedReferenceBand c hc alt hAlt d v g j y (P.topLength*x))) N =
      (P.constant*Real.pi^2)*(P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).variation x := by
  have hD : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have heq : packetPartialSum (fun j =>
      P.mixedReferenceBand c hc alt hAlt d v g j y (P.topLength*x)) =
      fun n => (P.constant*Real.pi^2) •
        hilbertPartialBandSum (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).packets n x := by
    funext n
    rw [P.mixedReferenceLine_partial c hc alt hAlt d v hv g hg hg1 y x n,
      smul_smul,mul_inv_cancel₀ hD.ne',one_smul]
  rw [heq,LinePacketFamily.cubicVariation_smul_nonneg _ N _ hD.le]
  rfl

/-- Independent profile choices share the same normalized coefficient
budget, and both reference moments remain uniform in dimension and scale. -/
theorem mixed_reference_uniform_moments (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1),
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.withProfile alt hAlt).raw 0 j u k y) xi = 0) →
      ∀ (y : ℝ) (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ P.topLength*grid.width) → ∀ p : ℝ, 0 ≤ p →
      let Q := P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y
      (∫⁻ x, (ENNReal.ofReal |Q.squareFunction x|)^p ∂grid.lineMeasure) ≤
        referenceSquareMomentCost (A/Real.pi^4) grid p*grid.lineMeasure univ ∧
      (∫⁻ x, (ENNReal.ofReal |Q.variation x|)^p ∂grid.lineMeasure) ≤
        referenceVariationMomentCost M P.constant (A/Real.pi^4) grid p*grid.lineMeasure univ := by
  obtain ⟨A,hA,hbudget⟩ := referenceAnalyzedLine_uniform_budget hL hlo hhi
  obtain ⟨M,hM,hvariation⟩ := LinePacketFamily.uniform_line_moment_of_supported hL hlo hhi
  refine ⟨A,M,hA,hM,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh hSlow hShigh y grid hb hwidth p hp
  let Q := P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y
  have hB : 0 ≤ A/Real.pi^4 := div_nonneg hA.le (pow_nonneg Real.pi_pos.le _)
  have hQ : Q.HasLocalBudget (A/Real.pi^4) :=
    hbudget N κ ι (P.frozenProfile c hc) d v hv g hg hg1 hd hAlow hAhigh y
  have hlen (j : Fin N) : Q.length j = P.length j/P.topLength := by
    change (P.topLength/P.topLength)/(2:ℝ)^j.val = (P.topLength/(2:ℝ)^j.val)/P.topLength
    ring
  have hwidth' (j : Fin N) (u : ι j) : Q.length j ≤ grid.width := by
    rw [hlen]
    exact (div_le_iff₀ P.topLength_pos).mpr (by simpa only [mul_comm] using hwidth j u)
  obtain ⟨hl,hh⟩ := (P.withProfile alt hAlt).referencePlanarFamily_cutoffs hSlow hShigh
  refine ⟨?_,?_⟩
  · exact Q.squareFunction_moment_of_supported grid hb hwidth' hB hQ hp
  · exact hvariation N κ ι Q (A/Real.pi^4) hB hQ
      (fun j u k xi hxi => hl j u k y xi hxi)
      (fun j u k xi hxi => hh j u k y xi hxi) grid hb hwidth' p hp

end LipschitzHilbert.SourceLatticePacket

end

end OAI
