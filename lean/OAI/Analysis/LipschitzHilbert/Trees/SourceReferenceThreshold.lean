import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceTailOrder

namespace OAI

/-! Fixed binary reference grids give polynomial thresholds with arbitrarily
strong exponential tails. The angular grid branching never enters this bound. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLatticePacket

/-- The reference variation constant grows at most linearly with the
packet envelope constant. All other parameters precede the packet family. -/
theorem binary_lineMomentBase_le (M B C : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hC : 0 ≤ C) :
    lineMomentBase C (M*C^2*B+1) 2 ≤
      lineMomentBase 1 (M*B+1) 2*(C+1) := by
  let t := C+1
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have hCt : C ≤ t := by dsimp [t]; linarith
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hsq : C^2 ≤ t^2 := pow_le_pow_left₀ hC hCt 2
  have hone : (1:ℝ) ≤ t^2 := one_le_pow₀ ht
  have hD : M*C^2*B+1 ≤ (M*B+1)*t^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hMB]
  have hsqrt : Real.sqrt (M*C^2*B+1) ≤ Real.sqrt (M*B+1)*t := by
    apply (Real.sqrt_le_sqrt hD).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  calc
    _ ≤ 16*((4*(2*(Real.sqrt (M*B+1)*t)+4*(t*(4*Real.pi)^2)))/
        Real.log (3/2)+Real.sqrt (M*B+1)*t+t) := by
      unfold lineMomentBase
      norm_num only
      gcongr
    _ = _ := by dsimp [lineMomentBase,t]; ring

/-- One natural moment order works for every reference packet family,
line position, and binary grid. Its threshold is a fixed power of L. -/
theorem eventually_reference_thresholds (M B a J : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (ha : 0 ≤ a) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧
      (1/4:ℝ)^n ≤ Real.exp (-J*L) ∧ 1 ≤ L^(a+4) ∧
      ∀ (grid : FiniteLineGrid) (C : ℝ), grid.branching = 2 →
        0 ≤ C → C ≤ L^a →
        4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ L^(a+4) ∧
        4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ L^(a+4) := by
  let S := 16*((4*(2*LinePacketFamily.squareMeanConstant B+48*(4*Real.pi)^4))/
    Real.log (3/2)+LinePacketFamily.squareMeanConstant B+1)
  let V := lineMomentBase 1 (M*B+1) 2
  let K := max S V
  have hV : 0 < V := lineMomentBase_pos _ _ _ (by norm_num) (by norm_num)
  have hK : 0 < K := lt_of_lt_of_le hV (le_max_right _ _)
  filter_upwards [eventually_source_reference_tail_order J hJ,
    eventually_ge_atTop (max 2 (2*K))] with L hn hlarge
  obtain ⟨n,hn,hnL,hdecay⟩ := hn
  have hL : 1 ≤ L := le_trans (by norm_num : (1:ℝ) ≤ 2)
    ((le_max_left _ _).trans hlarge)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKL : 2*K ≤ L := (le_max_right _ _).trans hlarge
  have hLa : 1 ≤ L^a := Real.one_le_rpow hL ha
  refine ⟨n,hn,hdecay,Real.one_le_rpow hL (by linarith),?_⟩
  intro grid C hb hC hCL
  have hbase : referenceSquareMomentBase B grid = S := by
    unfold referenceSquareMomentBase
    rw [hb]
    norm_num only [Nat.cast_ofNat]
    rfl
  have hCb : C+1 ≤ 2*L^a := by linarith
  have hfactor : K*(C+1) ≤ L^a*L := by
    calc
      _ ≤ K*(2*L^a) := mul_le_mul_of_nonneg_left hCb hK.le
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hKL (Real.rpow_nonneg hL0.le a)]
  have hpoly : (L^a*L)*L^2 ≤ L^(a+4) := by
    calc
      _ = L^(a+3) := by
        rw [Real.rpow_add hL0]
        rw [show L^(3:ℝ) = L^(3:ℕ) from Real.rpow_natCast L 3]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hbound (b : ℝ) (hb : b ≤ K*(C+1)) : 4*(b*(n:ℝ)) ≤ L^(a+4) := by
    calc
      _ = b*(4*(n:ℝ)) := by ring
      _ ≤ (K*(C+1))*(4*(n:ℝ)) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (L^a*L)*L^2 := mul_le_mul hfactor hnL (by positivity) (by positivity)
      _ ≤ _ := hpoly
  constructor
  · apply hbound
    rw [hbase]
    exact (le_max_left S V).trans (by nlinarith)
  · apply hbound
    rw [hb]
    norm_num only [Nat.cast_ofNat]
    exact (binary_lineMomentBase_le M B C hM hB hC).trans
      (mul_le_mul_of_nonneg_right (le_max_right S V) (by linarith))

/-- The moment hypotheses are the exact previously proved reference moment
bounds; no concentration or path estimate is assumed. -/
theorem reference_polynomial_tails_of_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F V : X → ℝ) (hF : Measurable F) (hV : Measurable V)
    (M B C T : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (n : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hs : 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ T)
    (hv : 4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ T)
    (hsm : (∫⁻ x, (ENNReal.ofReal |F x|)^(2*(n:ℝ)) ∂μ) ≤
      referenceSquareMomentCost B grid (2*(n:ℝ))*μ univ)
    (hvm : (∫⁻ x, (ENNReal.ofReal |V x|)^(n:ℝ) ∂μ) ≤
      referenceVariationMomentCost M C B grid n*μ univ) :
    μ {x | T ≤ |F x|} ≤ (1/4:ℝ≥0∞)^n*μ univ ∧
      μ {x | T ≤ |V x|} ≤ (1/4:ℝ≥0∞)^n*μ univ := by
  constructor
  · apply (measure_mono (show {x | T ≤ |F x|} ⊆
        {x | 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ (F x)^2} from ?_)).trans
      (reference_square_tail μ F hF B grid hB n hn hsm)
    intro x hx
    have h1 : 1 ≤ |F x| := hT.trans hx
    have : |F x| ≤ (F x)^2 := by nlinarith [sq_abs (F x)]
    exact hs.trans (hx.trans this)
  · exact (measure_mono (fun x hx => hv.trans hx)).trans
      (reference_variation_tail μ V hV M C B grid hC n hn hvm)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
