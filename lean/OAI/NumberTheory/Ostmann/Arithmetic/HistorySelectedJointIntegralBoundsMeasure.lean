import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Filter Construction PrimeCellFreezing HistoryPrincipalIntegralAverage
open HistoryGiantPriorGrid HistoryBulkPriorGrid HistoryPrincipalIntegralBounds

theorem exists_joint_integral_thresholds :
    ∃ L₀ G₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ G : ℝ, G₀ ≤ G →
      ∀ Ebulk Egiant : Finset ℕ, Ebulk.card ≤ 2 → Egiant.card ≤ 2 →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ {A : ℝ}, 0 ≤ A →
      (∀ f : (Bool → ℝ) → (ι → ℝ) → ℂ,
        (∀ t ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
          ∀ s ∈ logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
            ‖f (fun i => Real.exp (t i)) (fun i => Real.exp (s i))‖ ≤ A) →
        ‖primeIntegral (fun _ : Bool => G-1) (fun _ => G+1)
          (fun _ => logCellMass G Egiant)
          (primeCutoff G (fun u => primeIntegral
            (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
            (fun _ => bulkNormalizer L Ebulk) (f u)))‖ ≤
          64*2^Fintype.card ι*A) ∧
      (∀ f : (Option Unit → ℝ) → (ι → ℝ) → ℂ,
        (∀ t ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
          ∀ s ∈ logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
            ‖f (fun i => Real.exp (t i)) (fun i => Real.exp (s i))‖ ≤ A) →
        ‖mixedIntegral (G-1) (G+1) G smoothPartition
          (fun _ : Unit => G-1) (fun _ => G+1) (fun _ => logCellMass G Egiant)
          (mixedGiantPrimeTest G (fun u => primeIntegral
            (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
            (fun _ => bulkNormalizer L Ebulk) (f u)))‖ ≤
          64*2^Fintype.card ι*A) := by
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp eventually_norm_bulk_primeIntegral_le
  obtain ⟨G₀,hG₀⟩ := eventually_atTop.mp eventually_norm_giant_integrals_le
  refine ⟨L₀,G₀,?_⟩
  intro L hL G hG Ebulk Egiant hEbulk hEgiant ι _ _ A hA
  have hbulk := hL₀ L hL ι Ebulk hEbulk (A:=A) hA
  have hgiant := hG₀ G hG Egiant hEgiant
  have hmass : 0 ≤ (2:ℝ)^Fintype.card ι*A := mul_nonneg (by positivity) hA
  constructor
  · intro f hf
    have hh := hgiant.2.1 hmass
      (fun u => primeIntegral (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L Ebulk) (f u))
      (fun t ht => hbulk (f (fun i => Real.exp (t i))) (hf t ht))
    simpa only [mul_assoc] using hh
  · intro f hf
    have hh := hgiant.2.2 hmass
      (fun u => primeIntegral (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
        (fun _ => bulkNormalizer L Ebulk) (f u))
      (fun t ht => hbulk (f (fun i => Real.exp (t i))) (hf t ht))
    have h64 : 16*Real.exp 1 ≤ (64:ℝ) := by linarith [Real.exp_one_lt_three]
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h64 hmass)

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
