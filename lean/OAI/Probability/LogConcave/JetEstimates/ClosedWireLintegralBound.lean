import Mathlib
import OAI.Probability.LogConcave.JetEstimates.WireStep
import OAI.Probability.LogConcave.TensorGraphs.Vertex

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open MeasureTheory
open scoped ENNReal NNReal

theorem closed_wire_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D I O S : ℕ → Type*} [∀k,Fintype (D k)] [∀k,Fintype (I k)]
    [∀k,Fintype (O k)] [∀k,Fintype (S k)] [∀k,DecidableEq (S k)]
    [DecidableEq (D 0)]
    (A : ∀k,Ω → O k → I k → ℝ) (C : ℕ → Ω → ℝ) (M : ℕ → ℝ≥0∞)
    (hC : ∀k x,0≤C k x) (hA : ∀k x,Bound (A k x) ((C k x)^2))
    (ei : ∀k,D k ≃ I k×S k) (eo : ∀k,D (k+1) ≃ O k×S k)
    (n : ℕ) (hn : 0<n) (close : D 0 ≃ D n)
    (hm : ∀k<n,AEMeasurable (fun x => ENNReal.ofReal (C k x)) μ)
    (hb : ∀k<n,(∫⁻x,(ENNReal.ofReal (C k x))^n ∂μ)≤(M k)^n) :
    (∫⁻x,ENNReal.ofReal |∑i,circuit (fun k => wireStep (A k x) (ei k) (eo k)) n (close i) i| ∂μ)≤
      (Fintype.card (D 0):ℝ≥0∞)*(∏k∈Finset.range n,M k) := by
  have hp (x : Ω) :
      ENNReal.ofReal |∑i,circuit (fun k => wireStep (A k x) (ei k) (eo k)) n (close i) i|≤
        (Fintype.card (D 0):ℝ≥0∞)*(∏k∈Finset.range n,ENNReal.ofReal (C k x)) := by
    have hh := ENNReal.ofReal_le_ofReal (closed_wire_circuit_bound (fun k => A k x)
      (fun k => C k x) (fun k => hC k x) (fun k => hA k x) ei eo n close)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
      ENNReal.ofReal_prod_of_nonneg (fun k _ => hC k x)] at hh
    exact hh
  calc
    _ ≤ ∫⁻x,(Fintype.card (D 0):ℝ≥0∞)*(∏k∈Finset.range n,ENNReal.ofReal (C k x)) ∂μ :=
      lintegral_mono hp
    _ = (Fintype.card (D 0):ℝ≥0∞)*(∫⁻x,∏k∈Finset.range n,ENNReal.ofReal (C k x) ∂μ) := by
      exact lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply NetworkMoments.lintegral_prod_le (Finset.range n) ⟨0,Finset.mem_range.mpr hn⟩
      · exact fun k hk => hm k (Finset.mem_range.mp hk)
      · simpa only [Finset.card_range] using fun k hk => hb k (Finset.mem_range.mp hk)
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
