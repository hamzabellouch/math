import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessScales
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailPotential

namespace OAI

open Filter
open scoped Topology

namespace Balanced.Selection.Process

noncomputable section
universe u v w

def UniformSuccessEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      1 - ε q ≤ successMass (outputLaw p q G hG.2.1)

def UniformOccupancyEstimate (p : Parameters) (ε : ℕ → ℝ) (q : ℕ) : Prop :=
  ∀ (I : Type u) (V : Type v) [Fintype I] [Fintype V],
    ∀ G : Input I V, ∀ hG : GraphBounds G q p.c p.C,
      ∀ (P D L : Type w) [Fintype P] [Fintype D] [Fintype L],
        ∀ (A : FiniteAffine.Plane q P D L) (index : I ≃ (D × Bool)) (line : V → L),
          LineAssignment G A index line →
          ∀ T : L → Finset P, TrackedSets A T p.c₀ →
            occupancyFailureMass (outputLaw p q G hG.2.1) A line T p.rho ≤ ε q

theorem UniformSuccessEstimate.mono {p : Parameters} {ε δ : ℕ → ℝ} {q : ℕ}
    (h : UniformSuccessEstimate.{u,v} p ε q) (hle : ε q ≤ δ q) :
    UniformSuccessEstimate.{u,v} p δ q := by
  intro I V _ _ G hG
  exact (sub_le_sub_left hle 1).trans (h I V G hG)

theorem UniformOccupancyEstimate.mono {p : Parameters} {ε δ : ℕ → ℝ} {q : ℕ}
    (h : UniformOccupancyEstimate.{u,v,w} p ε q) (hle : ε q ≤ δ q) :
    UniformOccupancyEstimate.{u,v,w} p δ q := by
  intro I V _ _ G hG P D L _ _ _ A index line hline T hT
  exact (h I V G hG P D L A index line hline T hT).trans hle

theorem combined_error_tendsto_zero {ε δ : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun q => |ε q| + |δ q|) atTop (𝓝 0) := by
  simpa only [abs_zero, zero_add] using hε.abs.add hδ.abs

theorem selectionStatement_of_uniform_output_bounds
    (hsuccess : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformSuccessEstimate.{u,v} p ε q)
    (hoccupancy : ∀ p : Parameters, p.Admissible →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ q : ℕ in atTop, UniformOccupancyEstimate.{u,v,w} p ε q) :
    SelectionStatement.{u,v,w} := by
  intro c C c₀ hc hC hc₀ hc₀le
  obtain ⟨p, hpc, hpC, hpc₀, hp⟩ :=
    Parameters.exists_admissible c C c₀ hc hC hc₀ hc₀le
  obtain ⟨ε, hε, hsuccess⟩ := hsuccess p hp
  obtain ⟨δ, hδ, hoccupancy⟩ := hoccupancy p hp
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp
    ((hsuccess.and hoccupancy).and (Parameters.eventually_scale_regime p))
  refine ⟨cylinderConstant p, p.rho, (fun q => |ε q| + |δ q|), q₀,
    cylinderConstant_pos p, Parameters.rho_pos hp,
    (fun q => add_nonneg (abs_nonneg _) (abs_nonneg _)),
    combined_error_tendsto_zero hε hδ, ?_⟩
  intro q hq I V _ _ G hG
  have hG' : GraphBounds G q p.c p.C := by
    simpa only [hpc, hpC] using hG
  have hb := hq₀ q hq
  have hεle : ε q ≤ |ε q| + |δ q| :=
    (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hδle : δ q ≤ |ε q| + |δ q| :=
    (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨outputLaw p q G hG'.2.1, ?_, ?_, ?_⟩
  · exact (sub_le_sub_left hεle 1).trans (hb.1.1 I V G hG')
  · intro J prescribed
    exact cylinderMass_outputLaw_source_bound p q G hp hb.2.1 hb.2.2 hG' J prescribed
  · intro P D L _ _ _ A index line hline T hT
    have hT' : TrackedSets A T p.c₀ := by simpa only [hpc₀] using hT
    exact (hb.1.2 I V G hG' P D L A index line hline T hT').trans hδle

end
end Balanced.Selection.Process

end OAI
