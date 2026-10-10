import OAI.Geometry.NodalSets.Charts.NestedChartBounds
import OAI.Geometry.NodalSets.Waves.WaveCenterJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_spatial_bounds (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y) (k : ℕ) :
    ∃ delta > 0, ∃ C > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t x,
      ‖x-y t.1‖ ≤ delta → x ∈ (b.F t).target ∧
      ContDiffAt ℝ ∞ (b.phase t) x ∧
      (∀ N, ContDiffAt ℝ ∞ (b.amplitude N t) x) ∧
      (∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (b.phase t) x‖ ≤ C) ∧
      (∀ N, 1 ≤ N → ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (b.amplitude N t) x‖ ≤ C) ∧
      ContDiffAt ℝ ∞ ((b.F t).symm : Coord → Coord) x ∧
      ‖fderiv ℝ ((b.F t).symm : Coord → Coord) x‖ ≤ D := by
  have hB := actualFrameConnection_continuous g hg hpos (fun t : T × Fin 3 ↦ y t.1)
    (hy.comp continuous_fst) d.frame d.continuous_frame
  obtain ⟨delta,hd,R,hR,D,hD,hbound⟩ := existing_chart_target_bounds
    (fun t : T × Fin 3 ↦ y t.1) (hy.comp continuous_fst) d.frame d.continuous_frame
    (fun t ↦ actualFrameConnection g (y t.1) (d.frame t)) hB b.F b.chart_eq
    b.sourceRadius b.sourceRadius_pos (fun t ↦ (b.chart_domain t).1) (max k 1)
  obtain ⟨Cp,hCp,hp⟩ := (b.jets.phase_continuous.uniformSmoothBounded univ isCompact_univ R).2 k
  obtain ⟨Ca,hCa,ha⟩ := finiteAmplitude_all_parameter_derivatives b.A
    b.jets.amplitude_continuous J k univ isCompact_univ R
  let C := (k.factorial:ℝ)*(Cp+Ca)*D^k
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨delta,hd,C,hC,D,hD,?_⟩
  intro t x hx
  obtain ⟨hxt,hxn,hxs,hxb⟩ := hbound t x hx
  have hpS : ContDiffAt ℝ ∞ (b.phase t) x := (reval_contDiff _).contDiffAt.comp x hxs
  have haS (N : ℝ) : ContDiffAt ℝ ∞ (b.amplitude N t) x :=
    (finiteAmplitude_contDiff _ _ _).contDiffAt.comp x hxs
  have hcost (i : ℕ) (hi : i ≤ k) : (i.factorial:ℝ)*(Cp+Ca)*D^i ≤ C := by
    have hf : (i.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
    have hp := pow_le_pow_right₀ hD hi
    dsimp [C]
    gcongr
  refine ⟨hxt,hpS,haS,?_,?_,hxs,?_⟩
  · intro i hi
    have hb := chart_comp_derivative_bound (b.F t) (b.chart_domain t).2.2 (reval (b.phi t))
      (reval_contDiff _).contDiffOn x hxt i (Cp+Ca) D
      (fun j hj ↦ (hp t (mem_univ t) _ hxn j (hj.trans hi)).trans (by linarith))
      (fun j hj hji ↦ hxb j hj ((hji.trans hi).trans (le_max_left _ _)))
    exact hb.trans (hcost i hi)
  · intro N hN i hi
    have hb := chart_comp_derivative_bound (b.F t) (b.chart_domain t).2.2
      (finiteAmplitude (fun j ↦ b.A j t) J N) (finiteAmplitude_contDiff _ _ _).contDiffOn
      x hxt i (Cp+Ca) D
      (fun j hj ↦ (ha t (mem_univ t) N hN _ hxn j (hj.trans hi)).trans (by linarith))
      (fun j hj hji ↦ hxb j hj ((hji.trans hi).trans (le_max_left _ _)))
    exact hb.trans (hcost i hi)
  · simpa only [norm_iteratedFDeriv_one,pow_one] using hxb 1 le_rfl (le_max_right _ _)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
