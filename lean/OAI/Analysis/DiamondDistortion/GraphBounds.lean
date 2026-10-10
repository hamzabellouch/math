import OAI.Analysis.DiamondDistortion.StartBounds

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

/-- Exact positive-rho qualitative result for the complete finite-forest dual. -/
theorem forest_normer_first {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ,0 < ρ ∧ ρ < 1 ∧ Diamond.UnitLensBound ForestDual ε ρ :=
  Diamond.QuadraticLens.positive_gap forest_quadratic_lens hε

theorem forest_qualitative_backward {D : ℝ} (hD : 1 ≤ D) :
    ∃ ρ : ℝ,0 < ρ ∧ ρ < 1 ∧ ∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (s : ℝ),
      Diamond.HasDistortion k f D s → D⁻¹ ≤ ρ^k := by
  have hD0 : 0 < D := by linarith
  have hα : 0 < D⁻¹ := inv_pos.2 hD0
  obtain ⟨ρ,hρ,hρ1,hgap⟩ := forest_normer_first hα
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro k f s hf
  have hn := Diamond.upper_one_normalization f hf
  exact Diamond.backward hα ((inv_le_one₀ hD0).mpr hD) hρ.le hρ1
    (hgap.mono_separation (by linarith)) k (fun v => (D*s)⁻¹ • f v)
    (fun u v => (hn u v).1) (fun u v => (hn u v).2)

/-- The separately stated exact radial constant C_* = sqrt 2 + sqrt 6.
    The proof uses the stronger established bound on the identical norm. -/
theorem forest_radial_deficit {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → ForestDual)
    (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ) ≤ (Real.sqrt 2+Real.sqrt 6)^2*D*(D-1) := by
  have hh := headline.1 k f D s hf
  have hD : 1 ≤ D := hf.1
  have hD0 : 0 ≤ D := by linarith
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h6 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hp := mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6)
  have hC : 8 ≤ (Real.sqrt 2+Real.sqrt 6)^2 := by nlinarith
  have hb : (k:ℝ) ≤ 8*D*(D-1) := by nlinarith [sq_nonneg (D-1)]
  have hm := mul_le_mul_of_nonneg_right hC (mul_nonneg hD0 (by linarith : 0 ≤ D-1))
  nlinarith

namespace Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem Heads.vanishing_lens_pos (A : Heads ι X) (hinput : A.TailVanishing) {ε : ℝ}
    (hε : 0 < ε) : ∃ ρ : ℝ,0 < ρ ∧ ρ < 1 ∧ Diamond.UnitLensBound X ε ρ := by
  obtain ⟨ρ,hρ,hρ1,hlens⟩ := A.vanishing_lens hinput hε
  refine ⟨(1+ρ)/2,by linarith,by linarith,?_⟩
  exact fun x z hp hm hs => (hlens x z hp hm hs).trans (by linarith)
end Midpoint

namespace DirectLayers.Regular
variable {X Y I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Preorder I]
lemma transport {A : Midpoint.Heads I X} (hA : Regular A) (e : X ≃ₗᵢ[ℝ] Y) :
    Regular (A.transport e) where
  nonempty := hA.nonempty
  upper := hA.upper
  nested_left H K hHK x := by
    simp only [Midpoint.Heads.transport_projection,e.symm_apply_apply]
    rw [hA.nested_left H K hHK]
  nested_right H K hHK x := by
    simp only [Midpoint.Heads.transport_projection,e.symm_apply_apply]
    rw [hA.nested_right H K hHK]
  contractive H x := by
    rw [Midpoint.Heads.transport_projection,e.norm_map]
    exact (hA.contractive H (e.symm x)).trans_eq (e.symm.norm_map x)
end DirectLayers.Regular

namespace PathModel
open RecursiveModel DirectLayers SignCube
instance linearFullDualSeparable : TopologicalSpace.SeparableSpace (StrongDual ℝ FullLinearSpace) := by
  let e := linearFullEquiv.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  exact e.surjective.denseRange.separableSpace e.continuous

theorem linear_full_weak_graph (hinput : PathApplications.WeakInput FullLinearSpace)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := PathApplications.weak_linear hinput k f hf

theorem linear_full_regular : Regular linearFullHeads := linear_regular.transport linearFullEquiv

theorem full_adaptive_graph (C : ℝ) (hin : SignInput linearFullHeads.projection C)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace)
    (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ)/16 ≤ C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ∧
      C*(D^2+(k:ℝ)*((2:ℝ)^k)⁻¹^2) ≤ C*(D^2+1) :=
  DirectLayers.adaptive_graph linearFullHeads linear_full_regular hin k f hf

theorem full_predictable_495_graph (hin : PredictableInput linearFullHeads.projection 495)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace)
    (hf : Diamond.HasDistortion k f D s) : (k:ℝ)/4 ≤ 495*(D+1)^2 :=
  DirectLayers.predictable_graph linearFullHeads linear_full_regular hin k f hf

theorem full_variation_252_graph (hin : PredictableInput linearFullHeads.projection 252)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace)
    (hf : Diamond.HasDistortion k f D s) : (k:ℝ)/(16*D^2) ≤ 1008 :=
  DirectLayers.variation_graph linearFullHeads linear_full_regular hin k f hf

theorem full_leakage_1024_graph (hin : LeakageInput linearFullHeads.projection)
    {D s : ℝ} (k : ℕ) (hk : 1 ≤ k) (f : Diamond.Vertex k → FullLinearSpace)
    (hf : Diamond.HasDistortion k f D s) :
    (k:ℝ)/8 ≤ 1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ∧
      1024*(D^2+(k:ℝ)*(leakageTolerance k)^2) ≤ 1024*(D^2+1) :=
  DirectLayers.leakage_graph linearFullHeads linear_full_regular hin k hk f hf

theorem full_squared_gap_400_graph (hin : GapInput linearFullHeads.projection)
    {D s γ : ℝ} (k : ℕ) (f : Diamond.Vertex k → FullLinearSpace)
    (hf : Diamond.HasDistortion k f D s) (hγ : 0 < γ)
    (hγa : γ < (2/D)/8) (hγk : γ < 1/((k:ℝ)+1)) :
    ∃ T : Protocol FullLinearSpace ForestHead k,
      T.Martingale ∧ T.Nested ∧ T.Anchored ∧ T.CommonHeads ∧ T.Supported linearFullHeads.projection ∧
      T.terminalEnergy ≤ 4 ∧ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 ≤ T.terminalEnergy ∧
      (k:ℝ)*((2/D)/8)^2/400 ≤ T.initialEnergy+(k:ℝ)*((2/D)/8)^2/400 :=
  DirectLayers.gap_graph linearFullHeads linear_full_regular hin k f hf hγ hγa hγk
end PathModel

namespace RecursiveModel
open RecursiveApplications
/-- The weak-null clause on the literal full ℓ_p recursive-array model. -/
theorem full_cubic_weak (hinput : CubicInput fullVectorHeads) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (x : FullVectorSpace) (z : ℕ → FullVectorSpace)
    (hz : Midpoint.WeaklyNull z) (hl : ∀ i,ε ≤ ‖z i‖)
    (hp : ∀ i,‖x+z i‖ ≤ 1) (hm : ∀ i,‖x-z i‖ ≤ 1) : ‖x‖ ≤ theta ε :=
  cubic_weak_lens fullVectorHeads hinput hε hε1 z hz hl hp hm

/-- The infinite separated-lens clause, before the graph specialization. -/
theorem full_sixth_lens (hinput : SixthInput fullVectorHeads) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Diamond.UnitLensBound FullVectorSpace ε (q6 ε) :=
  sixth_lens fullVectorHeads hinput hε hε1
end RecursiveModel

end DiamondDistortion

end

end OAI
