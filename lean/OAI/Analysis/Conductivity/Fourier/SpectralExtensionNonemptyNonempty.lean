import Mathlib
import OAI.Analysis.Conductivity.Variational.Refl

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma spectralExtension_nonempty_of_nonempty {T : Set DiagonalTriple} (hT : T.Nonempty) :
    (spectralExtension T).Nonempty := by
  obtain ⟨d,hd⟩ := hT
  have hQ : (1 : Mat3) ∈ orthogonalFrames := by simp [orthogonalFrames]
  exact ⟨conjugateDiagonal 1 d,conjugateDiagonal_spectral hQ hd⟩

theorem global_scalar_tensor_approximation
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUm : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε := by
  let T := scalarNeighbourhood a b η
  have hTo : IsOpen T := isOpen_scalarNeighbourhood ha
  have hsub : ∀ d ∈ T, IsFiniteLaminate a b d := fun _ hd => hd.1
  have hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T := fun _ hd e => scalarNeighbourhood_permute hd e
  have hscalar : ∀ s, a < s → s < b → (fun _ => s) ∈ T := fun _ hs ht => scalar_mem_scalarNeighbourhood hη hs ht
  have hsc : (spectralExtension T).Nonempty := spectralExtension_nonempty_of_nonempty
    ⟨fun _ => (a+b)/2,hscalar _ (by linarith) (by linarith)⟩
  have hAmSubtype : @Measurable Coord3 Symmetric3 _ Subtype.instMeasurableSpace A := by
    change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) A at hAm
    rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)] at hAm
    exact hAm
  obtain ⟨n,hn⟩ := exists_finite_depth_loss μ A hAmSubtype hUm hUb.measure_lt_top.ne ha hTo hsub
    hperm hscalar hgraph (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2))
  obtain ⟨R,hRreg,hRG,hRloss⟩ := global_finite_depth_iteration μ ha hTo hsub hperm hsc hUb n
    u A hAm hint hdiv hreg hgraph (by linarith : 0 < ε/2)
  refine ⟨R,hRreg,hRG,hRloss.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hn.le le_rfl
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end ScalarConductivity

end

end OAI
