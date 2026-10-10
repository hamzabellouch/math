import Mathlib
import OAI.Analysis.Conductivity.Variational.MatrixFiniteLaminate
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves
import OAI.Analysis.Conductivity.Branching.JoinHull

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

lemma spectralExtension_mono {T S : Set DiagonalTriple} (h : T ⊆ S) :
    spectralExtension T ⊆ spectralExtension S := by
  rintro A ⟨Q,hQ,d,hd,he⟩
  exact ⟨Q,hQ,d,h hd,he⟩

lemma spectral_depth_mono (T : Set DiagonalTriple) :
    Monotone (fun n => spectralExtension (depthClass T n)) := by
  intro m n h
  exact spectralExtension_mono (depthClass_mono T h)

lemma matrixFiniteLaminate_mem_some_depth {a b : ℝ} {T : Set DiagonalTriple}
    (hT : ∀ s, a < s → s < b → (fun _ => s) ∈ T)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) :
    ∃ n, A ∈ spectralExtension (depthClass T n) := by
  obtain ⟨Q,hQ,d,hd,he⟩ := hA
  obtain ⟨n,hn⟩ := hd.mem_some_depth hT
  exact ⟨n,Q,hQ,d,hn,he⟩

lemma exists_finite_depth_loss
    (μ : Measure Coord3) (A : Coord3 → Symmetric3) (hA : Measurable A)
    {U : Set Coord3} (hU : MeasurableSet U) (hμU : μ U ≠ ∞)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hscalar : ∀ s, a < s → s < b → (fun _ => s) ∈ T)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, μ (U \ A ⁻¹' spectralExtension (depthClass T n)) < ε := by
  let B : ℕ → Set Coord3 := fun n => U \ A ⁻¹' spectralExtension (depthClass T n)
  have hB : ∀ n, MeasurableSet (B n) := fun n => hU.diff
    ((isOpen_spectralExtension (isOpen_depthClass ha hT hsub n) (depthClass_permute hperm n)).measurableSet.preimage hA)
  have hmono : Antitone B := fun _ _ h => sdiff_subset_sdiff_right
    (preimage_mono (spectral_depth_mono T h))
  have hnull : μ (⋂ n, B n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgraph] with x hx hin
    have h0 := mem_iInter.mp hin 0
    obtain ⟨n,hn⟩ := matrixFiniteLaminate_mem_some_depth hscalar (hx h0.1)
    exact (mem_iInter.mp hin n).2 hn
  have ht : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
    rw [← hnull]
    exact tendsto_measure_iInter_atTop (fun n => (hB n).nullMeasurableSet) hmono
      ⟨0, ((measure_mono sdiff_subset).trans_lt (lt_top_iff_ne_top.mpr hμU)).ne⟩
  exact (ht.eventually (gt_mem_nhds hε)).exists

end ScalarConductivity

end

end OAI
