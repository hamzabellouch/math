import Mathlib
import OAI.Analysis.Conductivity.Flux.AssembleCompatibleTensors
import OAI.Analysis.Conductivity.Flux.OpenRegularTensorTarget
import OAI.Analysis.Conductivity.Geometry.RegularRegionFiniteGluing

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

structure CompactGlobalUpdate (μ : Measure Coord3) (U : Set Coord3)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) where
  du : Coord3 → Fin 2 → ℝ
  dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  tensor : Coord3 → Symmetric3
  smooth_du : ContDiff ℝ (↑(⊤ : ℕ∞)) du
  compact_du : HasCompactSupport du
  support_du : tsupport du ⊆ U
  smooth_dF : ContDiff ℝ (↑(⊤ : ℕ∞)) dF
  compact_dF : HasCompactSupport dF
  support_dF : tsupport dF ⊆ U
  cauchy_dF : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
    (∫ x, fderiv ℝ ψ x ((dF x).col j) ∂μ) = 0
  measurable_tensor : Measurable tensor
  constitutive : ∀ x, conductivityFlux (fun y => u y+du y) tensor x = conductivityFlux u A x+dF x

theorem global_regular_depth_reduction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {n : ℕ} (hsc : (spectralExtension (depthClass T n)).Nonempty)
    {G : Set Coord3} (hGm : MeasurableSet G)
    (hG : G ⊆ regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : CompactGlobalUpdate μ U u A,
      μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) ≤ μ (U \ G) + ENNReal.ofReal ε := by
  classical
  obtain ⟨N,O,P,hO,hd,hP,hPG,hloss⟩ := finite_regular_depth_reduction μ u A hUb hdiv
    ha hT hsub hperm hsc hGm hG hε
  obtain ⟨du,dF,B,hus,huc,hUs,hFs,hFc,hFS,hpair,hB,heq,hoff,hconst⟩ :=
    assemble_compatible_tensors μ O (fun i => (hO i).1) hd u A hAm P
  have hOU : (⋃ i, O i) ⊆ U := iUnion_subset (fun i => subset_closure.trans (hO i).2.2.1)
  let R : CompactGlobalUpdate μ U u A := ⟨du,dF,B,hus,huc,hUs.trans hOU,
    hFs,hFc,hFS.trans hOU,hpair,hB,hconst⟩
  have hnew : ∀ i, RegularPatch (fun x => u x+du x) B (O i) := by
    intro i
    exact (hP i).congr (fun x hx => by rw [(heq i).1 hx]) (heq i).2.2
  have huo : EqOn (fun x => u x+du x) u (⋃ i, O i)ᶜ := by
    intro x hx
    change u x+du x = u x
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hUs hs)),add_zero]
  refine ⟨R,regularRegion_finite_gluing_ae μ hreg O
    (fun i => subset_closure.trans (hO i).2.2.1) hnew huo hoff (fun i => (hO i).2.2.2),?_,?_⟩
  · filter_upwards [hgraph] with x hx
    intro hxU
    change B x ∈ matrixFiniteLaminate a b
    by_cases hxin : x ∈ ⋃ i, O i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hxin
      rw [(heq i).2.2 hi]
      exact hPG i x hi
    · rw [hoff hxin]
      exact hx hxU
  · let bad : Fin N → Set Coord3 := fun i =>
      {x | x ∈ O i ∧ (P i).tensor x ∉ spectralExtension (depthClass T n)}
    have hset : U \ B ⁻¹' spectralExtension (depthClass T n) ⊆
        (U \ G) ∪ ((G \ ⋃ i, O i) ∪ (⋃ i, bad i)) := by
      intro x hx
      by_cases hxG : x ∈ G
      · right
        by_cases hxO : x ∈ ⋃ i, O i
        · right
          obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
          exact mem_iUnion.mpr ⟨i,hi,by rw [← (heq i).2.2 hi]; exact hx.2⟩
        · exact Or.inl ⟨hxG,hxO⟩
      · exact Or.inl ⟨hx.1,hxG⟩
    calc
      μ (U \ R.tensor ⁻¹' spectralExtension (depthClass T n)) ≤
          μ (U \ G) + (μ (G \ ⋃ i, O i) + μ (⋃ i, bad i)) :=
        (measure_mono hset).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ μ (U \ G) + (μ (G \ ⋃ i, O i) + ∑ i, μ (bad i)) :=
        add_le_add le_rfl (add_le_add le_rfl (measure_iUnion_fintype_le μ bad))
      _ ≤ μ (U \ G) + ENNReal.ofReal ε := add_le_add le_rfl hloss

end ScalarConductivity

end

end OAI
