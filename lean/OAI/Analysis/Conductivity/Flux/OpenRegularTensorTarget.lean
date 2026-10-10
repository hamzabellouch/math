import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactDepthReductionRegular
import OAI.Analysis.Conductivity.Geometry.RegularPatch

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

lemma isOpen_regular_tensor_target (u : Coord3 → Fin 2 → ℝ)
    (A : Coord3 → Symmetric3) (U : Set Coord3) {T : Set Symmetric3} (hT : IsOpen T) :
    IsOpen (regularRegion u A U ∩ A ⁻¹' T) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp hx.1
  have hAc : ContinuousAt A x := Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (hO.2.2.1.continuousOn.continuousAt (hO.1.mem_nhds hxO))
  exact Filter.inter_mem ((isOpen_regularRegion u A U).mem_nhds hx.1)
    (hAc.preimage_mem_nhds (hT.mem_nhds hx.2))

theorem finite_regular_depth_reduction
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : IsOpen T) (hsub : ∀ d ∈ T, IsFiniteLaminate a b d)
    (hperm : ∀ d ∈ T, ∀ e : Equiv.Perm (Fin 3), d ∘ e ∈ T)
    {n : ℕ} (hsc : (spectralExtension (depthClass T n)).Nonempty)
    {G : Set Coord3} (hGm : MeasurableSet G)
    (hG : G ⊆ regularRegion u A U ∩ A ⁻¹' spectralExtension (depthClass T (n+1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (O : Fin N → Set Coord3) (R : ∀ i, CompactCompatibleReplacement μ (O i) u A),
      (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧ closure (O i) ⊆ U ∧ μ (frontier (O i)) = 0) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      (∀ i, RegularPatch (fun x => u x+(R i).du x) (R i).tensor (O i)) ∧
      (∀ i x, x ∈ O i → (R i).tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (G \ ⋃ i, O i) +
        ∑ i, μ {x | x ∈ O i ∧ (R i).tensor x ∉ spectralExtension (depthClass T n)}
          ≤ ENNReal.ofReal ε := by
  classical
  have hlocal : ∀ p : G, ∃ W : Set Coord3,
      IsOpen W ∧ p.val ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W → ∀ δ : ℝ, 0 < δ →
      ∃ R : CompactCompatibleReplacement μ O u A,
        RegularPatch (fun x => u x+R.du x) R.tensor O ∧
        (∀ x ∈ O, R.tensor x ∈ matrixFiniteLaminate a b) ∧
        μ {x | x ∈ O ∧ R.tensor x ∉ spectralExtension (depthClass T n)} ≤ ENNReal.ofReal δ := by
    intro p
    obtain ⟨V,hVU,hV,hpV⟩ := mem_regularRegion_iff.mp (hG p.property).1
    obtain ⟨W,hW,hpW,hWV,hWc,hop⟩ := exists_compact_depth_reduction_regular μ u A
      hV.1 (hUb.subset hVU) hV.2.1 hV.2.2.1
      (fun j ψ hs hc ht => hdiv j ψ hs hc (ht.trans hVU)) hV.2.2.2
      ha hT hsub hperm hpV (hG p.property).2 hsc
    refine ⟨W,hW,hpW,hWV.trans hVU,hWc,?_⟩
    intro O hO hOW δ hδ
    obtain ⟨R,hr,hRG,hbad⟩ := hop O hO hOW δ hδ
    exact ⟨R,⟨hO,(hV.2.1.mono (hOW.trans (subset_closure.trans hWV))).add R.smooth_du.contDiffOn,
      R.smooth_tensor,hr⟩,hRG,hbad⟩
  choose W hWo hpW hWU hWc hop using hlocal
  have hμG : μ G ≠ ∞ := (hUb.subset (hG.trans (inter_subset_left.trans (regularRegion_subset u A U)))).measure_lt_top.ne
  have hcover : G ⊆ ⋃ p : G, W p := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hpW ⟨x,hx⟩⟩
  obtain ⟨N,O,tag,hO,hd,hmiss⟩ := finite_disjoint_localization_null μ hGm hμG W hWo hcover
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2)).ne'
  let δ : ℝ := (ε/2) / (N+1)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  choose R hR hRG hbad using fun i => hop (tag i) (O i) (hO i).1
    (subset_closure.trans (hO i).2.2.1) δ hδ
  refine ⟨N,O,R,fun i => ⟨(hO i).1,(hO i).2.1,(hO i).2.2.1.trans (subset_closure.trans (hWU (tag i))),
    (hO i).2.2.2⟩,hd,hR,hRG,?_⟩
  have hsum : (∑ i : Fin N, μ {x | x ∈ O i ∧ (R i).tensor x ∉ spectralExtension (depthClass T n)})
      ≤ ENNReal.ofReal (ε/2) := by
    calc
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal δ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = ENNReal.ofReal ((N : ℝ) * δ) := by simp [ENNReal.ofReal_mul]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal (by
        dsimp [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0:ℝ) < N+1)).mpr
        nlinarith)
  calc
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hmiss.le hsum
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end ScalarConductivity

end

end OAI
