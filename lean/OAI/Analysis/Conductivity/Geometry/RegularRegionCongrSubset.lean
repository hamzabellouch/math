import Mathlib
import OAI.Analysis.Conductivity.Fourier.SpectralExtensionNonemptyNonempty
import OAI.Analysis.Conductivity.Branching.MeasurableDisjointGluingMeasurable

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

lemma regularRegion_congr_subset {u v : Coord3 → Fin 2 → ℝ}
    {A B : Coord3 → Symmetric3} {O U : Set Coord3} (hOU : O ⊆ U)
    (hu : EqOn v u O) (hA : EqOn B A O) :
    regularRegion u A O ⊆ regularRegion v B U := by
  intro x hx
  obtain ⟨V,hVO,hV,hxV⟩ := mem_regularRegion_iff.mp hx
  exact mem_regularRegion_iff.mpr ⟨V,hVO.trans hOU,hV.congr (hu.mono hVO) (hA.mono hVO),hxV⟩

lemma regularRegion_piecewise_ae
    (μ : Measure Coord3) {I : Type*} [Fintype I]
    {u v : Coord3 → Fin 2 → ℝ} {A B : Coord3 → Symmetric3} {U : Set Coord3}
    (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i)) (hOU : ∀ i, O i ⊆ U)
    (old : μ (U \ regularRegion u A U) = 0)
    (localgood : ∀ i, μ (O i \ regularRegion v B (O i)) = 0)
    (hu : EqOn v u (⋃ i, O i)ᶜ) (hA : EqOn B A (⋃ i, O i)ᶜ)
    (hnull : ∀ i, μ (frontier (O i)) = 0) :
    μ (U \ regularRegion v B U) = 0 := by
  have hs : U \ regularRegion v B U ⊆ (U \ regularRegion u A U) ∪
      (⋃ i, O i \ regularRegion v B (O i)) ∪ (⋃ i, frontier (O i)) := by
    intro x hx
    by_cases hr : x ∈ regularRegion u A U
    · by_cases hi : x ∈ ⋃ i, O i
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hi
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i,hi,fun hh => hx.2
          (regularRegion_congr_subset (hOU i) (fun _ _ => rfl) (fun _ _ => rfl) hh)⟩))
      · by_cases hf : x ∈ ⋃ i, frontier (O i)
        · exact Or.inr hf
        · exfalso
          apply hx.2
          obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hr
          let W := V \ ⋃ i, closure (O i)
          have hW : IsOpen W := hV.1.sdiff (isClosed_iUnion_of_finite (fun _ => isClosed_closure))
          have hxW : x ∈ W := by
            refine ⟨hxV,?_⟩
            intro hh
            obtain ⟨i,hi'⟩ := mem_iUnion.mp hh
            apply hf
            refine mem_iUnion.mpr ⟨i,?_⟩
            rw [frontier,(hO i).interior_eq]
            exact ⟨hi',fun hh => hi (mem_iUnion.mpr ⟨i,hh⟩)⟩
          have hWoff : W ⊆ (⋃ i, O i)ᶜ := by
            intro y hy hh
            obtain ⟨i,hyi⟩ := mem_iUnion.mp hh
            exact hy.2 (mem_iUnion.mpr ⟨i,subset_closure hyi⟩)
          exact mem_regularRegion_iff.mpr ⟨W,sdiff_subset.trans hVU,
            (hV.mono hW sdiff_subset).congr (hu.mono hWoff) (hA.mono hWoff),hxW⟩
    · exact Or.inl (Or.inl ⟨hx.1,hr⟩)
  exact measure_mono_null hs (measure_union_null (measure_union_null old
    (measure_iUnion_null localgood)) (measure_iUnion_null hnull))

end ScalarConductivity

namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise ENNReal

lemma regularRegion_restrict_open {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U O : Set Coord3} (hO : IsOpen O) :
    O ∩ regularRegion u A U ⊆ regularRegion u A O := by
  intro x hx
  obtain ⟨V,hVU,hV,hxV⟩ := mem_regularRegion_iff.mp hx.2
  exact mem_regularRegion_iff.mpr ⟨V ∩ O,inter_subset_right,
    hV.mono (hV.1.inter hO) inter_subset_left,hxV,hx.1⟩

theorem fine_global_scalar_tensor_approximation
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U)
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b)
    {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (N : ℕ) (O : Fin N → Set Coord3) (center : Fin N → Coord3)
      (R : ∀ i, CompactGlobalUpdate μ (O i) u A) (S : CompactGlobalUpdate μ U u A),
      (∀ i, IsOpen (O i) ∧ closure (O i) ⊆ U ∧ closure (O i) ⊆ Metric.ball (center i) δ) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      S.du = (fun x => ∑ i, (R i).du x) ∧ S.dF = (fun x => ∑ i, (R i).dF x) ∧
      μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ U → S.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (U \ S.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ε := by
  classical
  let G := regularRegion u A U
  have hGo : IsOpen G := isOpen_regularRegion u A U
  have hGU : G ⊆ U := regularRegion_subset u A U
  obtain ⟨N,O,tag,center,hO,hd,hmiss⟩ := finite_disjoint_localization_fine μ hGo.measurableSet
    (hUb.subset hGU).measure_lt_top.ne (fun _ : Unit => G) (fun _ => hGo)
    (fun x hx => mem_iUnion.mpr ⟨(),hx⟩)
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε/2)).ne' hδ
  have hOU : ∀ i, O i ⊆ U := fun i => subset_closure.trans ((hO i).2.2.1.trans hGU)
  have hOr : ∀ i, μ (O i \ regularRegion u A (O i)) = 0 := by
    intro i
    have hs : O i ⊆ regularRegion u A (O i) := fun x hx =>
      regularRegion_restrict_open (hO i).1 ⟨hx,(hO i).2.2.1 (subset_closure hx)⟩
    simp only [sdiff_eq_empty.mpr hs,measure_empty]
  let ρ : ℝ := (ε/2)/(N+1)
  have hρ : 0 < ρ := div_pos (by linarith) (by positivity)
  have hlocal : ∀ i, ∃ R : CompactGlobalUpdate μ (O i) u A,
      μ (O i \ regularRegion (fun x => u x+R.du x) R.tensor (O i)) = 0 ∧
      (∀ᵐ x ∂μ, x ∈ O i → R.tensor x ∈ matrixFiniteLaminate a b) ∧
      μ (O i \ R.tensor ⁻¹' spectralExtension (scalarNeighbourhood a b η)) ≤ ENNReal.ofReal ρ := by
    intro i
    apply global_scalar_tensor_approximation μ ha hab (hO i).1.measurableSet (hUb.subset (hOU i)) u A hAm
      (fun j ψ hs hc ht => hint j ψ hs hc (ht.trans (hOU i)))
      (fun j ψ hs hc ht => hdiv j ψ hs hc (ht.trans (hOU i))) (hOr i)
    · filter_upwards [hgraph] with x hx
      exact fun hi => hx (hOU i hi)
    · exact hη
    · exact hρ
  choose R hRreg hRG hRbad using hlocal
  obtain ⟨S,hsu,hsF,hS,hSoff⟩ := assemble_global_updates μ O (fun i => (hO i).1) hOU hd u A hAm R
  have hsuoff : EqOn (fun x => u x+S.du x) u (⋃ i, O i)ᶜ := by
    intro x hx
    change u x+S.du x = u x
    rw [hsu]
    change u x+(∑ i, (R i).du x) = u x
    rw [supported_sum_eq_zero_off O _ (fun i => (R i).support_du) hx,add_zero]
  have hregS : μ (U \ regularRegion (fun x => u x+S.du x) S.tensor U) = 0 := by
    apply regularRegion_piecewise_ae μ O (fun i => (hO i).1) hOU hreg _ hsuoff hSoff
      (fun i => (hO i).2.2.2.1)
    intro i
    apply measure_mono_null _ (hRreg i)
    exact sdiff_subset_sdiff_right (regularRegion_congr_subset Subset.rfl
      (fun x hx => by rw [(hS i).1 hx]) (hS i).2.2)
  refine ⟨N,O,center,R,S,fun i => ⟨(hO i).1,(hO i).2.2.1.trans hGU,(hO i).2.2.2.2⟩,
    hd,hsu,hsF,hregS,?_,?_⟩
  · have hRGall : ∀ᵐ x ∂μ, ∀ i, x ∈ O i → (R i).tensor x ∈ matrixFiniteLaminate a b :=
      (ae_all_iff).mpr hRG
    filter_upwards [hgraph,hRGall] with x hx hRx
    intro hxU
    by_cases hi : x ∈ ⋃ i, O i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hi
      rw [(hS i).2.2 hi]
      exact hRx i hi
    · rw [hSoff hi]
      exact hx hxU
  · let T := spectralExtension (scalarNeighbourhood a b η)
    let bad : Fin N → Set Coord3 := fun i => O i \ (R i).tensor ⁻¹' T
    have hs : U \ S.tensor ⁻¹' T ⊆ (U \ G) ∪ ((G \ ⋃ i, O i) ∪ ⋃ i, bad i) := by
      intro x hx
      by_cases hxG : x ∈ G
      · right
        by_cases hxO : x ∈ ⋃ i, O i
        · right
          obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
          exact mem_iUnion.mpr ⟨i,hi,fun ht => hx.2 (by change S.tensor x ∈ T; rw [(hS i).2.2 hi]; exact ht)⟩
        · exact Or.inl ⟨hxG,hxO⟩
      · exact Or.inl ⟨hx.1,hxG⟩
    have hsum : (∑ i : Fin N, μ (bad i)) ≤ ENNReal.ofReal (ε/2) := by
      calc
        _ ≤ ∑ _i : Fin N, ENNReal.ofReal ρ := Finset.sum_le_sum (fun i _ => hRbad i)
        _ = ENNReal.ofReal ((N : ℝ)*ρ) := by simp [ENNReal.ofReal_mul]
        _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal (by
          dsimp [ρ]
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : (0:ℝ) < N+1)).mpr
          nlinarith)
    calc
      _ ≤ μ (U \ G) + (μ (G \ ⋃ i, O i) + ∑ i, μ (bad i)) :=
        (measure_mono (μ := μ) hs).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le μ bad)))))
      _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := by
        rw [hreg,zero_add]
        exact add_le_add hmiss.le hsum
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

end ScalarConductivity

end

end OAI
