import Mathlib
import OAI.Analysis.SymmetricDomains.GenericNashNormalCoordinates
import OAI.Analysis.SymmetricDomains.ProjectionNashChartGerms

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

theorem differentiable_image_null_same_dimension {d n : ℕ} (hd : d=n)
    (f : (Fin d → ℝ) → (Fin n → ℝ)) {A : Set (Fin d → ℝ)}
    (hf : DifferentiableOn ℝ f A) (hA : volume A = 0) :
    volume (f '' A) = 0 := by
  subst n
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hf hA

theorem partial_homeomorph_preimage_null {d n : ℕ} (hd : d=n)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin n → ℝ))
    {B A : Set (Fin n → ℝ)}
    (he : DifferentiableOn ℝ e.symm B) (hAB : A ⊆ B) (hA : volume A = 0) :
    volume (e.source ∩ e ⁻¹' A) = 0 := by
  have him := differentiable_image_null_same_dimension hd.symm e.symm (he.mono hAB) hA
  apply measure_mono_null (t := e.symm '' A) _ him
  intro x hx
  exact ⟨e x,hx.2,e.left_inv hx.1⟩

theorem locally_null_bad_set {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) (A : Set X) (P : X → Prop)
    (h : ∀ x ∈ A, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ μ {y | y ∈ A ∧ y ∈ W ∧ ¬ P y} = 0) :
    μ {y | y ∈ A ∧ ¬ P y} = 0 := by
  choose W hWo hxW hn using fun x : A => h x.val x.property
  obtain ⟨C,hCc,hCov⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover W hWo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩)
  have hnull : μ (⋃ x ∈ C, {y | y ∈ A ∧ y ∈ W x ∧ ¬ P y}) = 0 :=
    measure_biUnion_null_iff hCc |>.mpr (fun x _ => hn x)
  apply measure_mono_null _ hnull
  intro y hy
  obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hCov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hy.1,hxy,hy.2⟩
end

open Set Filter Topology Metric
open scoped Classical

lemma polynomialSignSet_linear_product_preimage {a b c : ℕ}
    {S : Set (Fin c → ℝ)} (hS : PolynomialSignSet id S)
    (L : ((Fin a → ℝ) × (Fin b → ℝ)) →ₗ[ℝ] (Fin c → ℝ)) :
    PolynomialSignSet (fun z => Sum.elim z.1 z.2) (L ⁻¹' S) := by
  let e := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ
  have hh := (SemialgebraicOn.affine PolynomialSignSet.univ (L.comp e.toLinearMap) 0).preimage hS
  simp only [univ_inter,add_zero] at hh
  exact hh.coordinate_preimage (fun z : (Fin a → ℝ) × (Fin b → ℝ) => Sum.elim z.1 z.2) id (by intro z i; rfl)

theorem nash_normal_graph_boundary {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N)
    (hqa : AnalyticOnNhd ℝ q B)
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N)
    (hHπ : ∀ᶠ y in 𝓝[V] (q a), H (π (y-q a)) = y)
    (r : ℝ) (hr : 0 < r)
    (hHs : SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < r}
      (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x))))
    (nc : NashNormalCoordinates B (fun x => π (q x-q a)) a) :
    let C := (nc.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
      (complexGraphRealEquiv nc.tangentDim nc.normalDim)
    let D := {z | ‖complexRealEquiv m (C.symm z)‖ < r ∧ H (C.symm z) ∈ U}
    PolynomialSignSet (fun z => Sum.elim z.1 z.2) D ∧
      ∃ R : ℝ, 0 < R ∧ R ≤ nc.radius ∧
        ∀ s ∈ ball 0 R, (s,nc.graph s) ∈ closure D \ D ∧
          ‖complexRealEquiv m (C.symm (s,nc.graph s))‖ < r ∧
          H (C.symm (s,nc.graph s)) = q (nc.parameters.symm s) := by
  let C := (nc.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
    (complexGraphRealEquiv nc.tangentDim nc.normalDim)
  let T := {z | ‖complexRealEquiv m (C.symm z)‖ < r}
  let F := H ∘ C.symm
  let G := fun y => C (π (y-q a))
  let D := T ∩ F ⁻¹' U
  have hDs : PolynomialSignSet (fun z => Sum.elim z.1 z.2) D := by
    have hu := semialgebraic_nash_chart_preimage hUs H hHs
    have hh := polynomialSignSet_linear_product_preimage hu
      ((complexRealEquiv m).toLinearMap.comp C.symm.toLinearMap)
    convert hh using 1
    ext z
    change (‖complexRealEquiv m (C.symm z)‖ < r ∧ H (C.symm z) ∈ U) ↔
      (‖complexRealEquiv m (C.symm z)‖ < r ∧
        H ((complexRealEquiv m).symm (complexRealEquiv m (C.symm z))) ∈ U)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hDs,?_⟩
  have hG : Continuous G := C.continuous.comp (π.continuous.comp (continuous_id.sub continuous_const))
  have hFG : ∀ᶠ y in 𝓝[V] (q a), F (G y) = y := by
    simpa only [F,G,Function.comp_apply,C.symm_apply_apply] using hHπ
  have hT : IsOpen T := isOpen_lt
    ((complexRealEquiv m).continuous.comp C.symm.continuous |>.norm) continuous_const
  have h0T : G (q a) ∈ T := by change ‖complexRealEquiv m (C.symm (C (π (q a-q a))))‖ < r; simpa using hr
  obtain ⟨W,hW,haW,htrans⟩ := inverse_germ_boundary_transfer U V hUV hV F G hG (q a) hFG T hT h0T
  have hinvc : ContinuousAt nc.parameters.symm 0 :=
    (nc.inverse_analytic 0 (mem_ball_self nc.radius_pos)).continuousAt
  have hqc : ContinuousAt (q ∘ nc.parameters.symm) 0 :=
    ContinuousAt.comp_of_eq (hqa a ha).continuousAt hinvc nc.inverse_zero
  have hnear : ∀ᶠ s in 𝓝 (0 : Fin ((nc.tangentDim+nc.tangentDim)+nc.normalDim) → ℝ),
      s ∈ ball 0 nc.radius ∧ q (nc.parameters.symm s) ∈ W :=
    inter_mem (ball_mem_nhds _ nc.radius_pos) (by
      apply hqc.preimage_mem_nhds
      simpa only [Function.comp_apply,nc.inverse_zero] using hW.mem_nhds haW)
  obtain ⟨R,hR,hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min R nc.radius,lt_min hR nc.radius_pos,min_le_right _ _,?_⟩
  intro s hs
  have hsR : s ∈ ball 0 R := ball_subset_ball (min_le_left _ _) hs
  have hh := hRsub hsR
  have hxB := nc.inverse_mapsTo hh.1
  have hg := htrans _ ⟨hqb _ hxB,hh.2⟩
  have hgraph : G (q (nc.parameters.symm s)) = (s,nc.graph s) := by
    change complexGraphRealEquiv nc.tangentDim nc.normalDim
      (nc.coordinates (π (q (nc.parameters.symm s)-q a))) = _
    have h := nc.graph_identity s hh.1
    simpa only [sub_self,map_zero,sub_zero] using h
  rw [hgraph] at hg
  exact hg
end Release061

end

end OAI
