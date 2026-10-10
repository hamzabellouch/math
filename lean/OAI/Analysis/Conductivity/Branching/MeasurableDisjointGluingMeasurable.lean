import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactGlobalUpdate

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
open scoped Matrix.Norms.Elementwise

lemma exists_measurable_disjoint_gluing_measurable
    {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype I] (O : I → Set X) (hO : ∀ i, MeasurableSet (O i))
    (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (A : X → Y) (hA : Measurable A) (B : I → X → Y)
    (hB : ∀ i, Measurable (B i)) :
    ∃ T : X → Y, Measurable T ∧ (∀ i, EqOn T (B i) (O i)) ∧
      EqOn T A (⋃ i, O i)ᶜ := by
  classical
  let P : Option I → Set X := fun i => match i with
    | none => (⋃ i, O i)ᶜ
    | some j => O j
  let G : Option I → X → Y := fun i => match i with
    | none => A
    | some j => B j
  have hP : ∀ i, MeasurableSet (P i) := by
    rintro (_ | i)
    · exact (MeasurableSet.iUnion hO).compl
    · exact hO i
  have hG : ∀ i, Measurable (G i) := by
    rintro (_ | i)
    · exact hA
    · exact hB i
  obtain ⟨T,hT,hTP⟩ := exists_measurable_piecewise P hP G hG (by
    rintro (_ | i) (_ | j) hij x ⟨hxi,hxj⟩
    · exact (hij rfl).elim
    · exact (hxi (mem_iUnion.mpr ⟨j,hxj⟩)).elim
    · exact (hxj (mem_iUnion.mpr ⟨i,hxi⟩)).elim
    · exact (Set.disjoint_left.mp (hd (fun e => hij (congrArg some e))) hxi hxj).elim)
  exact ⟨T,hT,fun i => hTP (some i),hTP none⟩

theorem assemble_global_updates
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Set Coord3} (O : I → Set Coord3) (hO : ∀ i, IsOpen (O i))
    (hOU : ∀ i, O i ⊆ U) (hd : Pairwise (fun i j => Disjoint (O i) (O j)))
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hA : Measurable A)
    (R : ∀ i, CompactGlobalUpdate μ (O i) u A) :
    ∃ S : CompactGlobalUpdate μ U u A,
      (S.du = fun x => ∑ i, (R i).du x) ∧
      (S.dF = fun x => ∑ i, (R i).dF x) ∧
      (∀ i, EqOn S.du (R i).du (O i) ∧ EqOn S.dF (R i).dF (O i) ∧
        EqOn S.tensor (R i).tensor (O i)) ∧ EqOn S.tensor A (⋃ i, O i)ᶜ := by
  let du : Coord3 → Fin 2 → ℝ := fun x => ∑ i, (R i).du x
  let dF : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun x => ∑ i, (R i).dF x
  have heu : ∀ i, EqOn du (R i).du (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).du) (fun i => (R i).support_du)
  have heF : ∀ i, EqOn dF (R i).dF (O i) :=
    supported_sum_eq_on O hd (fun i => (R i).dF) (fun i => (R i).support_dF)
  have hus : tsupport du ⊆ ⋃ i, O i :=
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_du))
  have hFs : tsupport dF ⊆ ⋃ i, O i :=
    (tsupport_finite_sum_subset _).trans (iUnion_mono (fun i => (R i).support_dF))
  obtain ⟨T,hT,hTon,hToff⟩ := exists_measurable_disjoint_gluing_measurable O
    (fun i => (hO i).measurableSet) hd A hA (fun i => (R i).tensor) (fun i => (R i).measurable_tensor)
  let S : CompactGlobalUpdate μ U u A := {
    du := du
    dF := dF
    tensor := T
    smooth_du := ContDiff.sum (fun i _ => (R i).smooth_du)
    compact_du := by
      simpa only [du, ← Finset.sum_apply] using
        (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_du))
    support_du := hus.trans (iUnion_subset hOU)
    smooth_dF := ContDiff.sum (fun i _ => (R i).smooth_dF)
    compact_dF := by
      simpa only [dF, ← Finset.sum_apply] using
        (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ => (R i).compact_dF))
    support_dF := hFs.trans (iUnion_subset hOU)
    cauchy_dF := finite_sum_cauchy_preserving μ (fun i => (R i).dF)
      (fun i => (R i).smooth_dF) (fun i => (R i).compact_dF) (fun i => (R i).cauchy_dF)
    measurable_tensor := hT
    constitutive := by
      intro x
      by_cases hx : x ∈ ⋃ i, O i
      · obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
        have he : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ (fun y => u y+(R i).du y) x := by
          apply Filter.EventuallyEq.fderiv_eq
          filter_upwards [(hO i).mem_nhds hxi] with y hy
          rw [heu i hy]
        simp only [conductivityFlux,hTon i hxi,he,heF i hxi]
        exact (R i).constitutive x
      · have hxu : x ∉ tsupport du := fun hu => hx (hus hu)
        have hder : fderiv ℝ (fun y => u y+du y) x = fderiv ℝ u x := by
          apply Filter.EventuallyEq.fderiv_eq
          filter_upwards [(isClosed_tsupport du).isOpen_compl.mem_nhds hxu] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy,add_zero]
        simp only [conductivityFlux,hToff hx,hder,image_eq_zero_of_notMem_tsupport (fun hy => hx (hFs hy)),add_zero]
  }
  exact ⟨S,rfl,rfl,fun i => ⟨heu i,heF i,hTon i⟩,hToff⟩

end ScalarConductivity

namespace ScalarConductivity
open Set MeasureTheory Metric
open scoped ENNReal

theorem finite_disjoint_localization_fine
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {A : Set E} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (U : I → Set E) (hU : ∀ i, IsOpen (U i)) (hc : A ⊆ ⋃ i, U i)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (Q : Fin n → Set E) (tag : Fin n → I) (center : Fin n → E),
      (∀ i, IsOpen (Q i) ∧ IsCompact (closure (Q i)) ∧ closure (Q i) ⊆ U (tag i) ∧
        μ (frontier (Q i)) = 0 ∧ closure (Q i) ⊆ Metric.ball (center i) δ) ∧
      Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧ μ (A \ ⋃ i, Q i) < ε := by
  let V : I × E → Set E := fun p => U p.1 ∩ Metric.ball p.2 δ
  have hV : ∀ p, IsOpen (V p) := fun p => (hU p.1).inter isOpen_ball
  have hcover : A ⊆ ⋃ p, V p := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hc hx)
    exact mem_iUnion.mpr ⟨(i,x),hi,mem_ball_self hδ⟩
  obtain ⟨n,Q,tag,hQ,hd,hmiss⟩ := finite_disjoint_localization_null μ hA hμA V hV hcover hε
  exact ⟨n,Q,fun i => (tag i).1,fun i => (tag i).2,
    fun i => ⟨(hQ i).1,(hQ i).2.1,(hQ i).2.2.1.trans inter_subset_left,
      (hQ i).2.2.2,(hQ i).2.2.1.trans inter_subset_right⟩,hd,hmiss⟩

end ScalarConductivity

end

end OAI
