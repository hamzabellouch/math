import Mathlib
import OAI.Geometry.CAT0Fillings.Reconstruction.Identification

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma restrictCurrent_congr {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {S U : Functional X k}
    (hS : IsMetricCurrent S) (hU : IsMetricCurrent U) (he : S = U) (E : Set X) :
    restrictCurrent hS E = restrictCurrent hU E := by
  subst U
  rfl

lemma integerRectifiable_of_chart_restrictions {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (C : ℕ → IntegerChart X k)
    (hact : ∀ i, (C i).action = restrictCurrent hT (C i).image)
    (hcover : currentMassMeasure hT (⋃ i, (C i).image)ᶜ = 0) :
    IntegerRectifiable T := by
  classical
  let Z : ℕ → Set X := disjointed (fun i => (C i).image)
  have hZ i : MeasurableSet (Z i) := MeasurableSet.disjointed (fun j => (C j).measurableSet_image) i
  have hd : Pairwise (fun i j => Disjoint (Z i) (Z j)) := disjoint_disjointed _
  have hZi i : Z i ⊆ (C i).image := disjointed_subset _ i
  have hZunion : (⋃ i, Z i) = ⋃ i, (C i).image := iUnion_disjointed
  let D i := (C i).restrictImage (Z i) (hZ i)
  have hDim i : (D i).image = Z i := by
    rw [IntegerChart.restrictImage_image,inter_eq_right.mpr (hZi i)]
  have hDa i : (D i).action = restrictCurrent hT (Z i) := by
    have hC : IsMetricCurrent (C i).action := (C i).action_isMetricCurrent
    have he := (C i).restrictImage_action (Z i) (hZ i) hC
    have hr : restrictCurrent hC (Z i) =
        restrictCurrent (restrictCurrent_isMetricCurrent hT (C i).measurableSet_image) (Z i) := by
      exact restrictCurrent_congr hC
        (restrictCurrent_isMetricCurrent hT (C i).measurableSet_image) (hact i) (Z i)
    exact he.trans (hr.trans (by rw [restrictCurrent_restrict hT (C i).measurableSet_image (hZ i),
      inter_eq_right.mpr (hZi i)]))
  refine ⟨D,?_,?_,?_,?_⟩
  · simpa only [hDim] using hd
  · intro i
    rw [hDa]
    exact restrictCurrent_isMetricCurrent hT (hZ i)
  · simp only [hDa]
    exact summable_restriction_mass hT Z hZ hd
  · intro b π
    rw [show T = restrictCurrent hT (⋃ i, Z i) from
      (restrictCurrent_eq_self_of_mass_compl_zero hT (MeasurableSet.iUnion hZ)
        (by simpa only [hZunion] using hcover)).symm]
    rw [restrictCurrent_iUnion hT Z hZ hd]
    exact tsum_congr fun i => congrFun (congrFun (hDa i).symm b) π

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

abbrev FullGraphCode := Σ (_ : ℕ × ℕ) (i : FullGraphIndex), Fin i.2.size

theorem exists_joint_chart_mass_cover {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X) :
    ∃ C : FullGraphCode → IntegerChart X (k+1),
      (∀ i, (C i).action = restrictCurrent h.metric (C i).image) ∧
      currentMassMeasure h.metric (⋃ i, (C i).image)ᶜ = 0 := by
  classical
  obtain ⟨b,π,hadm,htests⟩ := exists_countable_current_tests (X := X) (k+1)
  let p (q : ℕ × ℕ) := π q.1 q.2
  have hp (q : ℕ × ℕ) : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (p q i) := (hadm q.1 q.2).2
  have hu (q : ℕ × ℕ) : ∃ K : ℝ≥0, ∀ i, LipschitzWith K (p q i) := by
    choose L hL using hp q
    exact ⟨Finset.univ.sup L,fun i => (hL i).weaken (Finset.le_sup (Finset.mem_univ i))⟩
  choose K hK using hu
  have hpb q i := boundedLip_of_lipschitz (hK q i)
  choose E L U α hEc hEae hαL hαA hαu hαrep hαinj using
    fun q => fullSlice_compact_atom_graphs h hX (p q) (hK q)
  let D (i : FullGraphCode) : Set (Euc (k+1)) := E i.1 i.2.1
  let γ (i : FullGraphCode) (t : D i) : X := α i.1 i.2.1 t i.2.2
  have hD (i : FullGraphCode) : IsCompact (D i) := hEc i.1 i.2.1
  have hγ (i : FullGraphCode) : ∃ K L : ℝ≥0,
      LipschitzWith K (γ i) ∧ AntilipschitzWith L (γ i) :=
    ⟨L i.1 i.2.1,U i.1 i.2.1,hαL i.1 i.2.1 i.2.2,hαA i.1 i.2.1 i.2.2⟩
  let G : Set X := ⋃ i, Set.range (γ i)
  have hGc (i : FullGraphCode) : IsCompact (Set.range (γ i)) := by
    let : CompactSpace (D i) := isCompact_iff_compactSpace.mp (hD i)
    exact isCompact_range (hγ i).choose_spec.choose_spec.1.continuous
  have hG : MeasurableSet G := MeasurableSet.iUnion fun i => (hGc i).measurableSet
  have hrest : restrictCurrent h.metric Gᶜ = fun _ _ => 0 := by
    apply htests _ _ (restrictCurrent_isMetricCurrent h.metric hG.compl) (isMetricCurrent_zero (k+1))
    intro a j
    let q : ℕ × ℕ := (a,j)
    let f : X → ℝ := Gᶜ.indicator (b a j)
    have hf : Measurable f := (hadm a j).1.continuous.measurable.indicator hG.compl
    obtain ⟨B,hBb⟩ := (hadm a j).1.2
    let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
    have hBf (x : X) : |f x| ≤ B' := by
      by_cases hx : x ∈ Gᶜ
      · dsimp only [f]
        rw [indicator_of_mem hx]
        exact (hBb x).trans (le_max_left B 0)
      · simp only [f,indicator_of_notMem hx,abs_zero]
        exact B'.coe_nonneg
    have hslice : ∀ᵐ t : Euc (k+1),
        currentBorelAction (fullSlice h (p q) t) f (fun z => Fin.elim0 z) = 0 := by
      filter_upwards [hEae q] with t ht
      obtain ⟨i,hti⟩ := mem_iUnion.mp ht
      apply (hαrep q i ⟨t,hti⟩).borelAction_zero (fullSlice_integral h (p q) t).1 hf
      intro v
      have hx : α q i ⟨t,hti⟩ v ∈ G := by
        refine mem_iUnion.mpr ⟨⟨q,i,v⟩,?_⟩
        exact ⟨⟨t,hti⟩,rfl⟩
      exact indicator_of_notMem (by simpa only [mem_compl_iff,not_not] using hx) _
    have hagr := fullSlice_borel_integral h hX (p q) (hpb q) hf B' hBf
    dsimp only [ActionIntegralAgreement] at hagr
    rw [integral_eq_zero_of_ae hslice] at hagr
    rw [restrictCurrent_apply h.metric Gᶜ (hadm a j)]
    exact (currentBorelAction_eq h.metric f (π a j)).symm.trans hagr.2
  let C (i : FullGraphCode) : IntegerChart X (k+1) :=
    jointGraphChart (hD i) (γ i) (hγ i) (i.2.1.2.weights i.2.2)
  have hCi (i : FullGraphCode) : (C i).image = Set.range (γ i) := rfl
  refine ⟨C,?_,?_⟩
  · intro i
    rw [hCi]
    exact (joint_graph_restriction_eq_chart h hX (p i.1) (hpb i.1)
      (hEc i.1 i.2.1) (α i.1 i.2.1)
      (fun j => ⟨L i.1 i.2.1,U i.1 i.2.1,hαL i.1 i.2.1 j,hαA i.1 i.2.1 j⟩)
      i.2.1.2.weights (hαu i.1 i.2.1) (hαinj i.1 i.2.1)
      (hαrep i.1 i.2.1) i.2.2).symm
  simp only [hCi]
  have hz : Controls (restrictCurrent h.metric Gᶜ) (0 : Measure X) := by
    rw [hrest]
    intro b π _ _
    simp
  have hm := currentMassMeasure_le (restrictCurrent_isMetricCurrent h.metric hG.compl) hz Set.univ
  rw [restriction_massMeasure h.metric hG.compl,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at hm
  exact le_antisymm (by simpa [G] using hm) bot_le

theorem integerRectifiable_succ_of_normalApprox {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X) : IntegerRectifiable T := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_joint_chart_mass_cover h hX
  let : Nonempty FullGraphCode := ⟨⟨(0,0),
    ((0,0,0,0),⟨1,(fun _ => 1),(fun _ => 0),1⟩),0⟩⟩
  obtain ⟨e,he⟩ := exists_surjective_nat FullGraphCode
  apply integerRectifiable_of_chart_restrictions h.metric (C ∘ e) (fun i => hC (e i))
  have hu : (⋃ i, (C (e i)).image) = ⋃ j, (C j).image := by
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i,hi⟩ => ⟨e i,hi⟩,fun ⟨j,hj⟩ => by
      obtain ⟨i,rfl⟩ := he j
      exact ⟨i,hj⟩⟩
  simpa only [Function.comp_apply,hu] using hcover

end CAT0Fillings.SliceReconstruction
end

end OAI
