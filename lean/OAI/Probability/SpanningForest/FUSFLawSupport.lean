import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

theorem ustCylinder_eq_zero_of_present_not_mem
    (K : FiniteSubgraphCode) (A B : Finset EdgeCode) (e : EdgeCode)
    (he : e ∈ A) (hne : e.1 ∉ K.2) :
    ustCylinder K A B = 0 := by
  classical
  unfold ustCylinder
  apply ENNReal.div_eq_zero_iff.mpr
  left
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  apply Finset.ext
  intro T
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hT, hgood⟩
  have ht : T ⊆ K.2 ∧ TreeOn K T := by
    simpa only [spanningTrees, Finset.mem_filter, Finset.mem_powerset] using hT
  exact hne (ht.2.1 (hgood.1 e he))

theorem ustCylinder_eq_zero_of_nonedge
    {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A)
    (hne : ¬ Adj G e.1.1 e.1.2) :
    ustCylinder K A B = 0 := by
  apply ustCylinder_eq_zero_of_present_not_mem K A B e he
  intro hmem
  exact hne (hK.2.1 e.1 hmem).2.2.2

theorem HasFUSFLaw.measure_cylinder_eq_zero_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (A B : Finset EdgeCode) (e : EdgeCode) (he : e ∈ A)
    (hne : ¬ Adj G e.1.1 e.1.2) :
    P {ω | (∀ f ∈ A, X ω f = true) ∧ (∀ f ∈ B, X ω f = false)} = 0 := by
  have hconv := hX.2 H hH A B
  have hzero : (fun n => ustCylinder (H n) A B) = fun _ => 0 := by
    funext n
    exact ustCylinder_eq_zero_of_nonedge (hH.1 n) A B e he hne
  rw [hzero] at hconv
  exact tendsto_nhds_unique hconv tendsto_const_nhds

theorem HasFUSFLaw.measure_present_eq_zero_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (e : EdgeCode) (hne : ¬ Adj G e.1.1 e.1.2) :
    P {ω | X ω e = true} = 0 := by
  simpa using hX.measure_cylinder_eq_zero_of_nonedge H hH {e} ∅ e
    (Finset.mem_singleton_self e) hne

theorem HasFUSFLaw.ae_false_of_nonedge
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (e : EdgeCode) (hne : ¬ Adj G e.1.1 e.1.2) :
    ∀ᵐ ω ∂P, X ω e = false := by
  rw [ae_iff]
  simpa only [Bool.not_eq_false] using
    hX.measure_present_eq_zero_of_nonedge H hH e hne

theorem HasFUSFLaw.ae_subgraph
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H) :
    ∀ᵐ ω ∂P, ∀ e : EdgeCode, X ω e = true → Adj G e.1.1 e.1.2 := by
  rw [ae_all_iff]
  intro e
  by_cases he : Adj G e.1.1 e.1.2
  · exact Filter.Eventually.of_forall (fun _ _ => he)
  · filter_upwards [hX.ae_false_of_nonedge H hH e he] with ω hω
    intro htrue
    simp [hω] at htrue

theorem HasFUSFLaw.congr_ae
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X Y : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (hY : ∀ e, Measurable (fun ω => Y ω e))
    (hXY : ∀ e, (fun ω => X ω e) =ᵐ[P] fun ω => Y ω e) :
    HasFUSFLaw G P Y := by
  refine ⟨hY, ?_⟩
  intro H hH A B
  have hall : ∀ᵐ ω ∂P, ∀ e, X ω e = Y ω e := ae_all_iff.mpr hXY
  have hevents : {ω | (∀ e ∈ A, X ω e = true) ∧ (∀ e ∈ B, X ω e = false)}
      =ᵐ[P] {ω | (∀ e ∈ A, Y ω e = true) ∧ (∀ e ∈ B, Y ω e = false)} := by
    filter_upwards [hall] with ω hω
    exact congrArg (fun z : EdgeConfiguration =>
      (∀ e ∈ A, z e = true) ∧ (∀ e ∈ B, z e = false)) (funext hω)
  rw [← measure_congr hevents]
  exact hX.2 H hH A B

theorem HasFUSFLaw.measure_univ_eq_one_of_spanningTrees_nonempty
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (hne : ∀ n, (spanningTrees (H n)).Nonempty) :
    P Set.univ = 1 := by
  classical
  have hnorm (n : ℕ) : ustCylinder (H n) ∅ ∅ = 1 := by
    have hc : (spanningTrees (H n)).card ≠ 0 := Finset.card_ne_zero.mpr (hne n)
    simp only [ustCylinder, Finset.notMem_empty, false_implies, implies_true,
      and_self, Finset.filter_true]
    exact ENNReal.div_self (by exact_mod_cast hc) (by simp)
  have hconv := hX.2 H hH ∅ ∅
  simp only [hnorm] at hconv
  simpa using tendsto_nhds_unique hconv tendsto_const_nhds

theorem HasFUSFLaw.isProbabilityMeasure_of_spanningTrees_nonempty
    {Ω : Type} [MeasurableSpace Ω] {G : GraphCode}
    {P : Measure Ω} {X : Ω → EdgeConfiguration}
    (hX : HasFUSFLaw G P X)
    (H : ℕ → FiniteSubgraphCode) (hH : IsConnectedExhaustion G H)
    (hne : ∀ n, (spanningTrees (H n)).Nonempty) :
    IsProbabilityMeasure P :=
  ⟨hX.measure_univ_eq_one_of_spanningTrees_nonempty H hH hne⟩

end Problem336

end

end OAI
