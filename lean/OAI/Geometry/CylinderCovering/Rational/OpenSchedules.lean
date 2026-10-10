import OAI.Geometry.CylinderCovering.Rational.OpenSchedulesDefinitions
import OAI.Geometry.CylinderCovering.Rational.Construction
import OAI.Geometry.CylinderCovering.Convexity.OpenParallelogram

namespace OAI

noncomputable section
open Set Filter RuledApproximation
open scoped Topology

namespace SlopeRational

theorem pointwise_open_enlargement {n : ℕ} (C : Fin n → Cylinder)
    (hC : ∀ i, (C i).parallelogram) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Fin n → Cylinder, (∀ i, (U i).axis = (C i).axis) ∧
      (∀ i, (U i).openParallelogram ∧ (U i).openBounded) ∧
      (∀ i, (C i).carrier ⊆ (U i).carrier) ∧
      familySet C ⊆ familySet U ∧ familyArea U < familyArea C + ε := by
  classical
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hδ : 0 < ε / (n + 1 : ℝ) := div_pos hε hn
  choose U haxis hshape hopen hcover harea using
    fun i => (C i).enlarge_openParallelogram (hC i) hδ
  refine ⟨U, haxis, fun i => ⟨hshape i, hopen i⟩, hcover, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, hcover i hi⟩
  · have herror : (n : ℝ) * (ε / (n + 1 : ℝ)) < ε := by
      rw [← mul_div_assoc, div_lt_iff₀ hn]
      nlinarith
    calc
      familyArea U ≤ ∑ i, ((C i).area + ε / (n + 1 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + (n : ℝ) * (ε / (n + 1 : ℝ)) := by
        simp [familyArea, Finset.sum_add_distrib]
      _ < familyArea C + ε := by linarith

theorem strict_open_enlargement {n m : ℕ}
    (C : Fin n → Cylinder) (D : Fin m → Cylinder)
    (hC : ∀ i, (C i).parallelogram) (hD : ∀ j, (D j).parallelogram)
    (harea : familyArea C + familyArea D < physicalScale / 4) :
    ∃ U : Fin n → Cylinder, ∃ V : Fin m → Cylinder,
      StrictOpenEnlargement C D U V := by
  let e := (physicalScale / 4 - (familyArea C + familyArea D)) / 4
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨U, hUa, hUs, hUp, hUc, hUm⟩ := pointwise_open_enlargement C hC he
  obtain ⟨V, hVa, hVs, hVp, hVc, hVm⟩ := pointwise_open_enlargement D hD he
  have hnew : familyArea U + familyArea V < physicalScale / 4 := by
    dsimp [e] at hUm hVm
    linarith
  have hmin : 0 < CylinderCovering.minimumShadowArea referenceTetrahedron := by
    rw [referenceTetrahedron_minimumShadowArea]
    exact half_pos physicalScale_pos
  have hrelU := CylinderCovering.relativeCost_le_familyArea_div_minimum hmin U
  have hrelV := CylinderCovering.relativeCost_le_familyArea_div_minimum hmin V
  rw [referenceTetrahedron_minimumShadowArea] at hrelU hrelV
  have hrel := add_le_add hrelU hrelV
  rw [← add_div] at hrel
  refine ⟨U, V, ⟨hUa, hVa, hUs, hVs, hUp, hVp, hUc, hVc, hnew, ?_⟩⟩
  apply hrel.trans_lt
  apply (div_lt_iff₀ (half_pos physicalScale_pos)).2
  linarith

theorem HasStrictFiniteCover.open_enlarge {d ε q : ℝ}
    (h : HasStrictFiniteCover d ε q) : HasStrictFiniteOpenCover d ε q := by
  obtain ⟨n, m, C, D, hC, hD, hlo, hup, hcov, harea, _hrel⟩ := h
  obtain ⟨U, V, hopen⟩ := strict_open_enlargement C D hC hD harea
  exact ⟨n, m, C, D, U, V, hC, hD, hlo, hup, hcov, harea, hopen⟩

theorem HasStrictFiniteOpenCover.covers {d ε q : ℝ}
    (h : HasStrictFiniteOpenCover d ε q) :
    ∃ n m : ℕ, ∃ U : Fin n → Cylinder, ∃ V : Fin m → Cylinder,
      (∀ i, (U i).openParallelogram ∧ (U i).openBounded) ∧
      (∀ j, (V j).openParallelogram ∧ (V j).openBounded) ∧
      lowerSweep d ε q ⊆ familySet U ∧ upperSweep d ε q ⊆ familySet V ∧
      referenceTetrahedron ⊆ familySet U ∪ familySet V ∧
      familyArea U + familyArea V < physicalScale / 4 ∧
      CylinderCovering.relativeCost referenceTetrahedron U +
        CylinderCovering.relativeCost referenceTetrahedron V < 1 / 2 := by
  obtain ⟨n, m, C, D, U, V, _hC, _hD, hlo, hup, hcov, _harea, hopen⟩ := h
  exact ⟨n, m, U, V, hopen.first_shape, hopen.second_shape,
    hlo.trans hopen.first_contains, hup.trans hopen.second_contains,
    hcov.trans (union_subset_union hopen.first_contains hopen.second_contains),
    hopen.area_lt, hopen.relative_lt⟩

theorem openPaddingSchedules_main : OpenPaddingSchedulesStatement := by
  obtain ⟨hexists, hschedules⟩ := paddingSchedules_main
  refine ⟨hexists, ?_⟩
  intro d hd hgap
  obtain ⟨hvanishing, hquadratic⟩ := hschedules d hd hgap
  constructor
  · filter_upwards [hvanishing] with ε hε
    exact ⟨hε.1, hε.2.open_enlarge⟩
  · intro η hη hηgap
    filter_upwards [hquadratic η hη hηgap] with ε hε
    exact ⟨hε.1, hε.2.open_enlarge⟩

end SlopeRational

end

end OAI
