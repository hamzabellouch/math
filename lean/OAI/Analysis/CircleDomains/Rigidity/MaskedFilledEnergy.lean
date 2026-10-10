import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleFillings
import OAI.Analysis.CircleDomains.Rigidity.MaskedCorePreparation

namespace OAI

/-!
# Charging masked fillings to the original masked cost

Every added disk has zero pairwise wedge cost. Off the disks the
intrinsic differentials agree locally with the retained coordinates.
This proves the full cofinite masked energy estimate.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsMaskedFilledCircleFamily.integral_wedges_le_original
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hG : MeasurableSet G)
    (hM : ∀ i, IsClosed (M i)) (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * maskedCircleWedges M v z) (G \ K)) :
    (∫ z in Q \ K, 2 * maskedCircleWedges M F z) ≤
      ∫ z in G \ K, 2 * maskedCircleWedges M v z := by
  let S := (Q \ K) ∩ G
  have hSt : S ⊆ Q \ K := inter_subset_left
  have hSG : S ⊆ G \ K := fun z hz => ⟨hz.2, hz.1.2⟩
  have hS : MeasurableSet S := (hQ.measurableSet.diff hK.measurableSet).inter hG
  have hC : IsCompact (Q ∩ closure Kᶜ) :=
    hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right
  have hCΩ : Q ∩ closure Kᶜ ⊆ Ω \ ⋃ i, frontier (M i) := by
    intro z hz
    refine ⟨htail hz, ?_⟩
    intro hb
    obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    have hn : z ∉ interior K := by
      simpa only [closure_compl, mem_compl_iff] using hz.2
    exact hn (hboundary i hi)
  have hcont := ((continuousOn_maskedCircleWedges_off_boundaries hΩ M hM F hF.1).const_mul 2).mono hCΩ
  have hFi : IntegrableOn (fun z => 2 * maskedCircleWedges M F z) (Q \ K) :=
    (hcont.integrableOn_compact hC).mono_set (fun z hz => ⟨hz.1, subset_closure hz.2⟩)
  have hle (z : ℝ × ℝ) : maskedCircleWedges M F z ≤ maskedCircleWedges M v z := by
    by_cases hm : ∃ i, z ∈ D i
    · obtain ⟨i, hi⟩ := hm
      rw [hF.masked_wedges_eq_zero hi]
      exact maskedCircleWedges_nonneg M v z
    · rw [hF.masked_wedges_eq_outside hD (not_exists.mp hm)]
  have heq : (∫ z in Q \ K, 2 * maskedCircleWedges M F z) =
      ∫ z in S, 2 * maskedCircleWedges M F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hQ.measurableSet.diff hK.measurableSet) hSt
    intro z hz
    have hzG : z ∉ G := fun hzG => hz.2 ⟨hz.1, hzG⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((hcover hz.1.1).resolve_left hzG)
    rw [hF.masked_wedges_eq_zero hi, mul_zero]
  calc
    _ = ∫ z in S, 2 * maskedCircleWedges M F z := heq
    _ ≤ ∫ z in S, 2 * maskedCircleWedges M v z :=
      setIntegral_mono_on (hFi.mono_set hSt) (hv.mono_set hSG) hS
        (fun z _ => mul_le_mul_of_nonneg_left (hle z) (by norm_num))
    _ ≤ _ := setIntegral_mono_set hv
      (Eventually.of_forall fun z => mul_nonneg (by norm_num) (maskedCircleWedges_nonneg M v z))
      (Eventually.of_forall hSG)

theorem IsMaskedFilledCircleFamily.exists_spherical_metric_of_original_cost
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsMaskedFilledCircleFamily D Ω M v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hG : MeasurableSet G)
    (hM : ∀ i, IsClosed (M i)) (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * maskedCircleWedges M v z) (G \ K))
    {ε : ℝ} (hε : (∫ z in G \ K, 2 * maskedCircleWedges M v z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε := by
  have hbudget := (hF.integral_wedges_le_original hD hΩ hQ hK hKc htail hG hM hboundary hcover hv).trans_lt hε
  exact exists_spherical_metric_for_masked_cofinite_circles hΩ hQ hK hKc htail M hM hboundary F hF.1 hbudget

end CircleDomainRigidity.FiniteTransfer

end

end OAI
