import OAI.Analysis.CircleDomains.Topology.CircleFillings
import OAI.Analysis.CircleDomains.Modulus.CircleWedgeCost

namespace OAI

/-!
# Charging circle fillings to the original domain

The smooth circle fillings preserve differentials off the disks and
have rank at most one inside them. Thus their cost is charged entirely
to the original domain, and one common spherical metric controls the
actual transferred circle energies.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem IsFilledCircleFamily.eventuallyEq_outside
    {I L : Type*} [Fintype I] {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : L → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) {x : ℝ × ℝ} (hx : ∀ i, x ∉ D i) (l : L) :
    F l =ᶠ[𝓝 x] v l := by
  by_cases hb : ∃ i, x ∈ frontier (D i)
  · obtain ⟨i, hi⟩ := hb
    exact ((hF.2.2.1 i).filter_mono (nhds_le_nhdsSet hi)).mono (fun _ h => h l)
  · have hc (i : I) : x ∉ closure (D i) := by
      intro hi
      apply hb
      refine ⟨i, ?_⟩
      rw [(hD i).frontier_eq]
      exact ⟨hi, hx i⟩
    have hn : ∀ᶠ y in 𝓝 x, ∀ i, y ∉ closure (D i) :=
      eventually_all.mpr (fun i => isClosed_closure.isOpen_compl.mem_nhds (hc i))
    filter_upwards [hn] with y hy
    exact hF.2.1 l y (fun i hi => hy i (subset_closure hi))

theorem IsFilledCircleFamily.circleWedges_eq_zero
    {I : Type*} {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    {i : I} {z : ℝ × ℝ} (hz : z ∈ D i) : circleWedges F z = 0 := by
  rw [circleWedges, fieldWedges_eq_sum_upperPairs]
  apply sum_eq_zero
  intro p _
  rw [hF.2.2.2 i _ _ (upperPair_ne p) z hz, abs_zero]

theorem IsFilledCircleFamily.circleWedges_eq_outside
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → UnitAddCircle} (hF : IsFilledCircleFamily D Ω v F)
    (hD : ∀ i, IsOpen (D i)) {z : ℝ × ℝ} (hz : ∀ i, z ∉ D i) :
    circleWedges F z = circleWedges v z := by
  have hgrad (l : Fin n) := circleGradient_congr_of_eventuallyEq (hF.eventuallyEq_outside hD hz l)
  rw [circleWedges, fieldWedges_eq_sum_upperPairs, circleWedges, fieldWedges_eq_sum_upperPairs]
  apply sum_congr rfl
  intro p _
  rw [hgrad, hgrad]

theorem circleWedges_nonneg {n : ℕ} (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) :
    0 ≤ circleWedges f z := by
  rw [circleWedges, fieldWedges_eq_sum_upperPairs]
  exact sum_nonneg (fun _ _ => abs_nonneg _)

theorem continuousOn_circleWedges
    {n : ℕ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (hf : ∀ i, SmoothCircleOn (f i) Ω) :
    ContinuousOn (circleWedges f) Ω := by
  have hv (i : Fin n) := (contDiffOn_circleGradient hΩ (hf i)).continuousOn
  have heq : circleWedges f = fun z => ∑ p : UpperPairs n,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| := by
    funext z
    exact fieldWedges_eq_sum_upperPairs _ z
  rw [heq]
  apply continuousOn_finsetSum
  intro p _
  exact (((hv _).fst.mul (hv _).snd).sub ((hv _).snd.mul (hv _).fst)).abs

theorem IsFilledCircleFamily.integral_wedges_le_original
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsFilledCircleFamily D Ω v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hG : MeasurableSet G) (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * circleWedges v z) (G \ K)) :
    (∫ z in Q \ K, 2 * circleWedges F z) ≤ ∫ z in G \ K, 2 * circleWedges v z := by
  let S := (Q \ K) ∩ G
  have hSt : S ⊆ Q \ K := inter_subset_left
  have hSG : S ⊆ G \ K := fun z hz => ⟨hz.2, hz.1.2⟩
  have hS : MeasurableSet S := (hQ.isClosed.measurableSet.diff hK.measurableSet).inter hG
  have hFi : IntegrableOn (fun z => 2 * circleWedges F z) (Q \ K) :=
    (((continuousOn_circleWedges hΩ F hF.1).const_mul 2).mono hQΩ
      |>.integrableOn_compact hQ).mono_set sdiff_subset
  have hle (z : ℝ × ℝ) : circleWedges F z ≤ circleWedges v z := by
    by_cases hm : ∃ i, z ∈ D i
    · obtain ⟨i, hi⟩ := hm
      rw [hF.circleWedges_eq_zero hi]
      exact circleWedges_nonneg v z
    · rw [hF.circleWedges_eq_outside hD (not_exists.mp hm)]
  have heq : (∫ z in Q \ K, 2 * circleWedges F z) = ∫ z in S, 2 * circleWedges F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hQ.isClosed.measurableSet.diff hK.measurableSet) hSt
    intro z hz
    have hzG : z ∉ G := fun hzG => hz.2 ⟨hz.1, hzG⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((hcover hz.1.1).resolve_left hzG)
    rw [hF.circleWedges_eq_zero hi, mul_zero]
  calc
    _ = ∫ z in S, 2 * circleWedges F z := heq
    _ ≤ ∫ z in S, 2 * circleWedges v z :=
      setIntegral_mono_on (hFi.mono_set hSt) (hv.mono_set hSG) hS
        (fun z _ => mul_le_mul_of_nonneg_left (hle z) (by norm_num))
    _ ≤ _ := setIntegral_mono_set hv
      (Eventually.of_forall fun z => mul_nonneg (by norm_num) (circleWedges_nonneg v z))
      (Eventually.of_forall hSG)

theorem IsFilledCircleFamily.exists_spherical_metric_of_original_cost
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → UnitAddCircle}
    (hF : IsFilledCircleFamily D Ω v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hG : MeasurableSet G) (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * circleWedges v z) (G \ K))
    {ε : ℝ} (hε : (∫ z in G \ K, 2 * circleWedges v z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in Q \ K, fieldEnergy (circleGradient (F i)) g z) < ε := by
  have hbudget := (hF.integral_wedges_le_original hD hΩ hQ hQΩ hK hG hcover hv).trans_lt hε
  have hm : ∀ i : Fin n, IsClosed (univ : Set (ℝ × ℝ)) := fun _ => isClosed_univ
  have hboundary : ∀ i : Fin n, frontier (univ : Set (ℝ × ℝ)) ⊆ interior K := by
    intro i
    simp
  have hmasked : (∫ z in Q \ K,
      2 * maskedCircleWedges (fun _ : Fin n => univ) F z) < ε := by
    simpa only [maskedCircleWedges, circleWedges, fieldWedges_eq_sum_upperPairs, indicator_univ] using hbudget
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_spherical_metric_for_masked_circles hΩ hQ hQΩ hK (fun _ => univ) hm hboundary F
      (fun i => by simpa only [interior_univ, inter_univ] using hF.1 i) hmasked
  exact ⟨R, g, hR, hg, hPD, hcore, hfar, by simpa only [inter_univ] using henergy⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
