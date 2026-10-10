import OAI.Analysis.IrrationalRotation.Analysis.BlockedPositiveEvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem ae_all_coordinates_mem_Ico
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j, ∀ s i,
      (z s i).2.1 ∈ Ico (0 : ℝ) 1 ∧ (z s i).2.2 ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro s
  apply ae_all_iff.2
  intro i
  have hs : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ico (0 : ℝ) 1),
      t ∈ Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  have hx := (Measure.absolutelyContinuous_of_le_smul
    (law_left_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j s i)).ae_le hs
  have hy := (Measure.absolutelyContinuous_of_le_smul
    (law_right_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j s i)).ae_le hs
  have hmx : Measurable (fun z : Sample m => (z s i).2.1) := by fun_prop
  have hmy : Measurable (fun z : Sample m => (z s i).2.2) := by fun_prop
  exact (ae_of_ae_map hmx.aemeasurable hx).and (ae_of_ae_map hmy.aemeasurable hy)

theorem ae_all_coordinates_ordered
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j, ∀ s i, (z s i).2.1 ≤ (z s i).2.2 := by
  apply ae_all_iff.2
  intro s
  apply ae_all_iff.2
  intro i
  have ho : ∀ᵐ q ∂OneCoordinateCoupling.labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0), q.2.1 ≤ q.2.2 :=
    OneCoordinateCoupling.labelledLaw_ae_ordered (by have := hm s; norm_cast; omega)
  rw [← law_map_coordinate hm hκ0 hκ ha ha' hb hb' j s i] at ho
  exact ae_of_ae_map ((measurable_pi_apply i).comp (measurable_pi_apply s)).aemeasurable ho

theorem ae_circle_representatives
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j, ∀ i,
      circleRepresentative (circleLeftEndpoint e z i) = leftEndpoint e z i ∧
      circleRepresentative (circleRightEndpoint e z i) = rightEndpoint e z i := by
  filter_upwards [ae_all_coordinates_mem_Ico hm hκ0 hκ ha ha' hb hb' j] with z hz
  intro i
  have hx := (hz (e i).1 (e i).2).1
  have hy := (hz (e i).1 (e i).2).2
  have hx' : (z (e i).1 (e i).2).2.1 ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hx
  have hy' : (z (e i).1 (e i).2).2.2 ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hy
  constructor
  · exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx')
  · exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hy')

theorem ae_circle_endpoints_ordered
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j,
      ProductModel.Ordered (circleLeftEndpoint e z) (circleRightEndpoint e z) := by
  filter_upwards [ae_circle_representatives hm hκ0 hκ ha ha' hb hb' e j,
    ae_all_coordinates_ordered hm hκ0 hκ ha ha' hb hb' j] with z hr ho
  intro i
  rw [(hr i).1, (hr i).2]
  exact ho (e i).1 (e i).2

theorem measurePreserving_toCircle : MeasurePreserving toCircle
    OrderedProductCoupling.baseMeasure ProductModel.baseMeasure := by
  have hc : MeasurePreserving (fun t : ℝ => (t : Circle))
      OneCoordinateCoupling.baseLaw circleMeasure := by
    rw [OneCoordinateCoupling.baseLaw_eq_restrict, circleMeasure,
      restrict_Ico_eq_restrict_Ioc]
    simpa only [zero_add] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  refine ⟨by unfold toCircle; fun_prop, ?_⟩
  unfold OrderedProductCoupling.baseMeasure ProductModel.baseMeasure toCircle
  rw [Measure.infinitePi_map_pi _ (fun _ => hc.measurable)]
  simp only [hc.map_eq]

theorem eventually_circle_retainedEvent_mass
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (hsq : Summable (fun s => κ s ^ 2)) (e : ℕ ≃ Σ s, Fin (m s))
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {r : ProductModel.Base → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real
        (retainedEvent m K r (circleLeftEndpoint e) (circleRightEndpoint e) j) := by
  have hir : ∀ᵐ x ∂OrderedProductCoupling.baseMeasure,
      0 < (r ∘ toCircle) x ∧ (r ∘ toCircle) x < 1 :=
    measurePreserving_toCircle.quasiMeasurePreserving.ae hi
  have h := eventually_actual_retainedEvent_mass
    (m := m) (κ := κ) (a := a) (b := b)
    hm hκ0 hκ ha ha' hb hb' hsq e hK hd hratio
    (r := r ∘ toCircle) (hr.comp measurePreserving_toCircle.measurable) hir
  simpa only [retainedEvent, circleLeftEndpoint, circleRightEndpoint,
    Function.comp_apply] using h

end Invariant233.BlockedProductCoupling

end OAI
