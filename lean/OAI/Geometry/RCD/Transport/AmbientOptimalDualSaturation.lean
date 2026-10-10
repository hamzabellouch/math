import OAI.Geometry.RCD.Transport.OptimalDualSaturation
import OAI.Geometry.RCD.Transport.CompactCouplingAmbientCost

namespace OAI

/-! # The same dual pair calibrates every ambient optimal coupling -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {S T : Set X} [CompactSpace S] [CompactSpace T]

theorem ambient_optimal_dual_saturation (hS : MeasurableSet S) (hT : MeasurableSet T)
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (S × T)) [IsProbabilityMeasure Q]
    (hQl : Q.map Prod.fst=μ) (hQr : Q.map Prod.snd=ν)
    (f : C(S,ℝ)) (g : C(T,ℝ)) (c : ℝ)
    (hdual : ∀ a b, b ∈ ν.support → f a+g b+c ≤ dist (a : X) (b : X)^2)
    (heq : ∀ᵐ z ∂Q, f z.1+g z.2+c=dist (z.1 : X) (z.2 : X)^2)
    (P : Measure (X × X)) (hP : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val) P) :
    ∃ L : Measure (S × T), L.map (Prod.map Subtype.val Subtype.val)=P ∧
      L.map Prod.fst=μ ∧ L.map Prod.snd=ν ∧
      ∀ᵐ z ∂L, f z.1+g z.2+c=dist (z.1 : X) (z.2 : X)^2 := by
  let cost : C(S × T,ℝ) := ⟨fun z => dist (z.1 : X) (z.2 : X)^2,by fun_prop⟩
  have hmin := compact_dual_cost_minimizer μ ν Q hQl hQr f g cost c hdual heq
  have hQ := compact_coupling_ambient_optimal hS hT μ ν Q hQl hQr hmin
  obtain ⟨L,hL,hLl,hLr⟩ := coupling_lift_subtypes hS hT μ ν P hP.1 hP.2.1
  let : IsProbabilityMeasure (L.map Prod.fst) := by rw [hLl]; infer_instance
  let : IsProbabilityMeasure L := Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  have hle := hP.2.2 _ hQ.1 hQ.2.1
  rw [← hL,compact_coupling_transportCost L,compact_coupling_transportCost Q] at hle
  have hcost : (∫ z, cost z ∂L) ≤ ∫ z, cost z ∂Q :=
    (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)).mp hle
  exact ⟨L,hL,hLl,hLr,compact_dual_saturation_of_cost_le μ ν Q L hQl hQr hLl hLr
    f g cost c hdual heq hcost⟩

end RegularPointCoordinates

end

end OAI
