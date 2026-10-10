import OAI.Geometry.RCD.Transport.CompactDualCost

namespace OAI

/-! # Every cost-minimizing coupling saturates the same dual pair -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]

theorem compact_dual_saturation_of_cost_le (Q P : Measure (X × Y))
    (hQl : Q.map Prod.fst=μ) (hQr : Q.map Prod.snd=ν)
    (hPl : P.map Prod.fst=μ) (hPr : P.map Prod.snd=ν)
    (f : C(X,ℝ)) (g : C(Y,ℝ)) (cost : C(X × Y,ℝ)) (c : ℝ)
    (hdual : ∀ x y, y ∈ ν.support → f x+g y+c ≤ cost (x,y))
    (heq : ∀ᵐ z ∂Q, f z.1+g z.2+c=cost z)
    (hcost : (∫ z, cost z ∂P) ≤ ∫ z, cost z ∂Q) :
    ∀ᵐ z ∂P, f z.1+g z.2+c=cost z := by
  let : IsProbabilityMeasure (P.map Prod.fst) := by rw [hPl]; infer_instance
  let : IsProbabilityMeasure P := Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable
  let pot : C(X × Y,ℝ) := ⟨fun z => f z.1+g z.2+c,by fun_prop⟩
  have hQi : (∫ z, cost z ∂Q)=(∫ x, f x ∂μ)+(∫ y, g y ∂ν)+c := by
    calc
      _ = ∫ z, f z.1+g z.2+c ∂Q := integral_congr_ae (by
        filter_upwards [heq] with z hz
        exact hz.symm)
      _ = _ := coupling_potential_integral μ ν Q hQl hQr f g c
  have hPi : (∫ z, pot z ∂P)=(∫ x, f x ∂μ)+(∫ y, g y ∂ν)+c :=
    coupling_potential_integral μ ν P hPl hPr f g c
  have hi : Integrable cost P := cost.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hp : Integrable pot P := pot.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hnonneg : ∀ᵐ z ∂P, 0 ≤ cost z-pot z := by
    filter_upwards [coupling_snd_support (ν := ν) (π := P) hPr] with z hz
    exact sub_nonneg.mpr (hdual z.1 z.2 hz)
  have hzero : (∫ z, cost z-pot z ∂P)=0 := by
    apply le_antisymm
    · rw [integral_sub (f := fun z : X × Y => cost z) (g := fun z : X × Y => pot z) hi hp,hPi]
      rw [hQi] at hcost
      linarith
    · exact integral_nonneg_of_ae hnonneg
  have hh := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hi.sub hp)).mp hzero
  filter_upwards [hh] with z hz
  change cost z-pot z=0 at hz
  change pot z=cost z
  linarith

end RegularPointCoordinates

end

end OAI
