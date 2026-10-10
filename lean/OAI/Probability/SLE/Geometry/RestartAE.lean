import OAI.Probability.SLE.Geometry.RandomRestartEvents

namespace OAI

/-! A measurable family of full fresh-law events remains almost sure when
its parameter is selected from the original stopped past. -/

noncomputable section
open Set Filter MeasureTheory

namespace SLEExactGauge

theorem restart_ae_random_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (R : Ω × X → Prop) (hR : @MeasurableSet (Ω × X) (m.prod mX) {p | R p})
    (hsections : ∀ ω, ∀ᵐ x ∂ν, R (ω,x)) : ∀ᵐ ω ∂P, R (ω,Y ω) := by
  have hprod : ∀ᵐ p ∂@Measure.prod Ω X m mX (P.trim hm) ν, R p :=
    (Measure.ae_prod_iff_ae_ae hR).mpr (Eventually.of_forall hsections)
  rw [← @restart_joint_law Ω X mΩ mX P inferInstance ν inferInstance m hm Y hY hlaw] at hprod
  have hj : @Measurable Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω,Y ω)) :=
    (measurable_id'' hm).prodMk hY
  exact (ae_map_iff hj.aemeasurable hR).mp hprod

end SLEExactGauge

end

end OAI
