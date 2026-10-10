import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iIndepFun_option_of_indep_tuple
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {B : Option ι → Type*} [∀ i, MeasurableSpace (B i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ∀ i, Ω → B i} (hX : ∀ i, Measurable (X i))
    (hchildren : iIndepFun (fun i => X (some i)) μ)
    (hown : IndepFun (X none) (fun ω i => X (some i) ω) μ) :
    iIndepFun X μ := by
  have hm : Measurable (fun ω i => X (some i) ω) :=
    Measurable.of_eval fun i => hX (some i)
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mpr
  calc
    μ.map (fun ω i => X i ω) =
        (μ.map (fun ω => ((fun i => X (some i) ω), X none ω))).map
          (MeasurableEquiv.piOptionEquivProd B).symm := by
      rw [Measure.map_map (MeasurableEquiv.measurable _) (hm.prodMk (hX none))]
      congr 1
      funext ω i
      cases i <;> rfl
    _ = ((Measure.pi fun i => μ.map (X (some i))).prod (μ.map (X none))).map
        (MeasurableEquiv.piOptionEquivProd B).symm := by
      rw [hown.symm.map_prod_eq_prod_map_map hm.aemeasurable (hX none).aemeasurable,
        hchildren.map_fun_eq_pi_map (fun i => (hX (some i)).aemeasurable)]
    _ = _ := Measure.pi_map_piOptionEquivProd (fun i => μ.map (X i))

end Problem367

end

end OAI
