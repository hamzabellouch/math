import OAI.Probability.FreeIsing.Estimates.IndependentLabelSampler
import OAI.Probability.FreeIsing.Factors.ZeroFactor
import OAI.Probability.FreeIsing.Ising.ParameterRange
import OAI.Probability.FreeIsing.Spins.ProductLaw

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem IsFactorOfIID.mul_of_bounds {d : ℕ} {a b : ℝ}
    (hfa : IsFactorOfIID d a) (hfb : IsFactorOfIID d b)
    (ha0 : -1 ≤ a) (ha1 : a ≤ 1) (hb0 : -1 ≤ b) (hb1 : b ≤ 1) :
    IsFactorOfIID d (a * b) := by
  obtain ⟨F, hF, hFlaw, hFeq⟩ := hfa
  obtain ⟨G, hG, hGlaw, hGeq⟩ := hfb
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  let H := fun p : (TreeVertex d → ℝ) × (TreeVertex d → ℝ) =>
    spinProduct (F p.1, G p.2)
  have hH : Measurable H := measurable_spinProduct.comp (hF.prodMap hG)
  apply isFactorOfIID_of_independent_product_inputs uniform01 uniform01 H hH
  · change HasFreeIsingLaw (a * b) (((labelMeasure d).prod (labelMeasure d)).map H)
    have hmap : ((labelMeasure d).prod (labelMeasure d)).map H =
        (((labelMeasure d).map F).prod ((labelMeasure d).map G)).map spinProduct := by
      rw [Measure.map_prod_map _ _ hF hG,
        Measure.map_map measurable_spinProduct (hF.prodMap hG)]
      rfl
    rw [hmap]
    exact hFlaw.mul_product hGlaw ha0 ha1 hb0 hb1
  · intro g
    change ∀ᵐ p ∂(labelMeasure d).prod (labelMeasure d),
      H (relabel g p.1, relabel g p.2) = relabel g (H p)
    have hfirst : ∀ᵐ p ∂(labelMeasure d).prod (labelMeasure d),
        F (relabel g p.1) = relabel g (F p.1) := by
      apply ae_of_ae_map (p := fun x => F (relabel g x) = relabel g (F x))
        measurable_fst.aemeasurable
      simpa using hFeq g
    have hsecond : ∀ᵐ p ∂(labelMeasure d).prod (labelMeasure d),
        G (relabel g p.2) = relabel g (G p.2) := by
      apply ae_of_ae_map (p := fun x => G (relabel g x) = relabel g (G x))
        measurable_snd.aemeasurable
      simpa using hGeq g
    filter_upwards [hfirst, hsecond] with p hp hq
    change spinProduct (F (relabel g p.1), G (relabel g p.2)) = _
    rw [hp, hq, spinProduct_relabel]

theorem isFactorOfIID_degree_zero (theta : ℝ) : IsFactorOfIID 0 theta := by
  obtain ⟨F, hF, hLaw, hEquiv⟩ := isFactorOfIID_zero 0
  refine ⟨F, hF, ?_, hEquiv⟩
  intro D hD eta
  rw [hLaw D hD eta]
  have hadj (u v : TreeVertex 0) : ¬treeAdj u v := by
    rintro (⟨c, _⟩ | ⟨c, _⟩) <;> exact Fin.elim0 c
  have hedge : inducedEdges D = ∅ := by
    classical
    simp [inducedEdges, hadj]
  simp [freeCylinderWeight, hedge]

theorem IsFactorOfIID.mul {d : ℕ} {a b : ℝ}
    (hfa : IsFactorOfIID d a) (hfb : IsFactorOfIID d b) :
    IsFactorOfIID d (a * b) := by
  by_cases hd : d = 0
  · subst d
    exact isFactorOfIID_degree_zero _
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have ha := hfa.parameter_mem_Icc hdpos
    have hb := hfb.parameter_mem_Icc hdpos
    exact hfa.mul_of_bounds hfb ha.1 ha.2 hb.1 hb.2

end Problem367

end

end OAI
