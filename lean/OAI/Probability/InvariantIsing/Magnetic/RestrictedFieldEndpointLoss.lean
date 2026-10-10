import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldFactorization
import OAI.Probability.InvariantIsing.Fields.FieldEndpointIntegrability
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldStepLoss

namespace OAI

/-! Iterating the canonical one-step inequality carries the constrained
recursion loss to the actual terminal endpoint law, with no depth factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma linearGrowth_difference {E : Type*} [SeminormedAddCommGroup E]
    {F G : E → ℝ} (hF : HasLinearGrowth F) (hG : HasLinearGrowth G) :
    HasLinearGrowth (fun x => F x - G x) := by
  obtain ⟨C, L, hC, hL, hF⟩ := hF
  obtain ⟨D, K, hD, hK, hG⟩ := hG
  refine ⟨C + D, L + K, by positivity, by positivity, fun x => ?_⟩
  calc
    _ ≤ |F x| + |G x| := abs_sub _ _
    _ ≤ (C + L * ‖x‖) + (D + K * ‖x‖) := add_le_add (hF x) (hG x)
    _ = _ := by ring

lemma restrictedFieldTerminal_loss_regular {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Measurable (fun z => restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z) ∧
      HasLinearGrowth (fun z => restrictedFieldTerminal Finset.univ z - restrictedFieldTerminal S z) :=
  ⟨(continuous_restrictedFieldTerminal Finset.univ Finset.univ_nonempty).measurable.sub
      (continuous_restrictedFieldTerminal S hS).measurable,
    linearGrowth_difference (restrictedFieldTerminal_linearGrowth Finset.univ Finset.univ_nonempty)
      (restrictedFieldTerminal_linearGrowth S hS)⟩

theorem restrictedFieldRecursion_endpoint_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (hb1 : ∀ i < n, b i ≤ 1) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ n b v z - restrictedFieldRecursion S n b v z ≤
      ∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
        ∂fieldVectorTailEndpointKernel N (List.ofFn (fun i : Fin n => (b i, v i)))
          (by
            intro av hav
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
            exact hb i i.isLt) z := by
  induction n generalizing b v z with
  | zero =>
    simp only [List.ofFn_zero, fieldVectorTailEndpointKernel, Kernel.id_apply, integral_dirac]
    exact le_rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let L := List.ofFn (fun i : Fin n => (bs i, vs i))
    have hbs : ∀ i < n, 0 < bs i := fun i hi => hb (i + 1) (by omega)
    have hbs1 : ∀ i < n, bs i ≤ 1 := fun i hi => hb1 (i + 1) (by omega)
    have hL : ∀ av ∈ L, 0 < av.1 := by
      intro av hav
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
      exact hbs i i.isLt
    have hL1 : ∀ av ∈ L, av.1 ≤ 1 := by
      intro av hav
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
      exact hbs1 i i.isLt
    let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
    have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
    let κ := fieldVectorTransitionKernel N (b 0) (v 0) F hF.1
    let η := fieldVectorTailEndpointKernel N L hL
    let D := fun y => restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
    have hD := restrictedFieldTerminal_loss_regular S hS
    have hInt : Integrable D ((η ∘ₖ κ) z) := by
      have hfull : ∀ av ∈ (b 0, v 0) :: L, 0 < av.1 := by
        simpa only [List.forall_mem_cons] using And.intro (hb 0 (by omega)) hL
      have hfull1 : ∀ av ∈ (b 0, v 0) :: L, av.1 ≤ 1 := by
        simpa only [List.forall_mem_cons] using And.intro (hb1 0 (by omega)) hL1
      exact fieldVectorTailEndpointKernel_integrable N _ hfull hfull1 z D hD.1 hD.2
    have hOuter : Integrable (fun y => ∫ w, D w ∂η y) (κ z) := hInt.integral_comp
    let d := fun y => restrictedFieldRecursion Finset.univ n bs vs y -
      restrictedFieldRecursion S n bs vs y
    have hregF := restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs
    have hregS := restrictedFieldRecursion_regular hN S hS n bs vs hbs
    have hdM : Measurable d := hregF.1.sub hregS.1
    let μ := (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted
      (fun w => b 0 * restrictedFieldRecursion Finset.univ n bs vs (z + w))
    have hmap : μ.map (fun w => z + w) = κ z := by
      have he : (fun w => b 0 * restrictedFieldRecursion Finset.univ n bs vs (z + w)) =
          (fun w => b 0 * ∑ i, F ((z + w) i)) := by
        funext w
        rw [restrictedFieldRecursion_univ n bs vs hbs]
      change ((vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).tilted _).map _ = _
      rw [he]
      exact vectorGaussian_tilt_transition (b 0) (v 0) F hF.1 hF.2 z
    have hdInt : Integrable d (κ z) := by
      rw [← hmap]
      apply (integrable_map_measure hdM.aestronglyMeasurable
        (measurable_const.add measurable_id).aemeasurable).mpr
      exact (restrictedFieldRecursion_tilt_integrable hN Finset.univ Finset.univ
        Finset.univ_nonempty Finset.univ_nonempty n bs vs hbs (v 0) (b 0) z).sub
        (restrictedFieldRecursion_tilt_integrable hN Finset.univ S
          Finset.univ_nonempty hS n bs vs hbs (v 0) (b 0) z)
    have hm : (∫ w, d (z + w) ∂μ) = ∫ y, d y ∂κ z := by
      rw [← hmap]
      exact (integral_map (show AEMeasurable (fun w : Fin N → ℝ => z + w) μ from
        (measurable_const.add measurable_id).aemeasurable) hdM.aestronglyMeasurable).symm
    calc
      _ ≤ ∫ w, d (z + w) ∂μ := restrictedFieldRecursion_step_loss hN S hS n b v hb z
      _ = ∫ y, d y ∂κ z := hm
      _ ≤ ∫ y, ∫ w, D w ∂η y ∂κ z := by
        apply integral_mono hdInt hOuter
        intro y
        exact ih bs vs hbs hbs1 y
      _ = ∫ y, D y ∂(η ∘ₖ κ) z := (Kernel.integral_comp hInt).symm
      _ = _ := by
        simp only [List.ofFn_succ, fieldVectorTailEndpointKernel]
        rfl

end InvariantIsing

end

end OAI
