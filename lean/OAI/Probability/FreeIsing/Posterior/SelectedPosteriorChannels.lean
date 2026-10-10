import OAI.Probability.FreeIsing.Energy.Attenuation
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_selectedPosterior_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      ∀ p, selectedPosterior rho F v r p =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  have hm : Measurable[selectedObservationField F v]
      (selectedPosterior rho F v r) := stronglyMeasurable_condExp.measurable
  obtain ⟨g, hg, heq⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg, fun p => congrFun heq p⟩

theorem exists_selectedAttenuation_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta (Real.artanh (selectedPosterior rho F v r p)) ^ 2 =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  obtain ⟨f, hf, heq⟩ := exists_selectedPosterior_channel rho F v r
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hat : Measurable (responseAttenuation theta) := by
    unfold responseAttenuation
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  refine ⟨fun x => responseAttenuation theta (Real.artanh (f x)) ^ 2,
    ((hat.comp (ha.comp hf)).pow_const 2),
    ?_, ?_⟩
  · intro x
    refine ⟨sq_nonneg _, ?_⟩
    have hpos := responseAttenuation_pos hθ (Real.artanh (f x))
    have hone := responseAttenuation_le_one hθ (Real.artanh (f x))
    nlinarith
  · intro p
    rw [heq p]

theorem exists_selectedAttenuation_local_channel
    {d : ℕ} {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : κ → TreeVertex d) (j : ι → κ) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : ((κ → IsingSpin) × (κ → A)) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta
          (Real.artanh (selectedPosterior rho F (v ∘ j) r p)) ^ 2 =
        g (fun k => p.1 (v k), fun k => p.2 (v k)) := by
  obtain ⟨f, hf, hbound, heq⟩ := exists_selectedAttenuation_channel rho F (v ∘ j) r hθ
  let obs : ((κ → IsingSpin) × (κ → A)) → (ι → B) :=
    fun x i => F (x.1 (j i)) (x.2 (j i))
  have hobs : Measurable obs := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun x : (κ → IsingSpin) × (κ → A) =>
      (x.1 (j i), x.2 (j i))) by fun_prop)
  refine ⟨f ∘ obs, hf.comp hobs, fun x => hbound (obs x), ?_⟩
  intro p
  exact heq p

end Problem367

end

end OAI
