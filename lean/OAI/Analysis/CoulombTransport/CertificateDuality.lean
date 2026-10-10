import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uAlpha

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356.Certificate

/-- An integrable signed lower certificate bounds a nonnegative extended integral. -/
theorem ofReal_integral_le_lintegral {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {g : α → ℝ≥0∞}
    (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤ g x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, g x ∂μ := by
  by_cases htop : (∫⁻ x, g x ∂μ) = ⊤
  · simp [htop]
  have hgfin := ae_lt_top' hg htop
  have hgi := integrable_toReal_of_lintegral_ne_top hg htop
  have hreal : f ≤ᵐ[μ] fun x => (g x).toReal := by
    filter_upwards [hle, hgfin] with x hx hxfin
    exact (ENNReal.ofReal_le_iff_le_toReal hxfin.ne).mp hx
  calc
    ENNReal.ofReal (∫ x, f x ∂μ) ≤
        ENNReal.ofReal (∫ x, (g x).toReal ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono_ae hf hgi hreal)
    _ = ∫⁻ x, g x ∂μ := by
      rw [integral_toReal hg hgfin, ENNReal.ofReal_toReal htop]

/-- Equality with a signed lower certificate forces pointwise equality almost everywhere. -/
theorem ae_eq_of_integral_certificate {α : Type uAlpha} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {g : α → ℝ≥0∞}
    (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hle : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) ≤ g x)
    (hnonneg : 0 ≤ ∫ x, f x ∂μ)
    (heq : (∫⁻ x, g x ∂μ) = ENNReal.ofReal (∫ x, f x ∂μ)) :
    ∀ᵐ x ∂μ, g x = ENNReal.ofReal (f x) := by
  have htop : (∫⁻ x, g x ∂μ) ≠ ⊤ := by
    rw [heq]
    exact ENNReal.ofReal_ne_top
  have hgfin := ae_lt_top' hg htop
  have hgi := integrable_toReal_of_lintegral_ne_top hg htop
  have hreal : f ≤ᵐ[μ] fun x => (g x).toReal := by
    filter_upwards [hle, hgfin] with x hx hxfin
    exact (ENNReal.ofReal_le_iff_le_toReal hxfin.ne).mp hx
  have hint : (∫ x, f x ∂μ) = ∫ x, (g x).toReal ∂μ := by
    rw [integral_toReal hg hgfin, heq, ENNReal.toReal_ofReal hnonneg]
  have hae := (integral_eq_iff_of_ae_le hf hgi hreal).mp hint
  filter_upwards [hae, hgfin] with x hx hxfin
  rw [hx, ENNReal.ofReal_toReal hxfin.ne]

/-- The signed three-coordinate dual potential associated with one marginal potential. -/
def potentialSum (u : E3 → ℝ) (t : Triple) : ℝ :=
  u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)

private theorem first_measurable : Measurable tripleFst := measurable_fst
private theorem second_measurable : Measurable tripleSnd := measurable_fst.comp measurable_snd
private theorem third_measurable : Measurable tripleThd := measurable_snd.comp measurable_snd

/-- Marginal identities transfer integrability of a signed potential to its sum. -/
theorem integrable_potentialSum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ} (hu : Integrable u μ) :
    Integrable (potentialSum u) π := by
  have h₁ : MeasurePreserving tripleFst π μ := ⟨first_measurable, hπ.2.1⟩
  have h₂ : MeasurePreserving tripleSnd π μ := ⟨second_measurable, hπ.2.2.1⟩
  have h₃ : MeasurePreserving tripleThd π μ := ⟨third_measurable, hπ.2.2.2⟩
  exact ((h₁.integrable_comp hu.aestronglyMeasurable).mpr hu |>.add
    ((h₂.integrable_comp hu.aestronglyMeasurable).mpr hu)).add
    ((h₃.integrable_comp hu.aestronglyMeasurable).mpr hu)

/-- The integral of a common potential sum depends only on the common marginal. -/
theorem integral_potentialSum {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ} (hu : Integrable u μ) :
    (∫ t, potentialSum u t ∂π) = 3 * ∫ x, u x ∂μ := by
  have h₁ : MeasurePreserving tripleFst π μ := ⟨first_measurable, hπ.2.1⟩
  have h₂ : MeasurePreserving tripleSnd π μ := ⟨second_measurable, hπ.2.2.1⟩
  have h₃ : MeasurePreserving tripleThd π μ := ⟨third_measurable, hπ.2.2.2⟩
  have hi₁ := (h₁.integrable_comp hu.aestronglyMeasurable).mpr hu
  have hi₂ := (h₂.integrable_comp hu.aestronglyMeasurable).mpr hu
  have hi₃ := (h₃.integrable_comp hu.aestronglyMeasurable).mpr hu
  have he₁ : (∫ t, u (tripleFst t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.1]
    exact (integral_map first_measurable.aemeasurable (by rw [hπ.2.1]; exact hu.aestronglyMeasurable)).symm
  have he₂ : (∫ t, u (tripleSnd t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.2.1]
    exact (integral_map second_measurable.aemeasurable (by rw [hπ.2.2.1]; exact hu.aestronglyMeasurable)).symm
  have he₃ : (∫ t, u (tripleThd t) ∂π) = ∫ x, u x ∂μ := by
    rw [← hπ.2.2.2]
    exact (integral_map third_measurable.aemeasurable (by rw [hπ.2.2.2]; exact hu.aestronglyMeasurable)).symm
  calc
    (∫ t, potentialSum u t ∂π) =
        (∫ t, u (tripleFst t) + u (tripleSnd t) ∂π) +
        ∫ t, u (tripleThd t) ∂π := integral_add (hi₁.add hi₂) hi₃
    _ = ((∫ t, u (tripleFst t) ∂π) + (∫ t, u (tripleSnd t) ∂π)) +
        ∫ t, u (tripleThd t) ∂π := by
      congr 1
      exact integral_add hi₁ hi₂
    _ = 3 * ∫ x, u x ∂μ := by rw [he₁, he₂, he₃]; ring

private theorem cost_measurable : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

/-- Every coupling is concentrated on the cube of any full-marginal-mass set. -/
theorem coupling_ae_mem {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U) :
    ∀ᵐ t ∂π, tripleFst t ∈ U ∧ tripleSnd t ∈ U ∧ tripleThd t ∈ U := by
  have h₁ : ∀ᵐ t ∂π, tripleFst t ∈ U :=
    ae_of_ae_map first_measurable.aemeasurable (by rwa [hπ.2.1])
  have h₂ : ∀ᵐ t ∂π, tripleSnd t ∈ U :=
    ae_of_ae_map second_measurable.aemeasurable (by rwa [hπ.2.2.1])
  have h₃ : ∀ᵐ t ∂π, tripleThd t ∈ U :=
    ae_of_ae_map third_measurable.aemeasurable (by rwa [hπ.2.2.2])
  filter_upwards [h₁, h₂, h₃] with t ht₁ ht₂ ht₃
  exact ⟨ht₁, ht₂, ht₃⟩

/-- A signed supporting potential on a full-mass region is a Kantorovich lower bound. -/
theorem kantorovich_lower_bound {μ : Measure E3} {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t) :
    ENNReal.ofReal (3 * ∫ x, u x ∂μ) ≤ kantorovichValue μ := by
  apply le_iInf
  intro π
  apply le_iInf
  intro hπ
  rw [← integral_potentialSum hπ hu]
  apply ofReal_integral_le_lintegral (integrable_potentialSum hπ hu)
    cost_measurable.aemeasurable
  filter_upwards [coupling_ae_mem hπ hU] with t ht
  exact hcert t ht.1 ht.2.1 ht.2.2

/-- An explicit finite plan saturating a supporting potential is an optimizer. -/
theorem optimal_plan_of_certificate {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t)
    (heq : (∫⁻ t, coulombCost t ∂π) = ENNReal.ofReal (3 * ∫ x, u x ∂μ)) :
    (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ ∧
      kantorovichValue μ < ⊤ ∧ KantorovichAttained μ := by
  have hlower := kantorovich_lower_bound hu hU hcert
  have hupper : kantorovichValue μ ≤ ∫⁻ t, coulombCost t ∂π :=
    iInf_le_of_le π (iInf_le_of_le hπ le_rfl)
  have hvalue : (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ :=
    le_antisymm (heq ▸ hlower) hupper
  refine ⟨hvalue, ?_, ⟨π, hπ, hvalue⟩⟩
  rw [← hvalue, heq]
  exact ENNReal.ofReal_lt_top

/-- Every optimal finite plan must lie on the equality set of a supporting potential. -/
theorem optimal_ae_contact {μ : Measure E3} {π : Measure Triple}
    (hπ : IsThreeCoupling μ π) {u : E3 → ℝ}
    (hu : Integrable u μ) {U : Set E3} (hU : ∀ᵐ x ∂μ, x ∈ U)
    (hcert : ∀ t : Triple, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (potentialSum u t) ≤ coulombCost t)
    (hnonneg : 0 ≤ 3 * ∫ x, u x ∂μ)
    (hvalue : kantorovichValue μ = ENNReal.ofReal (3 * ∫ x, u x ∂μ))
    (hopt : (∫⁻ t, coulombCost t ∂π) = kantorovichValue μ) :
    ∀ᵐ t ∂π, coulombCost t = ENNReal.ofReal (potentialSum u t) := by
  apply ae_eq_of_integral_certificate (integrable_potentialSum hπ hu)
    cost_measurable.aemeasurable
  · filter_upwards [coupling_ae_mem hπ hU] with t ht
    exact hcert t ht.1 ht.2.1 ht.2.2
  · rwa [integral_potentialSum hπ hu]
  · rw [integral_potentialSum hπ hu, hopt, hvalue]

end Problem356.Certificate

end

end OAI
