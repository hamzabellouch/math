import OAI.InformationTheory.Entanglement.TranscriptClassical
import OAI.InformationTheory.Entanglement.CausalPublic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory
namespace SecretKey
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {F A B : MeasurableSpace Ω}
variable (hF : F ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)

def senderMask (r : Ω → TapeRole) (q : TapeRole) (M : Ω → X) (x₀ : X) : Ω → X :=
  fun ω => if r ω=q then M ω else x₀
lemma mask_measurable {G : MeasurableSpace Ω} (r : Ω → TapeRole)
    (hr : ∀ q, MeasurableSet[G] {ω | r ω=q}) (M : Ω→X)
    (hM : Measurable[G] M) (x₀ : X) (q : TapeRole) :
    Measurable[G] (senderMask r q M x₀) := by
  exact hM.ite (hr q) measurable_const

lemma masked_record_information (r : Ω → TapeRole)
    (hr : ∀ q, MeasurableSet[F] {ω | r ω=q}) (M : Ω→X) (x₀ : X) :
    F ⊔ (inferInstance : MeasurableSpace X).comap M=
    ((F ⊔ (inferInstance : MeasurableSpace X).comap (senderMask r .source M x₀)) ⊔
      (inferInstance : MeasurableSpace X).comap (senderMask r .alice M x₀)) ⊔
      (inferInstance : MeasurableSpace X).comap (senderMask r .bob M x₀) := by
  let C := (inferInstance : MeasurableSpace X).comap M
  let S := (inferInstance : MeasurableSpace X).comap (senderMask r .source M x₀)
  let P := (inferInstance : MeasurableSpace X).comap (senderMask r .alice M x₀)
  let Q := (inferInstance : MeasurableSpace X).comap (senderMask r .bob M x₀)
  change F ⊔ C=((F ⊔ S) ⊔ P) ⊔ Q
  have hFC : F≤F ⊔ C := le_sup_left
  have hC : Measurable[F ⊔ C] M := measurable_iff_comap_le.mpr le_sup_right
  have hmask (q : TapeRole) : (inferInstance : MeasurableSpace X).comap (senderMask r q M x₀)≤F ⊔ C :=
    (mask_measurable r (fun q => hFC _ (hr q)) M hC x₀ q).comap_le
  apply le_antisymm
  · apply sup_le
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · apply Measurable.comap_le
      have hFG : F≤((F ⊔ S) ⊔ P) ⊔ Q := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
      have hS : Measurable[((F ⊔ S) ⊔ P) ⊔ Q] (senderMask r .source M x₀) :=
        measurable_iff_comap_le.mpr (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
      have hP : Measurable[((F ⊔ S) ⊔ P) ⊔ Q] (senderMask r .alice M x₀) :=
        measurable_iff_comap_le.mpr (le_sup_of_le_left le_sup_right)
      have hQ : Measurable[((F ⊔ S) ⊔ P) ⊔ Q] (senderMask r .bob M x₀) :=
        measurable_iff_comap_le.mpr le_sup_right
      have he : M=(fun ω => if r ω=.source then senderMask r .source M x₀ ω else
        if r ω=.alice then senderMask r .alice M x₀ ω else senderMask r .bob M x₀ ω) := by
        funext ω
        cases h : r ω <;> simp [senderMask,h]
      rw [he]
      exact hS.ite (hFG _ (hr .source)) (hP.ite (hFG _ (hr .alice)) hQ)
  · exact sup_le (sup_le (sup_le le_sup_left (hmask .source)) (hmask .alice)) (hmask .bob)
include hA hB in

theorem adaptive_public_step (hind : CondIndep F A B hF μ)
    (r : Ω → TapeRole) (hr : ∀ q, MeasurableSet[F] {ω | r ω=q})
    (M : Ω→X) (x₀ : X)
    (ha : Measurable[A ⊔ F] (senderMask r .alice M x₀))
    (hb : Measurable[B ⊔ F] (senderMask r .bob M x₀))
    (hs : Measurable[mΩ] (senderMask r .source M x₀))
    (hk : ∀ E, MeasurableSet E → AEStronglyMeasurable[F]
      (μ⟦senderMask r .source M x₀ ⁻¹' E | (A ⊔ B) ⊔ F⟧) μ) :
    ∃ hD : F ⊔ (inferInstance : MeasurableSpace X).comap M ≤ mΩ,
      CondIndep (F ⊔ (inferInstance : MeasurableSpace X).comap M) A B hD μ := by
  let S := (inferInstance : MeasurableSpace X).comap (senderMask r .source M x₀)
  let P := (inferInstance : MeasurableSpace X).comap (senderMask r .alice M x₀)
  let Q := (inferInstance : MeasurableSpace X).comap (senderMask r .bob M x₀)
  have hS : S ≤ mΩ := hs.comap_le
  have hP : P ≤ mΩ := ha.comap_le.trans (sup_le hA hF)
  have hQ : Q ≤ mΩ := hb.comap_le.trans (sup_le hB hF)
  have hsource : CondIndep F S (A ⊔ B) hF μ := by
    apply CondIndep.symm
    apply independent_of_public_conditional_laws hF (sup_le (sup_le hA hB) hF)
      le_sup_right le_sup_left hS
    intro E hE
    obtain ⟨s,hs,hse⟩ := hE
    rw [← hse]
    exact hk s hs
  have hiS : CondIndep (F ⊔ S) A B (sup_le hF hS) μ := by
    simpa only [sup_comm S F] using public_source_preserves_independence hF hA hB hind hS hsource
  have hiP : CondIndep ((F ⊔ S) ⊔ P) A B (sup_le (sup_le hF hS) hP) μ := by
    apply sender_message_preserves_independence (sup_le hF hS) hA hB hiS le_sup_left
    exact sup_le le_sup_right (ha.comap_le.trans (sup_le_sup_left le_sup_left A))
  have hiQ : CondIndep (((F ⊔ S) ⊔ P) ⊔ Q) A B
      (sup_le (sup_le (sup_le hF hS) hP) hQ) μ := by
    apply CondIndep.symm
    apply sender_message_preserves_independence (sup_le (sup_le hF hS) hP) hB hA hiP.symm le_sup_left
    exact sup_le le_sup_right (hb.comap_le.trans
      (sup_le_sup_left (le_sup_of_le_left le_sup_left) B))
  rw [masked_record_information r hr M x₀]
  exact ⟨sup_le (sup_le (sup_le hF hS) hP) hQ,hiQ⟩

end SecretKey

end

end OAI
