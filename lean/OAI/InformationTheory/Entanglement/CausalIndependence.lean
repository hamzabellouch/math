import OAI.InformationTheory.Entanglement.CausalPublic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MeasurableSpace X]
variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X)
variable (g : (k : ℕ) → (Fin k → X) → I → X)
variable (hg : ∀ k, Measurable (uncurry (g k)))
def causalPublicFiltration : Filtration ℕ (inferInstance : MeasurableSpace (UniformTapes ℕ)) where
  seq := causalPublicInfo role pub x₀ g
  mono' := causalPublicInfo_mono role pub x₀ g
  le' := causalPublicInfo_le role pub x₀ g hg
lemma causalPublic_zero : causalPublicInfo role pub x₀ g 0=⊥ := by
  apply le_bot_iff.mp
  let : MeasurableSpace (UniformTapes ℕ) := ⊥
  have he : causalPublic role pub x₀ g 0=(fun _ => (Fin.elim0 : Fin 0 → X)) := by
    funext ω i; exact Fin.elim0 i
  change (inferInstance : MeasurableSpace (Fin 0→X)).comap _ ≤ _
  rw [he]
  exact (measurable_const : Measurable (fun _ : UniformTapes ℕ => (Fin.elim0 : Fin 0 → X))).comap_le
include hg in
lemma causal_initial_independence :
    CondIndep (causalPublicInfo role pub x₀ g 0) (roleInfo role .alice) (roleInfo role .bob)
      (causalPublicInfo_le role pub x₀ g hg 0) uniformTapesLaw := by
  apply initial_uniform_tape_independence (c := ∅)
  · apply Set.disjoint_left.mpr
    intro k hb ha
    simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_empty_iff_false,or_false] at ha
    have h : TapeRole.alice=TapeRole.bob := ha.symm.trans hb
    cases h
  · rw [causalPublic_zero]
    exact bot_le
include hg in
lemma causal_public_steps (hsource : ∀ k, role k=.source → k∈pub)
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (g k s)=κ k s) (k : ℕ) :
    TapePublicStep uniformTapesLaw (roleInfo role .alice) (roleInfo role .bob)
      (causalPublicInfo role pub x₀ g k) (causalPublicInfo role pub x₀ g (k+1))
      (causalPublicInfo_le role pub x₀ g hg k) := by
  cases hr : role k with
  | alice =>
    exact Or.inl (by simpa only [hr] using causalPublic_succ_local role pub x₀ g hg k)
  | bob =>
    exact Or.inr (Or.inl (by simpa only [hr] using causalPublic_succ_local role pub x₀ g hg k))
  | source => exact causal_source_step role pub x₀ g hg hsource κ hmap k hr

def completeCausalPublic (ω : UniformTapes ℕ) (k : ℕ) : X :=
  if k∈pub then sampledHistory (causalSampler role pub x₀ g) ω k else x₀
def completeCausalView (r : TapeRole) (ω : UniformTapes ℕ) (k : ℕ) : X :=
  if role k=r ∨ k∈pub then sampledHistory (causalSampler role pub x₀ g) ω k else x₀
omit [MeasurableSpace X] in
lemma completeCausalPublic_prefix (k : ℕ) (ω : UniformTapes ℕ) :
    causalPublic role pub x₀ g k ω=recordPrefix k (completeCausalPublic role pub x₀ g ω) := by
  funext i
  simp only [causalPublic,publicPrefix,recordPrefix,completeCausalPublic,sampledPrefix_eq]
omit [MeasurableSpace X] in
lemma completeCausalPublic_last (k : ℕ) (ω : UniformTapes ℕ) :
    causalPublic role pub x₀ g (k+1) ω (Fin.last k)=completeCausalPublic role pub x₀ g ω k := by
  rw [completeCausalPublic_prefix]
  rfl
include hg in
lemma completeCausalPublic_measurable : Measurable (completeCausalPublic role pub x₀ g) := by
  apply Measurable.of_eval
  intro k
  have he : (fun ω => completeCausalPublic role pub x₀ g ω k)=
      (fun ω => causalPublic role pub x₀ g (k+1) ω (Fin.last k)) :=
    funext fun ω => (completeCausalPublic_last role pub x₀ g k ω).symm
  rw [he]
  exact (measurable_pi_apply (Fin.last k)).comp (causalPublic_measurable role pub x₀ g hg (k+1))
lemma completeCausalPublic_information :
    (inferInstance : MeasurableSpace (ℕ → X)).comap (completeCausalPublic role pub x₀ g)=
      ⨆ k, causalPublicInfo role pub x₀ g k := by
  apply le_antisymm
  · let : MeasurableSpace (UniformTapes ℕ) := ⨆ k, causalPublicInfo role pub x₀ g k
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro k
    have he : (fun ω => completeCausalPublic role pub x₀ g ω k)=
        (fun ω => causalPublic role pub x₀ g (k+1) ω (Fin.last k)) :=
      funext fun ω => (completeCausalPublic_last role pub x₀ g k ω).symm
    rw [he]
    exact ((measurable_pi_apply (Fin.last k)).comp (causalPublic_own_measurable role pub x₀ g (k+1))).mono (le_iSup _ (k+1)) le_rfl
  · apply iSup_le
    intro k
    let : MeasurableSpace (UniformTapes ℕ) :=
      (inferInstance : MeasurableSpace (ℕ → X)).comap (completeCausalPublic role pub x₀ g)
    have hm : Measurable (completeCausalPublic role pub x₀ g) := measurable_iff_comap_le.mpr le_rfl
    have he : causalPublic role pub x₀ g k=recordPrefix k ∘ completeCausalPublic role pub x₀ g :=
      funext (completeCausalPublic_prefix role pub x₀ g k)
    exact (congrArg (fun f => (inferInstance : MeasurableSpace (Fin k→X)).comap f) he).le.trans
      ((recordPrefix_measurable k).comp hm).comap_le
include hg in
lemma completeCausalView_local (r : TapeRole) :
    Measurable[roleInfo role r ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g)]
      (completeCausalView role pub x₀ g r) := by
  rw [completeCausalPublic_information]
  let : MeasurableSpace (UniformTapes ℕ) := roleInfo role r ⊔ ⨆ k,causalPublicInfo role pub x₀ g k
  apply Measurable.of_eval
  intro k
  have he : (fun ω => completeCausalView role pub x₀ g r ω k)=
      (fun ω => causalVisible role pub x₀ g r (k+1) ω (Fin.last k)) := by
    funext ω
    simp [completeCausalView,causalVisible,visiblePrefix,sampledPrefix_succ,sampledHistory]
  rw [he]
  exact ((measurable_pi_apply (Fin.last k)).comp (causalVisible_local role pub x₀ g hg r (k+1))).mono
    (sup_le_sup_left (le_iSup _ (k+1)) _) le_rfl

theorem causal_complete_independence (hsource : ∀ k, role k=.source → k∈pub)
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (g k s)=κ k s) :
    CondIndep ((inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
      (roleInfo role .alice ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
      (roleInfo role .bob ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
      (completeCausalPublic_measurable role pub x₀ g hg).comap_le uniformTapesLaw := by
  simpa only [completeCausalPublic_information,causalPublicFiltration] using tapes_independent_given_complete_public uniformTapesLaw _ _ (roleInfo_le role .alice)
    (roleInfo_le role .bob) (causalPublicFiltration role pub x₀ g hg)
    (causal_initial_independence role pub x₀ g hg)
    (causal_public_steps role pub x₀ g hg hsource κ hmap)

end SecretKey

end

end OAI
