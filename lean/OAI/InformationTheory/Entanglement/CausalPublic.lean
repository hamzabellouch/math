import OAI.InformationTheory.Entanglement.CausalSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
attribute [local instance] Classical.propDecidable
variable {Ω X : Type*} [MeasurableSpace X]
lemma snoc_information (k : ℕ) (P : Ω → Fin k → X) (C : Ω → X) :
    (inferInstance : MeasurableSpace (Fin (k+1) → X)).comap (fun ω => Fin.snoc (P ω) (C ω))=
      (inferInstance : MeasurableSpace (Fin k → X)).comap P ⊔
      (inferInstance : MeasurableSpace X).comap C := by
  let Y : Ω → (Fin (k+1) → X) := fun ω => Fin.snoc (P ω) (C ω)
  apply le_antisymm
  · let : MeasurableSpace Ω := (inferInstance : MeasurableSpace (Fin k → X)).comap P ⊔
      (inferInstance : MeasurableSpace X).comap C
    have hp : Measurable P := measurable_iff_comap_le.mpr le_sup_left
    have hc : Measurable C := measurable_iff_comap_le.mpr le_sup_right
    exact ((snoc_measurable k).comp (hp.prodMk hc)).comap_le
  · let : MeasurableSpace Ω := (inferInstance : MeasurableSpace (Fin (k+1) → X)).comap Y
    have hy : Measurable Y := measurable_iff_comap_le.mpr le_rfl
    apply sup_le
    · have he : P=(fun u : Fin (k+1) → X => fun i : Fin k => u i.castSucc) ∘ Y := by
        funext ω i; simp [Y]
      exact (congrArg (fun f => (inferInstance : MeasurableSpace (Fin k → X)).comap f) he).le.trans
        ((show Measurable (fun u : Fin (k+1) → X => fun i : Fin k => u i.castSucc) by fun_prop).comp hy).comap_le
    · have he : C=(fun u : Fin (k+1) → X => u (Fin.last k)) ∘ Y := by
        funext ω; simp [Y]
      exact (congrArg (fun f => (inferInstance : MeasurableSpace X).comap f) he).le.trans
        ((measurable_pi_apply (Fin.last k)).comp hy).comap_le

variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X)
variable (g : (k : ℕ) → (Fin k → X) → I → X)
variable (hg : ∀ k, Measurable (uncurry (g k)))
omit [MeasurableSpace X] in
lemma causalPublic_succ (k : ℕ) (ω : UniformTapes ℕ) :
    causalPublic role pub x₀ g (k+1) ω=Fin.snoc (causalPublic role pub x₀ g k ω)
      (if k∈pub then sampledHistory (causalSampler role pub x₀ g) ω k else x₀) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [causalPublic,publicPrefix,sampledPrefix_succ]
  · simpa only [Fin.snoc_castSucc] using causalPublic_castSucc role pub x₀ g k ω j
lemma causalPublicInfo_succ (k : ℕ) (hk : k∈pub) :
    causalPublicInfo role pub x₀ g (k+1)=causalPublicInfo role pub x₀ g k ⊔
      (inferInstance : MeasurableSpace X).comap (fun ω => sampledHistory (causalSampler role pub x₀ g) ω k) := by
  simp only [causalPublicInfo,funext (causalPublic_succ role pub x₀ g k),hk,ite_true]
  exact snoc_information _ _ _
lemma causalPublicInfo_succ_of_private (k : ℕ) (hk : k∉pub) :
    causalPublicInfo role pub x₀ g (k+1)=causalPublicInfo role pub x₀ g k := by
  apply le_antisymm
  · let : MeasurableSpace (UniformTapes ℕ) := causalPublicInfo role pub x₀ g k
    have hP := causalPublic_own_measurable role pub x₀ g k
    change (inferInstance : MeasurableSpace (Fin (k+1) → X)).comap _ ≤ _
    have he : causalPublic role pub x₀ g (k+1)=fun ω => Fin.snoc (causalPublic role pub x₀ g k ω) x₀ := by
      funext ω
      simp only [causalPublic_succ,hk,ite_false]
    rw [he]
    exact ((snoc_measurable k).comp (hP.prodMk measurable_const)).comap_le
  · exact causalPublicInfo_mono role pub x₀ g (Nat.le_succ k)
include hg in
lemma causalOutcome_local (k : ℕ) :
    Measurable[roleInfo role (role k) ⊔ causalPublicInfo role pub x₀ g k]
      (fun ω => sampledHistory (causalSampler role pub x₀ g) ω k) := by
  have hv := causalVisible_local role pub x₀ g hg (role k) k
  have hu : Measurable[roleInfo role (role k) ⊔ causalPublicInfo role pub x₀ g k]
      (fun ω : UniformTapes ℕ => ω k) :=
    (measurable_tape_coordinate {j | role j=role k} k rfl).mono le_sup_left le_rfl
  exact (hg k).comp (hv.prodMk hu)
include hg in
lemma causalPublic_succ_local (k : ℕ) :
    causalPublicInfo role pub x₀ g (k+1) ≤ roleInfo role (role k) ⊔ causalPublicInfo role pub x₀ g k := by
  by_cases hk : k∈pub
  · rw [causalPublicInfo_succ role pub x₀ g k hk]
    exact sup_le le_sup_right (causalOutcome_local role pub x₀ g hg k).comap_le
  · rw [causalPublicInfo_succ_of_private role pub x₀ g k hk]
    exact le_sup_right
omit [MeasurableSpace X] in
lemma source_view_eq_public (hsource : ∀ k, role k=.source → k∈pub) (k : ℕ) :
    causalVisible role pub x₀ g .source k=causalPublic role pub x₀ g k := by
  funext ω i
  by_cases hi : i.val∈pub
  · simp [causalVisible,visiblePrefix,causalPublic,publicPrefix,hi]
  · have hn : role i.val≠.source := fun h => hi (hsource i h)
    simp [causalVisible,visiblePrefix,causalPublic,publicPrefix,hi,hn]

lemma causal_source_step (hsource : ∀ k, role k=.source → k∈pub)
    (κ : (k : ℕ) → Kernel (Fin k → X) X) [∀ k, IsMarkovKernel (κ k)]
    (hmap : ∀ k s, volume.map (g k s)=κ k s) (k : ℕ) (hk : role k=.source) :
    TapePublicStep uniformTapesLaw (roleInfo role .alice) (roleInfo role .bob)
      (causalPublicInfo role pub x₀ g k) (causalPublicInfo role pub x₀ g (k+1))
      (causalPublicInfo_le role pub x₀ g hg k) := by
  let E := {j | role j≠TapeRole.source}
  let S := {j | role j≠TapeRole.source ∨ j<k}
  let H : UniformTapes ℕ → UniformTapes E × (Fin k → X) :=
    fun ω => ((fun j => ω j),causalPublic role pub x₀ g k ω)
  have hrest : Measurable[tapeInformation S] (fun ω : UniformTapes ℕ => fun j : E => ω j) := by
    let : MeasurableSpace (UniformTapes ℕ) := tapeInformation S
    apply Measurable.of_eval
    intro j
    exact measurable_tape_coordinate S j (Or.inl j.property)
  have hP : Measurable[tapeInformation S] (causalPublic role pub x₀ g k) :=
    ((publicPrefix_measurable pub x₀ k).comp
      (sampledPrefix_measurable _ (causalSampler_measurable role pub x₀ g hg) k)).mono
        (tapeInformation_mono (fun j hj => Or.inr hj)) le_rfl
  have hHs : Measurable[tapeInformation S] H := hrest.prodMk hP
  have hH : Measurable H := hHs.mono (tapeInformation_le _) le_rfl
  have hind : IndepFun H (fun ω => ω k) uniformTapesLaw :=
    fresh_coordinate_independent (by simp [S,hk]) H hHs
  have hHown : Measurable[(inferInstance : MeasurableSpace (UniformTapes E × (Fin k→X))).comap H] H :=
    measurable_iff_comap_le.mpr le_rfl
  have hFH : causalPublicInfo role pub x₀ g k ≤ (inferInstance : MeasurableSpace (UniformTapes E × (Fin k→X))).comap H := by
    change (inferInstance : MeasurableSpace (Fin k→X)).comap (Prod.snd ∘ H) ≤ _
    exact ((show Measurable (Prod.snd : UniformTapes E × (Fin k→X) → Fin k→X) from measurable_snd).comp
      hHown).comap_le
  have hrH (r : TapeRole) (hr : r≠.source) :
      roleInfo role r ≤ (inferInstance : MeasurableSpace (UniformTapes E × (Fin k→X))).comap H := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    have hjE : j∈E := by dsimp [E]; exact fun hs => hr (hj.symm.trans hs)
    have hcoord : (fun ω : UniformTapes ℕ => ω j)=
        (fun p : UniformTapes E × (Fin k→X) => p.1 ⟨j,hjE⟩) ∘ H := rfl
    rw [hcoord]
    exact ((show Measurable (fun p : UniformTapes E × (Fin k→X) => p.1 ⟨j,hjE⟩) by fun_prop).comp
      hHown).comap_le
  have hDH := sup_le (hrH .alice (by decide)) (hrH .bob (by decide))
  have hc := sampled_public_independence (causalPublicInfo_le role pub x₀ g hg k)
    (sup_le (roleInfo_le role .alice) (roleInfo_le role .bob)) H hH hFH hDH
    Prod.snd measurable_snd (causalPublic_own_measurable role pub x₀ g k)
    (fun ω => ω k) (measurable_pi_apply k) hind (tape_coordinate_law k)
    (κ k) (g k) (hg k) (hmap k)
  have he : (fun ω => g k (causalPublic role pub x₀ g k ω) (ω k))=
      (fun ω => sampledHistory (causalSampler role pub x₀ g) ω k) := by
    funext ω
    change g k (causalPublic role pub x₀ g k ω) _=g k (causalVisible role pub x₀ g (role k) k ω) _
    rw [hk,source_view_eq_public role pub x₀ g hsource k]
  change CondIndep (causalPublicInfo role pub x₀ g k) (roleInfo role .alice ⊔ roleInfo role .bob) ((inferInstance : MeasurableSpace X).comap (fun ω => g k (causalPublic role pub x₀ g k ω) (ω k))) _ _ at hc
  rw [he] at hc
  refine Or.inr (Or.inr ⟨_,(show Measurable (fun ω => sampledHistory (causalSampler role pub x₀ g) ω k) from
    (measurable_pi_apply k).comp (sampledHistory_measurable _ (causalSampler_measurable role pub x₀ g hg))).comap_le,?_,hc.symm⟩)
  rw [causalPublicInfo_succ role pub x₀ g k (hsource k hk),sup_comm]

end SecretKey

end

end OAI
