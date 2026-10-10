import OAI.InformationTheory.Entanglement.SequentialSampling
import OAI.InformationTheory.Entanglement.PublicSampler
import OAI.InformationTheory.Entanglement.TranscriptClassical

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey

inductive TapeRole | alice | bob | source
  deriving DecidableEq
attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X]
variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X)

def visiblePrefix (r : TapeRole) (k : ℕ) (x : Fin k → X) : Fin k → X :=
  fun i => if role i = r ∨ i.val∈pub then x i else x₀

def publicPrefix (k : ℕ) (x : Fin k → X) : Fin k → X :=
  fun i => if i.val∈pub then x i else x₀
lemma visiblePrefix_measurable (r : TapeRole) (k : ℕ) :
    Measurable (visiblePrefix role pub x₀ r k) := by
  apply Measurable.of_eval
  intro i
  by_cases h : role i=r ∨ i.val∈pub
  · simpa only [visiblePrefix,h,ite_true] using measurable_pi_apply i
  · simpa only [visiblePrefix,h,ite_false] using (measurable_const : Measurable (fun _ : Fin k → X => x₀))
lemma publicPrefix_measurable (k : ℕ) :
    Measurable (publicPrefix pub x₀ k) := by
  apply Measurable.of_eval
  intro i
  by_cases h : i.val∈pub
  · simpa only [publicPrefix,h,ite_true] using measurable_pi_apply i
  · simpa only [publicPrefix,h,ite_false] using (measurable_const : Measurable (fun _ : Fin k → X => x₀))

variable (g : (k : ℕ) → (Fin k → X) → I → X)
def causalSampler (k : ℕ) (x : Fin k → X) (u : I) : X :=
  g k (visiblePrefix role pub x₀ (role k) k x) u
lemma causalSampler_measurable (hg : ∀ k, Measurable (uncurry (g k))) (k : ℕ) :
    Measurable (uncurry (causalSampler role pub x₀ g k)) := by
  exact (hg k).comp
    (((visiblePrefix_measurable role pub x₀ (role k) k).comp measurable_fst).prodMk measurable_snd)
def causalPublic (k : ℕ) : UniformTapes ℕ → (Fin k → X) :=
  fun ω => publicPrefix pub x₀ k (sampledPrefix (causalSampler role pub x₀ g) k ω)
def causalVisible (r : TapeRole) (k : ℕ) : UniformTapes ℕ → (Fin k → X) :=
  fun ω => visiblePrefix role pub x₀ r k (sampledPrefix (causalSampler role pub x₀ g) k ω)
@[instance_reducible]
def causalPublicInfo (k : ℕ) : MeasurableSpace (UniformTapes ℕ) :=
  (inferInstance : MeasurableSpace (Fin k → X)).comap (causalPublic role pub x₀ g k)
@[instance_reducible]
def roleInfo (r : TapeRole) : MeasurableSpace (UniformTapes ℕ) := tapeInformation {k | role k=r}
lemma causalPublic_measurable (hg : ∀ k, Measurable (uncurry (g k))) (k : ℕ) :
    Measurable (causalPublic role pub x₀ g k) :=
  (publicPrefix_measurable pub x₀ k).comp
    (sampledPrefix_measurable_global _ (causalSampler_measurable role pub x₀ g hg) k)
lemma causalPublicInfo_le (hg : ∀ k, Measurable (uncurry (g k))) (k : ℕ) :
    causalPublicInfo role pub x₀ g k ≤ (inferInstance : MeasurableSpace (UniformTapes ℕ)) :=
  (causalPublic_measurable role pub x₀ g hg k).comap_le
lemma roleInfo_le (r : TapeRole) : roleInfo role r ≤ (inferInstance : MeasurableSpace (UniformTapes ℕ)) :=
  tapeInformation_le _
lemma causalPublic_own_measurable (k : ℕ) :
    Measurable[causalPublicInfo role pub x₀ g k] (causalPublic role pub x₀ g k) :=
  measurable_iff_comap_le.mpr le_rfl

omit [MeasurableSpace X] in
lemma causalPublic_castSucc (k : ℕ) (ω : UniformTapes ℕ) (i : Fin k) :
    causalPublic role pub x₀ g (k+1) ω i.castSucc=causalPublic role pub x₀ g k ω i := by
  simp only [causalPublic,publicPrefix,sampledPrefix_succ,Fin.snoc_castSucc,Fin.val_castSucc]
lemma causalPublicInfo_mono : Monotone (causalPublicInfo role pub x₀ g) := by
  apply monotone_nat_of_le_succ
  intro k
  have h : causalPublic role pub x₀ g k=
      (fun v : Fin (k+1)→X => fun i : Fin k => v i.castSucc) ∘ causalPublic role pub x₀ g (k+1) := by
    funext ω i
    exact (causalPublic_castSucc role pub x₀ g k ω i).symm
  change (inferInstance : MeasurableSpace (Fin k→X)).comap _ ≤ _
  rw [h]
  exact ((show Measurable (fun v : Fin (k+1)→X => fun i : Fin k => v i.castSucc) by fun_prop).comp
    (causalPublic_own_measurable role pub x₀ g (k+1))).comap_le

theorem causalVisible_local (hg : ∀ k, Measurable (uncurry (g k))) (r : TapeRole) (k : ℕ) :
    Measurable[roleInfo role r ⊔ causalPublicInfo role pub x₀ g k]
      (causalVisible role pub x₀ g r k) := by
  induction k with
  | zero =>
    let : MeasurableSpace (UniformTapes ℕ) := roleInfo role r ⊔ causalPublicInfo role pub x₀ g 0
    apply Measurable.of_eval
    intro i
    exact Fin.elim0 i
  | succ k ih =>
    let F := roleInfo role r ⊔ causalPublicInfo role pub x₀ g (k+1)
    let : MeasurableSpace (UniformTapes ℕ) := F
    have hp : Measurable[F] (causalVisible role pub x₀ g r k) :=
      ih.mono (sup_le_sup_left (causalPublicInfo_mono role pub x₀ g (Nat.le_succ k)) _) le_rfl
    have hpub : Measurable[F] (causalPublic role pub x₀ g (k+1)) :=
      (causalPublic_own_measurable role pub x₀ g (k+1)).mono le_sup_right le_rfl
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · by_cases hk : k∈pub
      · have he : (fun ω => causalVisible role pub x₀ g r (k+1) ω (Fin.last k))=
            (fun ω => causalPublic role pub x₀ g (k+1) ω (Fin.last k)) := by
          funext ω
          simp [causalVisible,visiblePrefix,causalPublic,publicPrefix,hk]
        rw [he]
        exact (measurable_pi_apply (Fin.last k)).comp hpub
      · by_cases hr : role k=r
        · have hu : Measurable[F] (fun ω : UniformTapes ℕ => ω k) := by
            apply (measurable_tape_coordinate {j | role j=r} k hr).mono le_sup_left le_rfl
          have he : (fun ω => causalVisible role pub x₀ g r (k+1) ω (Fin.last k))=
              (fun ω => g k (causalVisible role pub x₀ g r k ω) (ω k)) := by
            funext ω
            simp [causalVisible,visiblePrefix,sampledPrefix_succ,sampledHistory,causalSampler,hr]
          rw [he]
          exact (hg k).comp (hp.prodMk hu)
        · have he : (fun ω => causalVisible role pub x₀ g r (k+1) ω (Fin.last k))=(fun _ => x₀) := by
            funext ω
            simp [causalVisible,visiblePrefix,hk,hr]
          rw [he]
          exact measurable_const
    · have he : (fun ω => causalVisible role pub x₀ g r (k+1) ω j.castSucc)=
          (fun ω => causalVisible role pub x₀ g r k ω j) := by
        funext ω
        simp only [causalVisible,visiblePrefix,sampledPrefix_succ,Fin.snoc_castSucc,Fin.val_castSucc]
      rw [he]
      exact (measurable_pi_apply j).comp hp

end SecretKey

end

end OAI
