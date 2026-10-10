import OAI.InformationTheory.Entanglement.CausalRealization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Function Filter
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
attribute [local instance] Classical.propDecidable
variable {X S : Type*}
variable (role : ℕ → TapeRole) (pub : Set ℕ) (x₀ : X) (r : TapeRole)
lemma visiblePrefix_init (k : ℕ) (h : Fin (k+1)→X) :
    Fin.init (visiblePrefix role pub x₀ r (k+1) h)=
      visiblePrefix role pub x₀ r k (Fin.init h) := by
  funext i
  simp only [Fin.init,visiblePrefix,Fin.val_castSucc]
lemma visiblePrefix_idem (k : ℕ) (h : Fin k→X) :
    visiblePrefix role pub x₀ r k (visiblePrefix role pub x₀ r k h)=visiblePrefix role pub x₀ r k h := by
  funext i
  dsimp only [visiblePrefix]
  split_ifs <;> rfl

def localStateAt (s₀ : S) (update : (k : ℕ) → (Fin k→X) → S → X → S) :
    (k : ℕ) → (Fin k→X) → S
  | 0, _ => s₀
  | k+1, h => if role k=r then
      update k (visiblePrefix role pub x₀ r k (Fin.init h))
        (localStateAt s₀ update k (Fin.init h)) (h (Fin.last k))
    else localStateAt s₀ update k (Fin.init h)
lemma localStateAt_visible (s₀ : S) (update : (k : ℕ) → (Fin k→X) → S → X → S)
    (k : ℕ) (h : Fin k→X) :
    localStateAt role pub x₀ r s₀ update k (visiblePrefix role pub x₀ r k h)=
      localStateAt role pub x₀ r s₀ update k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [localStateAt,visiblePrefix_init,visiblePrefix_idem,ih]
    by_cases hr : role k=r
    · simp [hr,visiblePrefix]
    · simp only [hr,ite_false]
variable [MeasurableSpace X] [MeasurableSpace S]
lemma localStateAt_measurable (s₀ : S) (update : (k : ℕ) → (Fin k→X) → S → X → S)
    (hupdate : ∀ k, Measurable (fun p : ((Fin k→X)×S)×X => update k p.1.1 p.1.2 p.2)) (k : ℕ) :
    Measurable (localStateAt role pub x₀ r s₀ update k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hini : Measurable (Fin.init : (Fin (k+1)→X) → (Fin k→X)) := by
      apply Measurable.of_eval; intro i; exact measurable_pi_apply i.castSucc
    by_cases hr : role k=r
    · simp only [localStateAt,hr,ite_true]
      exact (hupdate k).comp
        ((((visiblePrefix_measurable role pub x₀ r k).comp hini).prodMk (ih.comp hini)).prodMk
          (measurable_pi_apply (Fin.last k)))
    · simpa only [localStateAt,hr,ite_false,Function.comp_def] using ih.comp hini

def memoryOutcomeKernel (s₀ : S) (update : (k : ℕ) → (Fin k→X) → S → X → S)
    (hupdate : ∀ k, Measurable (fun p : ((Fin k→X)×S)×X => update k p.1.1 p.1.2 p.2))
    (K : (k : ℕ) → Kernel ((Fin k→X)×S) X) (k : ℕ) : Kernel (Fin k→X) X :=
  (K k).comap (fun h => (visiblePrefix role pub x₀ r k h,localStateAt role pub x₀ r s₀ update k h))
    ((visiblePrefix_measurable role pub x₀ r k).prodMk (localStateAt_measurable role pub x₀ r s₀ update hupdate k))
lemma memoryOutcomeKernel_visible (s₀ : S) (update : (k : ℕ) → (Fin k→X) → S → X → S)
    (hupdate : ∀ k, Measurable (fun p : ((Fin k→X)×S)×X => update k p.1.1 p.1.2 p.2))
    (K : (k : ℕ) → Kernel ((Fin k→X)×S) X) (k : ℕ) (h : Fin k→X) :
    memoryOutcomeKernel role pub x₀ r s₀ update hupdate K k (visiblePrefix role pub x₀ r k h)=
      memoryOutcomeKernel role pub x₀ r s₀ update hupdate K k h := by
  simp only [memoryOutcomeKernel,Kernel.comap_apply,visiblePrefix_idem,localStateAt_visible]

end SecretKey

end

end OAI
