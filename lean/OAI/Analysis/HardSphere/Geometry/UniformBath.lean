import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PermutationObserved

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
local instance permBathSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
local instance permBathSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

lemma uniform_of_equiv {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (e : Equiv.Perm A) :
    (PMF.uniformOfFintype A).toMeasure.map e=(PMF.uniformOfFintype A).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have he : (e:A→A) ⁻¹' {a}={e.symm a} := by ext b; simp [Equiv.eq_symm_apply]
  rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

def bathFinEquiv (a : Fin (n+1)) : Fin n ≃ {j : Option (Fin (n+1)) // j≠none ∧ j≠some a} :=
  Equiv.ofBijective (fun k ↦ ⟨some (a.succAbove k),
    ⟨Option.some_ne_none _,fun equality ↦ Fin.succAbove_ne a k (Option.some.inj equality)⟩⟩) (by
    constructor
    · intro j k h
      exact Fin.succAbove_right_injective (Option.some_injective _ (congrArg Subtype.val h))
    · rintro ⟨j,hj⟩
      cases j with
      | none => exact False.elim (hj.1 rfl)
      | some j =>
        have hja : j≠a := fun h ↦ hj.2 (congrArg some h)
        obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hja
        exact ⟨k,Subtype.ext (congrArg some hk)⟩)

lemma bathFinEquiv_apply (a : Fin (n+1)) (j : Fin n) :
    (bathFinEquiv a j).val=some (a.succAbove j) := rfl

def bathIndexPermutation (σ : Equiv.Perm (Option (Fin (n+1))))
    (a b : Fin (n+1)) (hs : σ none=some a) (hb : σ (some b)=none) : Equiv.Perm (Fin n) :=
  (bathFinEquiv b).trans ((bathPermutation σ none (some a) (some b) hs hb).trans
    ((Equiv.subtypeEquivRight fun _ ↦ and_comm).trans (bathFinEquiv a).symm))

lemma bathIndexPermutation_apply (σ : Equiv.Perm (Option (Fin (n+1))))
    (a b : Fin (n+1)) (hs : σ none=some a) (hb : σ (some b)=none) (j : Fin n) :
    some (a.succAbove (bathIndexPermutation σ a b hs hb j))=σ (some (b.succAbove j)) := by
  exact congrArg Subtype.val ((bathFinEquiv a).apply_symm_apply
    ((Equiv.subtypeEquivRight fun _ ↦ and_comm) (bathPermutation σ none (some a) (some b) hs hb (bathFinEquiv b j))))

def uniformBathOrder (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
instance uniformBathOrder_probability (n : ℕ) : IsProbabilityMeasure (uniformBathOrder n) := by
  unfold uniformBathOrder; infer_instance

def orderedPrimaryObservation (b : Bool) (i : Fin (n+1))
    (z : (Option (Fin (n+1))→E)×Equiv.Perm (Fin n)) : E×E×(Fin n→E) :=
  if b then (z.1 (some i),z.1 none,fun j ↦ z.1 (some (i.succAbove (z.2 j))))
  else (z.1 none,z.1 (some i),fun j ↦ z.1 (some (i.succAbove (z.2 j))))

lemma orderedPrimaryObservation_measurable (b : Bool) (i : Fin (n+1)) :
    Measurable (orderedPrimaryObservation (E:=E) b i) := by
  apply measurable_from_prod_countable_left
  intro τ
  cases b <;> dsimp [orderedPrimaryObservation] <;> fun_prop

theorem uniformBath_same_observation (σ : Equiv.Perm (Option (Fin (n+1))))
    (a b : Fin (n+1)) (hs : σ none=some a) (hb : σ (some b)=none)
    (F G : Option (Fin (n+1))→E) (hFG : ∀j,G j=F (σ j)) :
    (uniformBathOrder n).map (fun τ ↦ orderedPrimaryObservation true a (F,τ))=
    (uniformBathOrder n).map (fun τ ↦ orderedPrimaryObservation false b (G,τ)) := by
  let θ := bathIndexPermutation σ a b hs hb
  have hβ : (uniformBathOrder n).map (Equiv.mulLeft θ)=uniformBathOrder n :=
    uniform_of_equiv (Equiv.mulLeft θ)
  nth_rw 1 [←hβ]
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  apply ae_of_all
  intro τ
  dsimp [Function.comp_def,orderedPrimaryObservation]
  rw [hFG none,hFG (some b),hs,hb]
  congr 2
  funext j
  rw [hFG]; apply congrArg F
  exact bathIndexPermutation_apply σ a b hs hb (τ j)

end HardSphere.Comparison
end
end

end OAI
