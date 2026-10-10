import Mathlib
import OAI.Geometry.HyperbolicGroups.Candidate

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace PinnedAssignments
variable {W F A : Type*} [Fintype W] [Fintype A]
  [DecidableEq W] [DecidableEq F] [DecidableEq A]

abbrev Free (P : Finset W) := {v : W // v ∉ P}

def extend (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : W) : A :=
  if h : v ∈ P then ξ v else σ ⟨v,h⟩

omit [Fintype W] [Fintype A] [DecidableEq A] in
@[simp] lemma extend_free (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : Free P) :
    extend P ξ σ v.val = σ v := by simp [extend,v.property]

omit [Fintype W] [Fintype A] [DecidableEq A] in
@[simp] lemma extend_pin (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : W) (h : v ∈ P) :
    extend P ξ σ v = ξ v := by simp [extend,h]

def support (P E : Finset W) : Finset (Free P) := Finset.univ.filter (fun v => v.val ∈ E)

@[simp] lemma mem_support (P E : Finset W) (v : Free P) : v ∈ support P E ↔ v.val ∈ E := by
  simp [support]

lemma card_support (P E : Finset W) : (support P E).card = (E \ P).card := by
  classical
  let e : (support P E) ≃ ↥(E \ P) :=
    { toFun := fun v => ⟨v.val.val,Finset.mem_sdiff.mpr ⟨(mem_support _ _ _).mp v.property,v.val.property⟩⟩
      invFun := fun v => ⟨⟨v.val,(Finset.mem_sdiff.mp v.property).2⟩,
        (mem_support _ _ _).mpr (Finset.mem_sdiff.mp v.property).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

lemma support_biUnion {S : Type*} [DecidableEq S] (P : Finset W)
    (J : Finset S) (E : S → Finset W) :
    J.biUnion (fun s => support P (E s)) = support P (J.biUnion E) := by
  ext v
  simp

/-- Injectivity is imposed separately on each coordinate field, not globally. -/
def Fieldwise (tag : W → F) (σ : W → A) : Prop :=
  ∀ v w, tag v = tag w → σ v = σ w → v = w

instance (tag : W → F) (σ : W → A) : Decidable (Fieldwise tag σ) :=
  inferInstanceAs (Decidable (∀ v w, tag v = tag w → σ v = σ w → v = w))

def PinFieldwise (tag : W → F) (P : Finset W) (ξ : W → A) : Prop :=
  ∀ v ∈ P, ∀ w ∈ P, tag v = tag w → ξ v = ξ w → v = w

def candidates (tag : W → F) (P : Finset W) (ξ : W → A) : Finset (Free P → A) :=
  Finset.univ.filter (fun σ => Fieldwise tag (extend P ξ σ))

lemma embedding_mem (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ)
    (f : Free P ↪ {a : A // a ∉ P.image ξ}) :
    (fun v => (f v).val) ∈ candidates tag P ξ := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  intro v w ht he
  by_cases hv : v ∈ P <;> by_cases hw : w ∈ P
  · exact hξ v hv w hw ht (by simpa [extend,hv,hw] using he)
  · have hh : ξ v = (f ⟨w,hw⟩).val := by simpa [extend,hv,hw] using he
    exact False.elim ((f ⟨w,hw⟩).property (hh ▸ Finset.mem_image_of_mem ξ hv))
  · have hh : (f ⟨v,hv⟩).val = ξ w := by simpa [extend,hv,hw] using he
    exact False.elim ((f ⟨v,hv⟩).property (hh.symm ▸ Finset.mem_image_of_mem ξ hw))
  · have hh : f ⟨v,hv⟩ = f ⟨w,hw⟩ := Subtype.ext (by simpa [extend,hv,hw] using he)
    exact congrArg Subtype.val (f.injective hh)

lemma candidates_lower (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ) (hN : 4 * Fintype.card W ≤ Fintype.card A) :
    ((Fintype.card A : ℝ) / 2) ^ Fintype.card (Free P) ≤ (candidates tag P ξ).card := by
  apply BernoulliCandidates.card_lower_half _ (P.image ξ) (embedding_mem tag P ξ hξ)
  have h₁ := Finset.card_image_le (s := P) (f := ξ)
  have h₂ := Finset.card_le_univ P
  have h₃ := Fintype.card_subtype_le (fun v : W => v ∉ P)
  change Fintype.card (Free P) ≤ Fintype.card W at h₃
  omega

omit [Fintype A] [DecidableEq W] [DecidableEq F] [DecidableEq A] in
lemma permutations (tag : W → F) (P : Finset W) (ξ ζ : W → A)
    (hξ : PinFieldwise tag P ξ) (hζ : PinFieldwise tag P ζ) :
    ∃ π : F → Equiv.Perm A, ∀ v ∈ P, π (tag v) (ξ v) = ζ v := by
  classical
  have h (f : F) : ∃ π : Equiv.Perm A, ∀ v : {v : P // tag v.val = f},
      π (ξ v.val.val) = ζ v.val.val := by
    apply Equiv.Perm.exists_extending_pair
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact hξ _ v.val.property _ w.val.property (v.property.trans w.property.symm) he
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact hζ _ v.val.property _ w.val.property (v.property.trans w.property.symm) he
  choose π hπ using h
  exact ⟨π,fun v hv => hπ (tag v) ⟨⟨v,hv⟩,rfl⟩⟩

lemma card_candidates_eq (tag : W → F) (P : Finset W) (ξ ζ : W → A)
    (hξ : PinFieldwise tag P ξ) (hζ : PinFieldwise tag P ζ) :
    (candidates tag P ξ).card = (candidates tag P ζ).card := by
  classical
  obtain ⟨π,hπ⟩ := permutations tag P ξ ζ hξ hζ
  let e : (Free P → A) ≃ (Free P → A) := Equiv.piCongrRight (fun v => π (tag v.val))
  have hext (σ : Free P → A) (v : W) : extend P ζ (e σ) v = π (tag v) (extend P ξ σ v) := by
    by_cases hv : v ∈ P
    · simp [extend,hv,hπ v hv]
    · simp [extend,hv,e]
  have hm (σ : Free P → A) : e σ ∈ candidates tag P ζ ↔ σ ∈ candidates tag P ξ := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v w ht hvw
      apply h v w ht
      simp only [hext, ht, hvw]
    · intro h v w ht hvw
      rw [hext,hext,ht] at hvw
      exact h v w ht ((π (tag w)).injective hvw)
  let ec : (candidates tag P ξ) ≃ (candidates tag P ζ) :=
    { toFun := fun σ => ⟨e σ.val,(hm σ.val).mpr σ.property⟩
      invFun := fun τ => ⟨e.symm τ.val,(hm (e.symm τ.val)).mp (by simp [τ.property])⟩
      left_inv := fun σ => Subtype.ext (e.symm_apply_apply σ.val)
      right_inv := fun τ => Subtype.ext (e.apply_symm_apply τ.val) }
  simpa only [Fintype.card_coe] using Fintype.card_congr ec

end PinnedAssignments


end HyperbolicObstruction
end
end
end

end OAI
