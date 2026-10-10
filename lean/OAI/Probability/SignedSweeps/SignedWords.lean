import OAI.Probability.SignedSweeps.EquivSign

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module
local instance (priority := 2000) signedWordsFunctionDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedWordsSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma wordEvenSites_comp_mem {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C ⊕ C) (i : Fin p) :
    i ∈ wordEvenSites (w ∘ g) ↔ g i ∈ wordEvenSites w := by
  simp only [mem_wordEvenSites, Function.comp_apply]

def oddPositionSetEquiv {p : ℕ} (g : SymmetricGroup p)
    (S T : Finset (Fin p)) (h : ∀ i, i ∈ T ↔ g i ∈ S) :
    {i : Fin p // i ∉ T} ≃ {i : Fin p // i ∉ S} where
  toFun i := ⟨g i, fun hi => i.2 ((h i).mpr hi)⟩
  invFun i := ⟨g.symm i, by simpa only [h, Equiv.apply_symm_apply] using i.2⟩
  left_inv i := by apply Subtype.ext; exact g.symm_apply_apply i
  right_inv i := by apply Subtype.ext; exact g.apply_symm_apply i

def oddPositionEquiv {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C ⊕ C) :
    {i : Fin p // i ∉ wordEvenSites (w ∘ g)} ≃ {i : Fin p // i ∉ wordEvenSites w} :=
  oddPositionSetEquiv g (wordEvenSites w) (wordEvenSites (w ∘ g))
    (wordEvenSites_comp_mem g w)

lemma oddPositionEquiv_one {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) :
    oddPositionEquiv 1 w = Equiv.refl {i : Fin p // i ∉ wordEvenSites w} := by
  apply Equiv.ext
  intro i
  rfl

lemma oddPositionEquiv_mul {p : ℕ} {C : Type*} (g h : SymmetricGroup p)
    (w : Fin p → C ⊕ C) :
    oddPositionEquiv (g*h) w = (oddPositionEquiv h (w ∘ g)).trans (oddPositionEquiv g w) := by
  apply Equiv.ext
  intro i
  rfl

def wordPhase {p : ℕ} {C : Type*} (g : SymmetricGroup p) (w : Fin p → C ⊕ C) : ℂ :=
  complexEquivSign (oddPositionEquiv g w)

@[simp] lemma wordPhase_one {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) :
    wordPhase 1 w = 1 := by
  exact (congrArg (fun e => complexEquivSign e) (oddPositionEquiv_one w)).trans
    (complexEquivSign_refl)

lemma wordPhase_mul {p : ℕ} {C : Type*} (g h : SymmetricGroup p) (w : Fin p → C ⊕ C) :
    wordPhase (g*h) w = wordPhase g w * wordPhase h (w ∘ g) := by
  exact (congrArg (fun e => complexEquivSign e) (oddPositionEquiv_mul g h w)).trans
    (complexEquivSign_trans _ _)

lemma wordPhase_norm {p : ℕ} {C : Type*} (g : SymmetricGroup p) (w : Fin p → C ⊕ C) :
    ‖wordPhase g w‖ = 1 := complexEquivSign_norm _

def signedWordLinear {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) where
  toFun f := WithLp.toLp 2 (fun w => wordPhase g w * f (w ∘ g))
  map_add' f h := by ext w; exact mul_add _ _ _
  map_smul' c f := by ext w; exact mul_left_comm _ _ _

@[simp] lemma signedWordLinear_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) (w : Fin p → C ⊕ C) :
    signedWordLinear g f w = wordPhase g w * f (w ∘ g) := rfl

def signedWordRepresentation (p : ℕ) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup p) (WordSpace p (C ⊕ C)) where
  toFun := signedWordLinear
  map_one' := by ext f w; simp only [signedWordLinear_apply, wordPhase_one, one_mul]; rfl
  map_mul' g h := by
    ext f w
    simp only [signedWordLinear_apply, Module.End.mul_apply, wordPhase_mul]
    exact mul_assoc _ _ _

@[simp] lemma signedWordRepresentation_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) (w : Fin p → C ⊕ C) :
    signedWordRepresentation p C g f w = wordPhase g w * f (w ∘ g) := rfl

lemma signedWordRepresentation_norm {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) :
    ‖signedWordRepresentation p C g f‖ = ‖f‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [signedWordRepresentation_apply, norm_mul, wordPhase_norm, one_mul]
  exact (Equiv.sum_comp (wordPositionEquiv g).symm (fun w => ‖f w‖^2))

lemma wordEvenSites_comp_eq {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordEvenSites (w ∘ g) = wordEvenSites (z ∘ g) := by
  ext i
  simp only [wordEvenSites_comp_mem, h]

lemma oddPositionSetEquiv_sign_congr {p : ℕ} (g : SymmetricGroup p)
    {S T R U : Finset (Fin p)} (hS : S = T) (hT : R = U)
    (h1 : ∀ i, i ∈ R ↔ g i ∈ S) (h2 : ∀ i, i ∈ U ↔ g i ∈ T) :
    complexEquivSign (oddPositionSetEquiv g S R h1) =
      complexEquivSign (oddPositionSetEquiv g T U h2) := by
  subst T
  subst U
  rfl

lemma wordPhase_eq_of_parity {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w z : Fin p → C ⊕ C) (h : wordEvenSites w = wordEvenSites z) :
    wordPhase g w = wordPhase g z := by
  have hi := wordEvenSites_comp_eq g w z h
  exact oddPositionSetEquiv_sign_congr g h hi _ _

end SignedSweeps
end

end OAI
