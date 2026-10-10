import OAI.Probability.SignedSweeps.MarkedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, Fintype (A j)]

def sigmaPermutation : (∀ j, Equiv.Perm (A j)) →* Equiv.Perm (Σ j, A j) where
  toFun := Equiv.Perm.sigmaCongrRight
  map_one' := by apply Equiv.ext; intro x; cases x; rfl
  map_mul' g h := by apply Equiv.ext; intro x; cases x; rfl

omit [Fintype J] [∀ j, Fintype (A j)] in
lemma sigmaPermutation_injective : Function.Injective (sigmaPermutation (A := A)) := by
  intro g h he
  funext j
  apply Equiv.ext
  intro x
  have hx := Equiv.congr_fun he ⟨j,x⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

omit [Fintype J] [∀ j, Fintype (A j)] in
lemma sigmaPermutation_single (j : J) (g : Equiv.Perm (A j)) :
    sigmaPermutation (Pi.mulSingle j g) = g.viaEmbedding ⟨Sigma.mk j, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩ := by
  apply Equiv.ext
  rintro ⟨i,x⟩
  by_cases hi : i = j
  · subst i
    change Sigma.mk j ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g j) x) = _
    rw [Pi.mulSingle_eq_same]
    exact (Equiv.Perm.viaEmbedding_apply g ⟨Sigma.mk j, fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩ x).symm
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · change Sigma.mk i ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g i) x) = Sigma.mk i x
      rw [Pi.mulSingle_eq_of_ne hi]
      rfl
    · rintro ⟨y,hy⟩
      exact hi (congrArg Sigma.fst hy).symm

theorem sign_sigmaPermutation (g : ∀ j, Equiv.Perm (A j)) :
    Equiv.Perm.sign (sigmaPermutation g) = ∏ j, Equiv.Perm.sign (g j) := by
  let R : (∀ j, Equiv.Perm (A j)) →* ℤˣ :=
    { toFun := fun g => ∏ j, Equiv.Perm.sign (g j)
      map_one' := by simp
      map_mul' := fun g h => by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib] }
  have he : Equiv.Perm.sign.comp (sigmaPermutation (A := A)) = R := by
    apply MonoidHom.pi_ext
    intro j g
    change Equiv.Perm.sign (sigmaPermutation (Pi.mulSingle j g)) = ∏ i, Equiv.Perm.sign ((Pi.mulSingle (M := fun j => Equiv.Perm (A j)) j g) i)
    rw [sigmaPermutation_single]
    simp only [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    symm
    rw [Finset.prod_eq_single j]
    · rw [Pi.mulSingle_eq_same]
    · intro i _ hi
      rw [Pi.mulSingle_eq_of_ne hi, map_one]
    · simp
  exact congrArg (fun f : (∀ j, Equiv.Perm (A j)) →* ℤˣ => f g) he

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p : ℕ} {k : J → ℕ}

def blockPermutation (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (∀ j, SymmetricGroup (k j)) →* SymmetricGroup p :=
  e.permCongrHom.toMonoidHom.comp sigmaPermutation

omit [Fintype J] in
@[simp] lemma blockPermutation_apply (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) (j : J) (i : Fin (k j)) :
    blockPermutation e g (e ⟨j,i⟩) = e ⟨j,g j i⟩ := by
  change (e.permCongr (sigmaPermutation g)) (e ⟨j,i⟩) = _
  simp [Equiv.permCongr_apply, sigmaPermutation]

omit [Fintype J] in
lemma blockPermutation_injective (e : (Σ j, Fin (k j)) ≃ Fin p) :
    Function.Injective (blockPermutation e) := by
  intro g h he
  exact sigmaPermutation_injective (e.permCongr.injective he)

omit [Fintype J] in
lemma blockPermutation_fiber (e : (Σ j, Fin (k j)) ≃ Fin p)
    (g : ∀ j, SymmetricGroup (k j)) :
    blockPermutation e g ∈ fiberSubgroup (fun x => (e.symm x).1) := by
  intro x
  obtain ⟨x,rfl⟩ := e.surjective x
  rcases x with ⟨j,i⟩
  rw [blockPermutation_apply]
  simp only [Equiv.symm_apply_apply]

end SignedSweeps
end

end OAI
