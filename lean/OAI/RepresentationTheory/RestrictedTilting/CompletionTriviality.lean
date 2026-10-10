import OAI.RepresentationTheory.RestrictedTilting.AdicJets

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct Pointwise
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable (I : Ideal R)

 
def completionOfJetMaps
    (F : (j : ℕ) → (M ⧸ (I^j • (⊤ : Submodule R M))) →ₗ[R]
      (N ⧸ (I^j • (⊤ : Submodule R N))))
    (hF : ∀ m n (h : m ≤ n) z,
      AdicCompletion.transitionMap I N h (F n z) =
        F m (AdicCompletion.transitionMap I M h z)) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  toFun x := ⟨fun j => F j (x.val j), by
    intro m n h
    rw [hF, x.property h]⟩
  map_add' x y := by ext j; exact map_add (F j) _ _
  map_smul' r x := by
    apply AdicCompletion.ext
    intro j
    change F j (r.val j • x.val j) = r.val j • F j (x.val j)
    obtain ⟨a,ha⟩ := (I^j • (⊤ : Submodule R R)).mkQ_surjective (r.val j)
    rw [← ha]
    exact map_smul (F j) a (x.val j)

 

theorem completionOfJetMaps_bijective
    (F : (j : ℕ) → (M ⧸ (I^j • (⊤ : Submodule R M))) →ₗ[R]
      (N ⧸ (I^j • (⊤ : Submodule R N))))
    (hF : ∀ m n (h : m ≤ n) z,
      AdicCompletion.transitionMap I N h (F n z) =
        F m (AdicCompletion.transitionMap I M h z))
    (hbij : ∀ j, Function.Bijective (F j)) :
    Function.Bijective (completionOfJetMaps I F hF) := by
  constructor
  · intro x y h
    apply AdicCompletion.ext
    intro j
    exact (hbij j).1 (congrArg (fun z : AdicCompletion I N => z.val j) h)
  · intro y
    let e (j : ℕ) := LinearEquiv.ofBijective (F j) (hbij j)
    let x : AdicCompletion I M := ⟨fun j => (e j).symm (y.val j), by
      intro m n h
      apply (hbij m).1
      rw [← hF]
      change AdicCompletion.transitionMap I N h ((e n) ((e n).symm (y.val n))) =
        (e m) ((e m).symm (y.val m))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, y.property h]⟩
    refine ⟨x, ?_⟩
    apply AdicCompletion.ext
    intro j
    exact (e j).apply_symm_apply _
end
end FiberFunctorProof

end OAI
