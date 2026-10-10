import OAI.Algebra.AuslanderReiten.Duality.LinearHomologyDuality

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W] [AddCommGroup U'] [Module k U']
variable [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
variable (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
variable (f' : U' →ₗ[k] V') (g' : V' →ₗ[k] W') (h' : g'.comp f' = 0)
variable (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V') (c : W ≃ₗ[k] W')
variable (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ x, c (g x) = g' (b x))

def cycleEquiv : LinearMap.ker g ≃ₗ[k] LinearMap.ker g' where
  toFun x := ⟨b x.val, by
    change g' (b x.val) = 0
    rw [← hg, x.property, map_zero]⟩
  invFun y := ⟨b.symm y.val, by
    apply c.injective
    rw [hg, b.apply_symm_apply, y.property, map_zero]⟩
  left_inv x := Subtype.ext (b.symm_apply_apply x.val)
  right_inv y := Subtype.ext (b.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (b.map_add x.val y.val)
  map_smul' r x := Subtype.ext (b.map_smul r x.val)

include a hf in
theorem cycleEquiv_boundaries :
    (boundaries f g h).map (cycleEquiv g g' b c hg).toLinearMap = boundaries f' g' h' := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨a u, Subtype.ext (hf u).symm⟩
  · rintro ⟨u, rfl⟩
    refine ⟨cycleMap f g h (a.symm u), ⟨a.symm u, rfl⟩, ?_⟩
    apply Subtype.ext
    change b (f (a.symm u)) = f' u
    rw [hf, a.apply_symm_apply]

def congr : Homology f g h ≃ₗ[k] Homology f' g' h' :=
  Submodule.Quotient.equiv _ _ (cycleEquiv g g' b c hg)
    (cycleEquiv_boundaries f g h f' g' h' a b c hf hg)

@[simp]
theorem congr_mk (x : LinearMap.ker g) :
    congr f g h f' g' h' a b c hf hg ((boundaries f g h).mkQ x) =
      (boundaries f' g' h').mkQ (cycleEquiv g g' b c hg x) := rfl

@[simp]
theorem congr_symm_mk (x : LinearMap.ker g') :
    (congr f g h f' g' h' a b c hf hg).symm ((boundaries f' g' h').mkQ x) =
      (boundaries f g h).mkQ ((cycleEquiv g g' b c hg).symm x) := rfl

end ArExplicit.LinearHomology

end OAI
