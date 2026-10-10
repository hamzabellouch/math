import OAI.Probability.ThorpShuffle.FourierPerturbation

namespace OAI

universe uI uβ uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα}

attribute [-simp] Thorp.Specht.perm_apply_inv Thorp.Specht.perm_inv_apply in
def perm (p : I → Equiv.Perm β) : Equiv.Perm (I × β) where
  toFun x := (x.1, p x.1 x.2)
  invFun x := (x.1, (p x.1)⁻¹ x.2)
  left_inv x := by simp
  right_inv x := by simp

def hom : (I → Equiv.Perm β) →* Equiv.Perm (I × β) where
  toFun := perm
  map_one' := by ext ⟨i,b⟩ <;> rfl
  map_mul' p q := by ext ⟨i,b⟩ <;> rfl

def embedding (e : α ≃ I × β) : (I → Equiv.Perm β) →* Equiv.Perm α :=
  (e.symm.permCongrHom).toMonoidHom.comp hom

def complement (i : I) := {j : I // j ≠ i} × β

instance [Fintype I] [Fintype β] (i : I) : Fintype (complement (β:=β) i) :=
  inferInstanceAs (Fintype ({j : I // j ≠ i} × β))

lemma card_complement [Fintype I] [Fintype β] (i : I) :
    Fintype.card (complement (β:=β) i) = (Fintype.card I - 1) * Fintype.card β := by
  change Fintype.card ({j : I // j ≠ i} × β) = _
  rw [Fintype.card_prod, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

def complementIn (e : α ≃ I × β) (i : I) (x : complement (β:=β) i) : α :=
  e.symm (x.1.val, x.2)

lemma complementIn_injective (e : α ≃ I × β) (i : I) :
    Function.Injective (complementIn (β:=β) e i) := by
  intro x y h
  have hh := e.symm.injective h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun p : I × β => p.2) hh)

def restriction (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) : complement (β:=β) i → α :=
  g ∘ complementIn e i

lemma perm_single_apply (i j : I) (h : Equiv.Perm β) (b : β) :
    perm (Pi.mulSingle i h) (j,b) = if j = i then (j,h b) else (j,b) := by
  by_cases hj : j = i
  · subst j; simp [perm]
  · simp [perm, hj]

lemma embedding_apply (e : α ≃ I × β) (p : I → Equiv.Perm β) (x : α) :
    embedding e p x = e.symm (perm p (e x)) := rfl

lemma restriction_right (e : α ≃ I × β) (i : I) (g : Equiv.Perm α) (h : Equiv.Perm β) :
    restriction e i (g * embedding e (Pi.mulSingle i h)) = restriction e i g := by
  funext x
  simp only [restriction, Function.comp_apply, Equiv.Perm.coe_mul, embedding_apply,
    complementIn, e.apply_symm_apply, perm_single_apply, x.1.property, ↓reduceIte]

lemma fixes_inside (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) (b : β) : (r (i,b)).1 = i := by
  by_contra h
  have hh := hr (r (i,b)).1 (r (i,b)).2 h
  have he : (i,b) = r (i,b) := r.injective (by simpa only [Prod.mk.eta] using hh.symm)
  exact h (congrArg Prod.fst he).symm

lemma fixes_outside_inv (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) (j : I) (b : β) (hj : j ≠ i) :
    r⁻¹ (j,b) = (j,b) := by
  apply r.injective
  simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hr j b hj).symm

def extract (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) : Equiv.Perm β where
  toFun b := (r (i,b)).2
  invFun b := (r⁻¹ (i,b)).2
  left_inv b := by
    have he : (i, (r (i,b)).2) = r (i,b) := Prod.ext (fixes_inside i r hr b).symm rfl
    change (r⁻¹ (i, (r (i,b)).2)).2 = b
    rw [he, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  right_inv b := by
    have he : (i, (r⁻¹ (i,b)).2) = r⁻¹ (i,b) :=
      Prod.ext (fixes_inside i r⁻¹ (fixes_outside_inv i r hr) b).symm rfl
    change (r (i, (r⁻¹ (i,b)).2)).2 = b
    rw [he, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

lemma perm_extract (i : I) (r : Equiv.Perm (I × β))
    (hr : ∀ j b, j ≠ i → r (j,b) = (j,b)) : perm (Pi.mulSingle i (extract i r hr)) = r := by
  apply Equiv.ext
  rintro ⟨j,b⟩
  rw [perm_single_apply]
  by_cases hj : j = i
  · subst j
    simp only [↓reduceIte]
    exact Prod.ext (fixes_inside i r hr b).symm rfl
  · rw [ite_eq_right hj, hr j b hj]

lemma restriction_fiber (e : α ≃ I × β) (i : I) (g k : Equiv.Perm α)
    (hk : restriction e i k = restriction e i g) :
    ∃ h : Equiv.Perm β, g * embedding e (Pi.mulSingle i h) = k := by
  let r : Equiv.Perm (I × β) := e.permCongr (g⁻¹ * k)
  have hr (j : I) (b : β) (hj : j ≠ i) : r (j,b) = (j,b) := by
    have hh := congrFun hk (⟨j,hj⟩,b)
    change k (e.symm (j,b)) = g (e.symm (j,b)) at hh
    change e (g⁻¹ (k (e.symm (j,b)))) = (j,b)
    rw [hh, Equiv.Perm.inv_def, Equiv.symm_apply_apply, e.apply_symm_apply]
  refine ⟨extract i r hr, ?_⟩
  apply mul_left_cancel (a:=g⁻¹)
  rw [← mul_assoc, inv_mul_cancel, one_mul]
  have he := perm_extract i r hr
  apply (Equiv.permCongrHom e).injective
  change e.permCongr (e.symm.permCongr (perm (Pi.mulSingle i (extract i r hr)))) = r
  simpa only [← Equiv.permCongr_symm, Equiv.apply_symm_apply] using he

lemma single_embedding_injective (e : α ≃ I × β) (i : I) :
    Function.Injective (fun h : Equiv.Perm β => embedding e (Pi.mulSingle i h)) := by
  intro h k hh
  ext b
  have he := DFunLike.congr_fun hh (e.symm (i,b))
  simp only [embedding_apply, e.apply_symm_apply, perm_single_apply, ↓reduceIte] at he
  exact congrArg Prod.snd (e.symm.injective he)

end Thorp.Block

end

end OAI
