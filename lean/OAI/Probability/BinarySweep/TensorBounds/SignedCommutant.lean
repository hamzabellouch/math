import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.EvenPostselection

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

def invariantSubspace (p : A → Bool) (n : ℕ) :
    Submodule ℂ (Matrix (Fin n → A) (Fin n → A) ℂ) where
  carrier := {M | Invariant p M}
  zero_mem' := by intro g x y; simp
  add_mem' := by
    intro M N hM hN g x y
    simp only [Matrix.add_apply, hM g x y, hN g x y, mul_add]
  smul_mem' := by
    intro c M hM g x y
    simp only [Matrix.smul_apply, smul_eq_mul, hM g x y]
    ring

abbrev RealizedType (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :=
  Set.range (wordType (A := A × A) n)

def typeRepresentative (c : RealizedType A n) : Fin n → A × A := c.property.choose

lemma typeRepresentative_type (c : RealizedType A n) :
    wordType n (typeRepresentative c) = c.val := c.property.choose_spec

def invariantCode (p : A → Bool) (n : ℕ) :
    invariantSubspace p n →ₗ[ℂ] (RealizedType A n → ℂ) where
  toFun M c := M.val (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma invariantCode_injective (p : A → Bool) (n : ℕ) :
    Function.Injective (invariantCode p n) := by
  intro M N h
  apply Subtype.ext
  ext x y
  let w : Fin n → A × A := fun i => (x i,y i)
  let c : RealizedType A n := ⟨wordType n w, ⟨w,rfl⟩⟩
  have hc : wordCounts w = wordCounts (typeRepresentative c) :=
    (wordType_eq_iff n w _).mp (typeRepresentative_type c).symm
  obtain ⟨g,hg⟩ := exists_perm_eq_of_wordCounts hc
  have hx : (Prod.fst ∘ typeRepresentative c) ∘ g = x := by
    funext i
    exact congrArg Prod.fst (hg i)
  have hy : (Prod.snd ∘ typeRepresentative c) ∘ g = y := by
    funext i
    exact congrArg Prod.snd (hg i)
  have hm := M.property g (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  have hn := N.property g (Prod.fst ∘ typeRepresentative c) (Prod.snd ∘ typeRepresentative c)
  rw [hx,hy] at hm hn
  rw [hm,hn]
  exact congrArg (fun z : ℂ => signC (p ∘ (Prod.fst ∘ typeRepresentative c)) g⁻¹ *
    signC (p ∘ (Prod.snd ∘ typeRepresentative c)) g⁻¹ * z) (congrFun h c)

lemma invariantSubspace_finrank (p : A → Bool) (n : ℕ) :
    Module.finrank ℂ (invariantSubspace p n) ≤ (n+1)^((Fintype.card A)^2) := by
  let : Fintype (RealizedType A n) := Fintype.ofFinite _
  have h := LinearMap.finrank_le_finrank_of_injective (f := invariantCode p n)
    (invariantCode_injective p n)
  rw [Module.finrank_pi] at h
  have hc := Fintype.card_le_of_injective (fun c : RealizedType A n => c.val) Subtype.val_injective
  have ht := card_types_le (A := A × A) n
  simp only [Fintype.card_coe, Fintype.card_prod, ← pow_two] at hc ht
  exact h.trans (hc.trans ht)

omit [Fintype A] in
lemma act_single_comp (p : A → Bool) (g : Equiv.Perm (Fin n)) (y : Fin n → A) :
    act p g (Pi.single (y ∘ g) (1 : ℂ)) =
      signC (p ∘ y) g⁻¹ • Pi.single y (1 : ℂ) := by
  funext x
  change signC (p ∘ x) g⁻¹ * ((Pi.single (y ∘ g) (1 : ℂ) : (Fin n → A) → ℂ) (x ∘ g)) = _
  by_cases h : x=y
  · subst x
    simp
  · have hg : x ∘ g ≠ y ∘ g := by
      intro he
      apply h
      funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun he (g.symm i)
    simp [h, hg]

lemma intertwiner_matrix_invariant (p : A → Bool)
    (f : Representation.IntertwiningMap (tensorRep p n) (tensorRep p n)) :
    Invariant p (LinearMap.toMatrix' f.toLinearMap) := by
  intro g x y
  have h := congrFun (Representation.IntertwiningMap.isIntertwining _ _ f g (Pi.single (y ∘ g) (1 : ℂ))) x
  change f (act p g (Pi.single (y ∘ g) 1)) x = signC (p ∘ x) g⁻¹ * f (Pi.single (y ∘ g) 1) (x ∘ g) at h
  rw [act_single_comp, map_smul] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  simp only [LinearMap.toMatrix'_apply, Representation.IntertwiningMap.toLinearMap_apply]
  have hs := signC_sq (p ∘ x) g⁻¹
  calc
    _ = (signC (p ∘ x) g⁻¹ * signC (p ∘ x) g⁻¹) * f (Pi.single (y ∘ g) 1) (x ∘ g) := by rw [hs,one_mul]
    _ = _ := by rw [mul_assoc, ← h]; ring

def commutantToInvariant (p : A → Bool) (n : ℕ) :
    Representation.IntertwiningMap (tensorRep p n) (tensorRep p n) →ₗ[ℂ]
      invariantSubspace p n where
  toFun f := ⟨LinearMap.toMatrix' f.toLinearMap, intertwiner_matrix_invariant p f⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp

lemma commutantToInvariant_injective (p : A → Bool) (n : ℕ) :
    Function.Injective (commutantToInvariant p n) := by
  intro f g h
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  exact congrArg Subtype.val h

theorem tensor_commutant_finrank (p : A → Bool) (n : ℕ) :
    Module.finrank ℂ (Representation.IntertwiningMap (tensorRep p n) (tensorRep p n)) ≤
      (n+1)^((Fintype.card A)^2) :=
  (LinearMap.finrank_le_finrank_of_injective (f := commutantToInvariant p n)
    (commutantToInvariant_injective p n)).trans (invariantSubspace_finrank p n)

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] {n : ℕ}

abbrev TensorSpace (A : Type*) (n : ℕ) := EuclideanSpace ℂ (Fin n → A)

def coeffEquiv (A : Type*) [Fintype A] (n : ℕ) :
    TensorSpace A n ≃ₗ[ℂ] ((Fin n → A) → ℂ) := WithLp.linearEquiv 2 ℂ _

def wordReorder (g : Equiv.Perm (Fin n)) : (Fin n → A) ≃ (Fin n → A) where
  toFun x := x ∘ g
  invFun x := x ∘ g.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

def actHilbert (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    TensorSpace A n →ₗ[ℂ] TensorSpace A n := (coeffEquiv A n).symm.conj (act p g)

lemma actHilbert_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) (x) :
    actHilbert p g v x = signC (p ∘ x) g⁻¹ * v (x ∘ g) := rfl

lemma actHilbert_inner (p : A → Bool) (g : Equiv.Perm (Fin n)) (v w : TensorSpace A n) :
    inner ℂ (actHilbert p g v) (actHilbert p g w) = inner ℂ v w := by
  simp only [PiLp.inner_apply, actHilbert_apply, RCLike.inner_apply, map_mul,
    starRingEnd_apply, signC_star]
  have he (x : Fin n → A) : signC (p ∘ x) g⁻¹ * w (x ∘ g) *
      (signC (p ∘ x) g⁻¹ * star (v (x ∘ g))) = w (x ∘ g) * star (v (x ∘ g)) := by
    calc
      _ = (signC (p ∘ x) g⁻¹ * signC (p ∘ x) g⁻¹) *
          (w (x ∘ g) * star (v (x ∘ g))) := by ring
      _ = _ := by rw [signC_sq, one_mul]
  simp_rw [he]
  exact Equiv.sum_comp (wordReorder g) (fun x => w x * star (v x))

def actionIsometry (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    TensorSpace A n →ₗᵢ[ℂ] TensorSpace A n := (actHilbert p g).isometryOfInner (actHilbert_inner p g)

def hilbertSubspace (S : Submodule ℂ ((Fin n → A) → ℂ)) : Submodule ℂ (TensorSpace A n) :=
  S.map (coeffEquiv A n).symm.toLinearMap

lemma hilbertSubspace_finrank (S : Submodule ℂ ((Fin n → A) → ℂ)) :
    Module.finrank ℂ (hilbertSubspace S) = Module.finrank ℂ S :=
  (Submodule.equivMapOfInjective (coeffEquiv A n).symm.toLinearMap
    (coeffEquiv A n).symm.injective S).finrank_eq.symm

lemma hilbertSubspace_map (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) (g : Equiv.Perm (Fin n)) :
    (hilbertSubspace S).map (actHilbert p g) = hilbertSubspace S := by
  apply le_antisymm
  · rintro _ ⟨u,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨act p g v, ?_, ?_⟩
    · rw [← hS g]
      exact ⟨v,hv,rfl⟩
    · simp only [actHilbert, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨v,hv,rfl⟩
    have hm : v ∈ S.map (act p g) := (hS g).symm ▸ hv
    obtain ⟨w,hw,rfl⟩ := hm
    refine ⟨(coeffEquiv A n).symm w, ⟨w,hw,rfl⟩, ?_⟩
    simp only [actHilbert, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

end BinaryCoordinateSweeps.Signed

end

end OAI
