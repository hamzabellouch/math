import OAI.Computability.StarHeight.Episodes

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uS uM uK uS2

namespace AffineRecovery

open scoped Computability
open EpisodeAlgebra

variable {Alphabet : Type u} {S : Type uS} [AddCommGroup S]

def affine (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (e : List Alphabet) (x : S) : S := L e x + b e

lemma update_add (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (es : List (List Alphabet)) (x z : S) :
    updateWord (affine L b) (x + z) es =
      updateWord (fun e => L e) x es + updateWord (affine L b) z es := by
  induction es generalizing x z with
  | nil => rfl
  | cons e es ih =>
      simp only [updateWord_cons]
      have hh : affine L b e (x + z) = L e x + affine L b e z := by
        simp only [affine, map_add, add_assoc]
      rw [hh, ih]

lemma update_eq_linear_add (L : List Alphabet → S →+ S) (b : List Alphabet → S)
    (es : List (List Alphabet)) (x : S) :
    updateWord (affine L b) x es =
      updateWord (fun e => L e) x es + updateWord (affine L b) 0 es := by
  simpa only [add_zero] using update_add L b es x 0

theorem recovery {E D : Language Alphabet} (hE : PrefixCode E) (hDE : D ≤ E)
    (L : List Alphabet → S →+ S) (b : List Alphabet → S) (x y : S) :
    graph D (fun e => L e) x y =
      ⨆ c : S, graph D (affine L b) x (y + c) ⊓ graph D (affine L b) 0 c := by
  ext w
  rw [Language.mem_iSup]
  constructor
  · rintro ⟨es, he, rfl, hxy⟩
    refine ⟨updateWord (affine L b) 0 es, ⟨es, he, rfl, ?_⟩, es, he, rfl, rfl⟩
    rw [update_eq_linear_add, hxy]
  · rintro ⟨c, ⟨es, he, hw, hx⟩, fs, hf, hfw, hzero⟩
    have hef := flatten_injective hE (he.mono hDE) (hf.mono hDE) (hw.trans hfw.symm)
    subst fs
    refine ⟨es, he, hw, ?_⟩
    rw [update_eq_linear_add, hzero] at hx
    exact add_right_cancel hx

theorem recovery_height [Finite S] {E D : Language Alphabet}
    (hE : PrefixCode E) (hDE : D ≤ E)
    (L : List Alphabet → S →+ S) (b : List Alphabet → S) (H : ℕ)
    (hG : ∀ x y, HasHeightAtMost (graph D (affine L b) x y) H) (x y : S) :
    HasHeightAtMost (graph D (fun e => L e) x y) H := by
  rw [recovery hE hDE L b]
  exact HasHeightAtMost.iSup _ (fun c => (hG x (y + c)).inter (hG 0 c))

end AffineRecovery

namespace RightRegular

variable (M : Type uM) [Monoid M] [Finite M]

abbrev V := M → ZMod 2

noncomputable def basis : Module.Basis M (ZMod 2) (V M) := Pi.basisFun (ZMod 2) M

noncomputable def action (d : M) : V M →ₗ[ZMod 2] V M :=
  (basis M).constr (ZMod 2) (fun m => basis M (m * d))

@[simp] lemma action_basis (d m : M) : action M d (basis M m) = basis M (m * d) := by
  simp only [action, Module.Basis.constr_basis]

@[simp] lemma action_one : action M 1 = LinearMap.id := by
  apply (basis M).ext
  intro m
  simp

lemma action_mul (d e : M) : action M (d * e) = (action M e).comp (action M d) := by
  apply (basis M).ext
  intro m
  simp [mul_assoc]

omit [Monoid M] in
lemma basis_injective : Function.Injective (basis M) := (basis M).injective

lemma action_faithful : Function.Injective (action M) := by
  intro d e h
  have hh := LinearMap.congr_fun h (basis M 1)
  simp only [action_basis, one_mul] at hh
  exact basis_injective M hh

lemma value_recovery (d e : M) : action M d (basis M 1) = basis M e ↔ d = e := by
  simp only [action_basis, one_mul, (basis_injective M).eq_iff]

end RightRegular

namespace Homogenization

variable {K : Type uK} {S : Type uS2} [CommSemiring K] [AddCommMonoid S] [Module K S]

def lift (L : S →ₗ[K] S) (b : S) : (S × K) →ₗ[K] (S × K) where
  toFun u := (L u.1 + u.2 • b, u.2)
  map_add' u v := by
    ext <;> simp [add_smul, add_assoc, add_comm, add_left_comm]
  map_smul' a u := by
    ext <;> simp [smul_add, smul_smul]

@[simp] lemma lift_apply_one (L : S →ₗ[K] S) (b : S) (x : S) :
    lift L b (x, 1) = (L x + b, 1) := by simp [lift]

@[simp] lemma lift_apply_zero (L : S →ₗ[K] S) (b : S) (x : S) :
    lift L b (x, 0) = (L x, 0) := by simp [lift]

lemma lift_comp (L A : S →ₗ[K] S) (b c : S) :
    (lift A c).comp (lift L b) = lift (A.comp L) (A b + c) := by
  ext u <;> simp [lift, smul_add]

end Homogenization

end GeneralizedStarHeight

end OAI
