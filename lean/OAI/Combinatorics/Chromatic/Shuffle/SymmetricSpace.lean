import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.Cut

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

def symmetricSpace (d : I → ℕ) : Subalgebra ℚ (MvPolynomial (Σi, Fin (d i)) ℚ) where
  carrier := {f | PackSymmetric d f}
  mul_mem' := by intro f g hf hg σ; simp only [map_mul, hf σ, hg σ]
  one_mem' := by intro σ; exact map_one _
  add_mem' := by intro f g hf hg σ; simp only [map_add, hf σ, hg σ]
  zero_mem' := by intro σ; exact map_zero _
  algebraMap_mem' := by intro r σ; simp

abbrev S (d : I → ℕ) := ↥(symmetricSpace d)

noncomputable def shufflePolynomial (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g : S e) : S (d+e) :=
  ⟨Classical.choose (rawShuffle_polynomial a f.val f.property g.val g.property),
    (Classical.choose_spec (rawShuffle_polynomial a f.val f.property g.val g.property)).1⟩

lemma shufflePolynomial_eq (a : I → I → ℕ) {d e : I → ℕ} (f : S d) (g : S e) :
    algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
      (shufflePolynomial a f g).val = rawShuffle a f.val g.val :=
  (Classical.choose_spec (rawShuffle_polynomial a f.val f.property g.val g.property)).2.symm

lemma rawShuffle_add_left (a : I → I → ℕ) {d e : I → ℕ}
    (f f' : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a (f+f') g = rawShuffle a f g + rawShuffle a f' g := by
  simp only [rawShuffle, cutNumerator, map_add, add_mul, add_div,
    Finset.sum_add_distrib]

lemma rawShuffle_add_right (a : I → I → ℕ) {d e : I → ℕ}
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g g' : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a f (g+g') = rawShuffle a f g + rawShuffle a f g' := by
  simp only [rawShuffle, cutNumerator, map_add, mul_add, add_mul, add_div,
    Finset.sum_add_distrib]

lemma rawShuffle_smul_left (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a (r • f) g = r • rawShuffle a f g := by
  let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
    (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
  simp only [rawShuffle, cutNumerator, map_smul, map_rat_smul, smul_mul_assoc,
    div_eq_mul_inv, smul_mul_assoc, Finset.smul_sum]

lemma rawShuffle_smul_right (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    rawShuffle a f (r • g) = r • rawShuffle a f g := by
  let : DistribSMul ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ)) :=
    (inferInstance : Module ℚ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))).toDistribMulAction.toDistribSMul
  simp only [rawShuffle, cutNumerator, map_smul, map_rat_smul, mul_smul_comm, smul_mul_assoc,
    div_eq_mul_inv, smul_mul_assoc, Finset.smul_sum]

@[simp] lemma shufflePolynomial_add_left (a : I → I → ℕ) {d e : I → ℕ}
    (f f' : S d) (g : S e) :
    shufflePolynomial a (f+f') g = shufflePolynomial a f g + shufflePolynomial a f' g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_add, map_add, shufflePolynomial_eq, rawShuffle_add_left]

@[simp] lemma shufflePolynomial_add_right (a : I → I → ℕ) {d e : I → ℕ}
    (f : S d) (g g' : S e) :
    shufflePolynomial a f (g+g') = shufflePolynomial a f g + shufflePolynomial a f g' := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_add, map_add, shufflePolynomial_eq, rawShuffle_add_right]

@[simp] lemma shufflePolynomial_smul_left (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : S d) (g : S e) : shufflePolynomial a (r • f) g = r • shufflePolynomial a f g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_smul, map_rat_smul, shufflePolynomial_eq, rawShuffle_smul_left]

@[simp] lemma shufflePolynomial_smul_right (a : I → I → ℕ) {d e : I → ℕ} (r : ℚ)
    (f : S d) (g : S e) : shufflePolynomial a f (r • g) = r • shufflePolynomial a f g := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  simp only [Subalgebra.coe_smul, map_rat_smul, shufflePolynomial_eq, rawShuffle_smul_right]

noncomputable def shuffleLinear (a : I → I → ℕ) (d e : I → ℕ) :
    S d →ₗ[ℚ] S e →ₗ[ℚ] S (d+e) where
  toFun f :=
    { toFun := shufflePolynomial a f
      map_add' := shufflePolynomial_add_right a f
      map_smul' := fun r g => shufflePolynomial_smul_right a r f g }
  map_add' f f' := by apply LinearMap.ext; intro g; exact shufflePolynomial_add_left a f f' g
  map_smul' r f := by apply LinearMap.ext; intro g; exact shufflePolynomial_smul_left a r f g

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def translation {α : Type*} (t : ℚ) :
    MvPolynomial α ℚ →ₐ[ℚ] MvPolynomial α ℚ :=
  aeval fun i => X i + C t

@[simp] lemma translation_X {α : Type*} (t : ℚ) (i : α) :
    translation t (X i) = X i + C t := by simp [translation]
@[simp] lemma translation_C {α : Type*} (t r : ℚ) :
    translation (α := α) t (C r) = C r := by simp [translation]

lemma translation_rename {α β : Type*} (t : ℚ) (f : α → β) (p : MvPolynomial α ℚ) :
    translation t (rename f p) = rename f (translation t p) := by
  have h : (translation t).comp (rename f) = (rename f).comp (translation t) := by
    ext i; simp
  exact DFunLike.congr_fun h p

lemma translation_add {α : Type*} (t s : ℚ) (p : MvPolynomial α ℚ) :
    translation t (translation s p) = translation (t+s) p := by
  have h : (translation (α := α) t).comp (translation s) = translation (t+s) := by
    ext i; simp [map_add]; ring
  exact DFunLike.congr_fun h p

@[simp] lemma translation_zero {α : Type*} (p : MvPolynomial α ℚ) :
    translation 0 p = p := by
  have h : translation (α := α) 0 = AlgHom.id ℚ _ := by ext i; simp
  exact DFunLike.congr_fun h p

noncomputable def translationEquiv {α : Type*} (t : ℚ) :
    MvPolynomial α ℚ ≃ₐ[ℚ] MvPolynomial α ℚ :=
  AlgEquiv.ofAlgHom (translation t) (translation (-t))
    (by ext p; simp [AlgHom.comp_apply])
    (by ext p; simp [AlgHom.comp_apply])

noncomputable def translationFraction {α : Type*} (t : ℚ) :
    FractionRing (MvPolynomial α ℚ) →+* FractionRing (MvPolynomial α ℚ) :=
  IsFractionRing.lift (g := (algebraMap _ _).comp (translation (α := α) t).toRingHom)
    ((IsFractionRing.injective _ (FractionRing (MvPolynomial α ℚ))).comp
      (translationEquiv t).injective)

@[simp] lemma translationFraction_algebraMap {α : Type*} (t : ℚ) (p : MvPolynomial α ℚ) :
    translationFraction t (algebraMap _ (FractionRing (MvPolynomial α ℚ)) p) =
      algebraMap _ (FractionRing (MvPolynomial α ℚ)) (translation t p) := by
  apply IsFractionRing.lift_algebraMap

@[simp] lemma translation_diagonal {α : Type*} (t : ℚ) (i j : α) :
    translation t (diagonal i j) = diagonal i j := by
  simp [diagonal]

omit [Fintype I] [DecidableEq I] in
lemma translation_cutFactor {d e : I → ℕ} (t : ℚ) (A : Cut d e) (i j : I) (k : ℕ) :
    translation t (cutFactor A i j k) = cutFactor A i j k := by
  simp [cutFactor]

omit [DecidableEq I] in
lemma translation_cutDenominator {d e : I → ℕ} (t : ℚ) (A : Cut d e) :
    translation t (cutDenominator A) = cutDenominator A := by
  simp [cutDenominator, translation_cutFactor]

omit [DecidableEq I] in
lemma translation_cutNumerator (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ) (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    translation t (cutNumerator a A f g) =
      cutNumerator a A (translation t f) (translation t g) := by
  simp [cutNumerator, translation_rename, translation_cutFactor]

lemma translation_rawShuffle (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    translationFraction t (rawShuffle a f g) =
      rawShuffle a (translation t f) (translation t g) := by
  simp only [rawShuffle, map_sum, map_div₀, translationFraction_algebraMap,
    translation_cutNumerator, translation_cutDenominator]

omit [Fintype I] [DecidableEq I] in
lemma translation_symmetric {d : I → ℕ} (t : ℚ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f) :
    PackSymmetric d (translation t f) := by
  intro σ
  rw [← translation_rename, hf σ]

noncomputable def translationS (d : I → ℕ) (t : ℚ) : S d →ₗ[ℚ] S d :=
  { toFun := fun f => ⟨translation t f.val, translation_symmetric t f.val f.property⟩
    map_add' := by intros; apply Subtype.ext; apply map_add
    map_smul' := by intros; apply Subtype.ext; apply map_smul }

lemma translation_shufflePolynomial (a : I → I → ℕ) {d e : I → ℕ} (t : ℚ)
    (f : S d) (g : S e) :
    translationS (d+e) t (shufflePolynomial a f g) =
      shufflePolynomial a (translationS d t f) (translationS e t g) := by
  apply Subtype.ext
  apply IsFractionRing.injective _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
  change algebraMap _ _ (translation t (shufflePolynomial a f g).val) = _
  calc
    _ = translationFraction t
        (algebraMap _ (FractionRing (MvPolynomial (Σi,Fin (d i+e i)) ℚ))
          (shufflePolynomial a f g).val) :=
      (translationFraction_algebraMap t (shufflePolynomial a f g).val).symm
    _ = _ := by
      rw [shufflePolynomial_eq, translation_rawShuffle, shufflePolynomial_eq]
      rfl

noncomputable def dimensionCast {d e : I → ℕ} (h : d = e) : S d →ₗ[ℚ] S e :=
  h ▸ LinearMap.id

omit [Fintype I] [DecidableEq I] in
@[simp] lemma dimensionCast_rfl (d : I → ℕ) (f : S d) :
    dimensionCast rfl f = f := rfl

omit [Fintype I] [DecidableEq I] in
lemma translation_dimensionCast {d e : I → ℕ} (h : d = e) (t : ℚ) (f : S d) :
    translationS e t (dimensionCast h f) = dimensionCast h (translationS d t f) := by
  subst e; rfl

def destabilizingGenerators (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) : Set (S d) :=
  { F | ∃ (u v : I → ℕ) (h : u+v=d) (f : S u) (g : S v),
      u ≠ 0 ∧ v ≠ 0 ∧ μ u > μ d ∧ F = dimensionCast h (shufflePolynomial a f g) }

noncomputable def destabilizingSpace (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    Submodule ℚ (S d) := Submodule.span ℚ (destabilizingGenerators a μ d)

lemma translation_generator (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) {f : S d} (hf : f ∈ destabilizingGenerators a μ d) :
    translationS d t f ∈ destabilizingGenerators a μ d := by
  obtain ⟨u,v,h,f,g,hu,hv,hμ,rfl⟩ := hf
  refine ⟨u,v,h,translationS u t f,translationS v t g,hu,hv,hμ,?_⟩
  rw [translation_dimensionCast, translation_shufflePolynomial]

lemma translation_destabilizing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (t : ℚ) :
    destabilizingSpace a μ d ≤
      (destabilizingSpace a μ d).comap (translationS d t) := by
  apply Submodule.span_le.mpr
  intro f hf
  exact Submodule.subset_span (translation_generator a μ d t hf)

abbrev B (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :=
  S d ⧸ destabilizingSpace a μ d

noncomputable def translationB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) : B a μ d →ₗ[ℚ] B a μ d :=
  (destabilizingSpace a μ d).mapQ (destabilizingSpace a μ d) (translationS d t)
    (translation_destabilizing a μ d t)

@[simp] lemma translationB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) (f : S d) :
    translationB a μ d t ((destabilizingSpace a μ d).mkQ f) =
      (destabilizingSpace a μ d).mkQ (translationS d t f) := rfl

omit [Fintype I] [DecidableEq I] in
lemma translationS_add (d : I → ℕ) (t s : ℚ) (f : S d) :
    translationS d t (translationS d s f) = translationS d (t+s) f := by
  apply Subtype.ext
  exact translation_add t s f.val

omit [Fintype I] [DecidableEq I] in
@[simp] lemma translationS_zero (d : I → ℕ) (f : S d) : translationS d 0 f = f := by
  apply Subtype.ext
  exact translation_zero f.val

lemma translationB_add (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t s : ℚ) (f : B a μ d) :
    translationB a μ d t (translationB a μ d s f) = translationB a μ d (t+s) f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (destabilizingSpace a μ d).mkQ (translationS_add d t s f)

@[simp] lemma translationB_zero (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (f : B a μ d) : translationB a μ d 0 f = f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (destabilizingSpace a μ d).mkQ (translationS_zero d f)

noncomputable def translationBEquiv (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t : ℚ) : B a μ d ≃ₗ[ℚ] B a μ d :=
  LinearEquiv.ofLinearMap (translationB a μ d t) (translationB a μ d (-t))
    (by ext f; simp [LinearMap.comp_apply, translationB_add])
    (by ext f; simp [LinearMap.comp_apply, translationB_add])

end ElementaryPositivity.RawShuffle

end

end OAI
