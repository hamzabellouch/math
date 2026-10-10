import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev rightMult (M : ModuleCat.{u} R) (r : R) : (M →ₗ[R] R) →ₗ[k] (M →ₗ[R] R) :=
  LinearMap.compRight k (LinearMap.mulRight R r)

@[simp] lemma rightMult_apply (M : ModuleCat.{u} R) (r : R) (f : M →ₗ[R] R) (x : M) :
    rightMult k R M r f x = f x * r := rfl

def Object (M : ModuleCat.{u} R) := Module.Dual k (M →ₗ[R] R)

namespace Object
variable {k R}
def value {M : ModuleCat.{u} R} (x : Object k R M) : Module.Dual k (M →ₗ[R] R) := x
instance (M : ModuleCat.{u} R) : AddCommGroup (Object k R M) := inferInstanceAs (AddCommGroup (Module.Dual k (M →ₗ[R] R)))
instance (M : ModuleCat.{u} R) : Module k (Object k R M) := inferInstanceAs (Module k (Module.Dual k (M →ₗ[R] R)))
@[ext] lemma ext {M : ModuleCat.{u} R} {x y : Object k R M} (h : ∀ f, value x f = value y f) : x = y := LinearMap.ext h
instance (M : ModuleCat.{u} R) : Module R (Object k R M) where
  smul r f := (value f).comp (rightMult k R M r)
  one_smul f := by
    ext g
    change (value f) (rightMult k R M 1 g) = (value f) g
    congr 1
    ext x
    exact mul_one _
  mul_smul r s f := by
    ext g
    change (value f) ((rightMult k R M (r*s)) g) =
      (value f) (rightMult k R M s (rightMult k R M r g))
    congr 1
    ext x
    simp [mul_assoc]
  smul_zero r := by ext g; rfl
  smul_add r f g := by ext h; rfl
  zero_smul f := by
    ext g
    change (value f) (rightMult k R M 0 g) = 0
    have : rightMult k R M 0 g = 0 := by ext x; exact mul_zero _
    rw [this, map_zero]
  add_smul r s f := by
    ext g
    change (value f) (rightMult k R M (r+s) g) =
      (value f) (rightMult k R M r g) + (value f) (rightMult k R M s g)
    rw [← map_add]
    congr 1
    ext x
    simp [mul_add]

instance (M : ModuleCat.{u} R) : SMulCommClass R k (Object k R M) where
  smul_comm r a f := by ext g; rfl
instance (M : ModuleCat.{u} R) : IsScalarTower k R (Object k R M) where
  smul_assoc a r f := by
    ext g
    change (value f) (rightMult k R M (a • r) g) = a • (value f) (rightMult k R M r g)
    rw [← map_smul]
    congr 1
    ext x
    exact mul_smul_comm _ _ _
end Object

variable {k R}
def map {M N : ModuleCat.{u} R} (f : M ⟶ N) : Object k R M →ₗ[R] Object k R N where
  toFun h := (Object.value h).comp (LinearMap.lcomp k R f.hom)
  map_add' _ _ := rfl
  map_smul' r h := by
    ext g
    change (Object.value h) (rightMult k R M r ((LinearMap.lcomp k R f.hom) g)) =
      (Object.value h) ((LinearMap.lcomp k R f.hom) (rightMult k R N r g))
    rfl

variable (k R)
def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Object k R M)
  map f := ModuleCat.ofHom (map f)
  map_id M := by ext h g; rfl
  map_comp f g := by ext h φ; rfl
instance : (functor k R).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply Object.ext
    intro φ
    change (Object.value h) ((LinearMap.lcomp k R (f+g).hom) φ) =
      (Object.value h) ((LinearMap.lcomp k R f.hom) φ) +
      (Object.value h) ((LinearMap.lcomp k R g.hom) φ)
    rw [← map_add]
    congr 1
    ext x
    exact map_add φ _ _

abbrev coind (V : ModuleCat.{u} k) :=
  (ModuleCat.coextendScalars (algebraMap k R)).obj V

instance coind_modulek (V : ModuleCat.{u} k) : Module k (coind k R V) :=
  inferInstanceAs (Module k ((ModuleCat.restrictScalars (algebraMap k R)).obj
    (ModuleCat.of R R) →ₗ[k] V))

instance coind_tower (V : ModuleCat.{u} k) : IsScalarTower k R (coind k R V) where
  smul_assoc a r h := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    change R at x
    change h (x * (a • r)) = a • h (x*r)
    rw [mul_smul_comm]
    rw [Algebra.smul_def]
    exact h.map_smul a (x*r)

instance coind_comm (V : ModuleCat.{u} k) : SMulCommClass R k (coind k R V) where
  smul_comm _ _ _ := rfl

lemma field_injective (V : ModuleCat.{u} k) : Injective V where
  factors {X Y} g f hf := by
    obtain ⟨s, hs⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp s), ?_⟩
    apply ModuleCat.hom_ext
    change g.hom.comp (s.comp f.hom) = g.hom
    rw [hs, LinearMap.comp_id]

instance coind_injective (V : ModuleCat.{u} k) : Injective (coind k R V) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R)).map_injective _
    (field_injective k V)

abbrev DA := coind k R (ModuleCat.of k k)

def daEquiv : DA k R ≃ₗ[k] Module.Dual k R where
  toFun h := {
    toFun := h
    map_add' := h.map_add
    map_smul' a r := by
      rw [Algebra.smul_def]
      exact h.map_smul a r }
  invFun h := {
    toFun := h
    map_add' := h.map_add
    map_smul' a r := by
      change R at r
      change h (algebraMap k R a * r) = a • h r
      rw [← Algebra.smul_def]
      exact h.map_smul a r }
  left_inv h := rfl
  right_inv h := rfl
  map_add' f g := rfl
  map_smul' a h := rfl

def etaMap (M : ModuleCat.{u} R) (p : M) : DA k R →ₗ[R] Object k R M where
  toFun h := (daEquiv k R h).comp (LinearMap.applyₗ' k p)
  map_add' h g := rfl
  map_smul' r h := by
    apply Object.ext
    intro φ
    change h (φ p * r) = h (φ p * r)
    rfl

@[simp] lemma etaMap_apply (M : ModuleCat.{u} R) (p : M) (h : DA k R)
    (φ : M →ₗ[R] R) : Object.value (etaMap k R M p h) φ = h (φ p) := rfl

lemma eta_natural {M N : ModuleCat.{u} R} (f : M ⟶ N) (p : M) :
    (map f).comp (etaMap k R M p) = etaMap k R N (f p) := by rfl

structure Frame (M : ModuleCat.{u} R) where
  n : ℕ
  b : Fin n → M
  c : Fin n → (M →ₗ[R] R)
  expand : ∀ x, ∑ i, c i x • b i = x

lemma frame_nonempty (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Nonempty (Frame R M) := by
  classical
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨⟨n, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i).comp g, ?_⟩⟩
  intro x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, ← map_smul, ← map_sum]
  have he : ∑ i : Fin n, g x i • Pi.single i (1 : R) = g x := by
    ext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [he]
  exact LinearMap.congr_fun hfg x

variable {k R}
lemma Frame.dual_expand {M : ModuleCat.{u} R} (F : Frame R M) (φ : M →ₗ[R] R) :
    ∑ i, rightMult k R M (φ (F.b i)) (F.c i) = φ := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.sum_apply, rightMult_apply, map_sum, map_smul,
    smul_eq_mul] using congrArg φ (F.expand x)

variable (k R)
lemma eta_injective [FiniteDimensional k R] (M : ModuleCat.{u} R)
    (F : Frame R M) : Function.Injective (etaMap k R M) := by
  intro x y h
  have hxy (i : Fin F.n) : F.c i x = F.c i y := by
    apply (Module.evalEquiv k R).injective
    apply LinearMap.ext
    intro φ
    exact congrArg (fun f : DA k R →ₗ[R] Object k R M =>
      Object.value (f ((daEquiv k R).symm φ)) (F.c i)) h
  rw [← F.expand x, ← F.expand y]
  simp only [hxy]

lemma eta_surjective [FiniteDimensional k R] (M : ModuleCat.{u} R)
    (F : Frame R M) : Function.Surjective (etaMap k R M) := by
  classical
  intro f
  let p : Fin F.n → R := fun i => (Module.evalEquiv k R).symm (
    (LinearMap.applyₗ' k (F.c i)).comp
      ((f.restrictScalars k).comp (daEquiv k R).symm.toLinearMap))
  have hp (i : Fin F.n) (h : DA k R) : h (p i) = Object.value (f h) (F.c i) := by
    change (daEquiv k R h) (p i) = _
    dsimp only [p]
    rw [Module.apply_evalEquiv_symm_apply]
    change Object.value (f ((daEquiv k R).symm (daEquiv k R h))) (F.c i) = _
    rw [LinearEquiv.symm_apply_apply]

  refine ⟨∑ i, p i • F.b i, ?_⟩
  apply LinearMap.ext
  intro h
  apply Object.ext
  intro φ
  change h (φ (∑ i, p i • F.b i)) = Object.value (f h) φ
  calc
    h (φ (∑ i, p i • F.b i)) = ∑ i, h (p i * φ (F.b i)) := by
      change (daEquiv k R h) (φ (∑ i, p i • F.b i)) = _
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl
    _ = ∑ i, Object.value (f h) (rightMult k R M (φ (F.b i)) (F.c i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show h (p i * φ (F.b i)) =
        (φ (F.b i) • h : DA k R) (p i) from rfl, hp]
      rw [map_smul]
      rfl
    _ = Object.value (f h) φ := by rw [← map_sum, F.dual_expand]

lemma coind_smul_eval (V : ModuleCat.{u} k) (g : coind k R V) (a : k) (r : R) :
    g (a • r) = a • g r := by
  rw [Algebra.smul_def]
  exact g.map_smul a r

lemma coind_add_eval (V : ModuleCat.{u} k) (g : coind k R V) (r s : R) :
    g (r+s) = g r + g s := g.map_add r s

def coindInclusion (M : ModuleCat.{u} R) :
    (functor k R).obj M ⟶ coind k R (ModuleCat.of k (Object k R M)) :=
  ModuleCat.ofHom {
    toFun := fun h => {
      toFun := fun r => (show R from r) • h
      map_add' := fun r s => add_smul _ _ _
      map_smul' := fun a r => by
        change R at r
        change (algebraMap k R a * r) • h = a • (r • h)
        rw [← Algebra.smul_def, smul_assoc] }
    map_add' := fun h g => by
      apply LinearMap.ext
      intro r
      exact smul_add _ _ _
    map_smul' := fun r h => by
      apply LinearMap.ext
      intro s
      exact (mul_smul (show R from s) r h).symm }

def coindRetraction (M : ModuleCat.{u} R) (F : Frame R M) :
    coind k R (ModuleCat.of k (Object k R M)) ⟶ (functor k R).obj M :=
  ModuleCat.ofHom {
    toFun := fun g => {
      toFun := fun φ => ∑ i, Object.value (g (φ (F.b i))) (F.c i)
      map_add' := fun φ ψ => by
        change ∑ i, Object.value (g ((φ+ψ) (F.b i))) (F.c i) = _
        have hg (r s : R) : g (r+s) = g r + g s := g.map_add r s
        simp only [LinearMap.add_apply, hg]
        change ∑ i, (Object.value (g (φ (F.b i))) (F.c i) +
          Object.value (g (ψ (F.b i))) (F.c i)) = _
        exact Finset.sum_add_distrib
      map_smul' := fun a φ => by
        change ∑ i, Object.value (g ((a • φ) (F.b i))) (F.c i) =
          a • (∑ i, Object.value (g (φ (F.b i))) (F.c i))
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun x : Object k R M => Object.value x (F.c i))
          (coind_smul_eval k R (ModuleCat.of k (Object k R M)) g a (φ (F.b i))) }
    map_add' := fun g h => by
      apply Object.ext
      intro φ
      change ∑ i, (Object.value (g (φ (F.b i))) (F.c i) +
        Object.value (h (φ (F.b i))) (F.c i)) = _
      exact Finset.sum_add_distrib
    map_smul' := fun r g => by
      apply Object.ext
      intro φ
      rfl }

lemma coindInclusion_retraction (M : ModuleCat.{u} R) (F : Frame R M) :
    coindInclusion k R M ≫ coindRetraction k R M F = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply Object.ext
  intro φ
  change ∑ i, Object.value h (rightMult k R M (φ (F.b i)) (F.c i)) = Object.value h φ
  rw [← map_sum, F.dual_expand]

lemma object_injective (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Injective ((functor k R).obj M) := by
  obtain ⟨F⟩ := frame_nonempty R M
  exact (show Retract ((functor k R).obj M) (coind k R (ModuleCat.of k (Object k R M))) from
    ⟨coindInclusion k R M, coindRetraction k R M F, coindInclusion_retraction k R M F⟩).injective

end LittleFinitistic.Nakayama

end

end OAI
