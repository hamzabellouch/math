import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Nakayama.Modules
import OAI.Algebra.FinitisticAsymmetry.Rickard.InjectiveSums

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Module
namespace LittleFinitistic.Nakayama
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma da_finite : Module.Finite R (DA k R) := by
  let : Module.Finite k (DA k R) := Module.Finite.equiv (daEquiv k R).symm
  exact Module.Finite.of_restrictScalars_finite k R _

variable {k R}
def coindLine (V : ModuleCat.{u} k) (v : V) : DA k R →ₗ[R] coind k R V :=
  ((ModuleCat.coextendScalars (algebraMap k R)).map
    (ModuleCat.ofHom ((LinearMap.id : k →ₗ[k] k).smulRight v))).hom

omit [FiniteDimensional k R] in
@[simp] lemma coindLine_apply (V : ModuleCat.{u} k) (v : V) (φ : DA k R) (r : R) :
    coindLine V v φ r = φ r • v := rfl

omit [FiniteDimensional k R] in
@[simp] private lemma coind_zero_eval (V : ModuleCat.{u} k) (r : R) :
    (0 : coind k R V) r = 0 := rfl

omit [FiniteDimensional k R] in
private lemma coind_sum_eval {J : Type*} (s : Finset J) (V : ModuleCat.{u} k)
    (f : J → coind k R V) (r : R) :
    (∑ j ∈ s, f j) r = ∑ j ∈ s, f j r := by
  change (ModuleCat.CoextendScalars.equiv (algebraMap k R) V (∑ j ∈ s, f j)) r = _
  rw [map_sum]
  exact LinearMap.sum_apply _ _ _

variable {ι : Type u}
def coindBasisMap (V : ModuleCat.{u} k) (b : Basis ι k V) :
    (Π₀ _ : ι, DA k R) →ₗ[R] coind k R V := by
  classical
  exact DFinsupp.lsum ℤ (fun i => coindLine V (b i))

omit [FiniteDimensional k R] in
lemma coindBasisMap_injective (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Injective (coindBasisMap (R := R) V b) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro φ hφ
  change φ = 0
  apply DFinsupp.ext
  intro i
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  change R at r
  change φ i r = 0
  have h := congrArg (fun g : coind k R V => b.repr (g r) i) hφ
  rw [coind_zero_eval, map_zero, Finsupp.zero_apply] at h
  change coindBasisMap V b φ = 0 at hφ
  have he : coindBasisMap V b φ r = ∑ j ∈ φ.support, φ j r • b j := by
    have hexp : coindBasisMap V b φ = ∑ j ∈ φ.support, coindLine V (b j) (φ j) := by
      simp [coindBasisMap, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
    rw [hexp, coind_sum_eval]
    simp only [coindLine_apply]
  rw [he] at h
  simp only [map_sum, map_smul, b.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  by_cases hi : i ∈ φ.support
  · simpa [hi] using h
  · have hh := DFinsupp.notMem_support_iff.mp hi
    rw [hh]
    rfl

lemma coindBasisMap_surjective
    (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Surjective (coindBasisMap (R := R) V b) := by
  classical
  intro φ
  let φ' : R →ₗ[k] V := {
    toFun := φ
    map_add' := φ.map_add
    map_smul' := coind_smul_eval k R V φ }
  let g : R →ₗ[k] Π₀ _ : ι, k := (finsuppLequivDFinsupp k).toLinearMap.comp
    (b.repr.toLinearMap.comp φ')
  obtain ⟨s, hs⟩ := Rickard.finite_support_map (R := k) (fun _ : ι => k) R g
  let c (i : ι) : DA k R := (daEquiv k R).symm ((Finsupp.lapply i).comp
    (b.repr.toLinearMap.comp φ'))
  let x : Π₀ _ : ι, DA k R := ∑ i ∈ s, DFinsupp.single i (c i)
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro r
  change R at r
  change coindBasisMap V b x r = φ r
  have he : coindBasisMap V b x r = ∑ i ∈ s, b.repr (φ r) i • b i := by
    have hx : coindBasisMap V b x = ∑ i ∈ s, coindLine V (b i) (c i) := by
      simp only [x, map_sum, coindBasisMap, DFinsupp.lsum_single]
    rw [hx, coind_sum_eval]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [he]
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ s
  · simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi]
  · have hh := hs r i hi
    change b.repr (φ r) i = 0 at hh
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply, hi, hh]

variable (k R)
lemma coindBasisMap_bijective (V : ModuleCat.{u} k) (b : Basis ι k V) :
    Function.Bijective (coindBasisMap (R := R) V b) :=
  ⟨coindBasisMap_injective V b, coindBasisMap_surjective V b⟩

def moduleCoindInclusion (M : ModuleCat.{u} R) :
    M ⟶ coind k R ((ModuleCat.restrictScalars (algebraMap k R)).obj M) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R)).unit.app M

omit [FiniteDimensional k R] in
lemma moduleCoindInclusion_mono (M : ModuleCat.{u} R) : Mono (moduleCoindInclusion k R M) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y h
  have hh := congrArg (fun g : coind k R ((ModuleCat.restrictScalars (algebraMap k R)).obj M) => g (1 : R)) h
  change (1 : R) • x = (1 : R) • y at hh
  simpa using hh

end LittleFinitistic.Nakayama

end

end OAI
