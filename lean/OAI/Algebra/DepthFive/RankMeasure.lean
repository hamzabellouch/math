import Mathlib

namespace OAI

/-!
# Finite-dimensional rank bookkeeping

The differentiation--multiplication measure is obtained by applying a linear
family of linear maps to a polynomial. Its rank can be studied independently
of the construction of that family and the choice of homogeneous spaces.
-/

noncomputable section

open scoped BigOperators

namespace Problem335
namespace RankMeasure

universe u v w x y

variable {K : Type u} [Field K]
variable {P : Type v} [AddCommGroup P] [Module K P]
variable {V : Type w} [AddCommGroup V] [Module K V]
variable {W : Type x} [AddCommGroup W] [Module K W]
variable {Z : Type y} [AddCommGroup Z] [Module K Z]

/-- The natural-number rank of a linear map. Its use below always has a
finite-dimensional source, or an explicit finite-dimensional factorization. -/
def mapRank (f : V →ₗ[K] W) : ℕ := Module.finrank K (LinearMap.range f)

@[simp] theorem mapRank_zero : mapRank (0 : V →ₗ[K] W) = 0 := by
  rw [mapRank, LinearMap.range_zero, finrank_bot]

theorem mapRank_smul (f : V →ₗ[K] W) (a : K) (ha : a ≠ 0) :
    mapRank (a • f) = mapRank f := by
  unfold mapRank
  rw [LinearMap.range_smul f a ha]

theorem mapRank_smul_le [FiniteDimensional K V] (f : V →ₗ[K] W) (a : K) :
    mapRank (a • f) ≤ mapRank f := by
  exact Submodule.finrank_mono (LinearMap.range_smul_le_range f a)

theorem mapRank_add_le [FiniteDimensional K V] (f g : V →ₗ[K] W) :
    mapRank (f + g) ≤ mapRank f + mapRank g := by
  have h := LinearMap.rank_add_le f g
  rw [LinearMap.rank, LinearMap.rank, LinearMap.rank,
    ← Module.finrank_eq_rank, ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem mapRank_sum_le [FiniteDimensional K V] {ι : Type*}
    (s : Finset ι) (f : ι → V →ₗ[K] W) :
    mapRank (∑ i ∈ s, f i) ≤ ∑ i ∈ s, mapRank (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (mapRank_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mapRank_comp_le_left [FiniteDimensional K Z]
    (f : V →ₗ[K] Z) (g : Z →ₗ[K] W) :
    mapRank (g.comp f) ≤ mapRank g := by
  apply Submodule.finrank_mono
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

theorem mapRank_comp_le_right [FiniteDimensional K V]
    (f : V →ₗ[K] Z) (g : Z →ₗ[K] W) :
    mapRank (g.comp f) ≤ mapRank f := by
  unfold mapRank
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le g (LinearMap.range f)

/-- Factorization through a finite-dimensional intermediate space bounds rank. -/
theorem mapRank_factor_le [FiniteDimensional K Z]
    (f : V →ₗ[K] Z) (g : Z →ₗ[K] W) :
    mapRank (g.comp f) ≤ Module.finrank K Z :=
  (mapRank_comp_le_left f g).trans g.finrank_range_le

/-- Changing to finite bases identifies our rank convention with matrix rank. -/
theorem mapRank_eq_matrixRank {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (f : V →ₗ[K] W) :
    mapRank f = (LinearMap.toMatrix bV bW f).rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin _ bW bV]
  rw [Matrix.toLin_toMatrix]
  rfl

/-- The rank of a restricted map does not depend on whether its codomain is
viewed as a subspace or as the ambient space. -/
theorem mapRank_subtype_comp (S : Submodule K W) (f : V →ₗ[K] S) :
    mapRank (S.subtype.comp f) = mapRank f := by
  unfold mapRank
  rw [LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype f.range).finrank_eq.symm

/-- Restrict the source of a linear operator family to a chosen homogeneous
subspace, leaving the codomain ambient. This avoids unnecessary transports
between equivalent descriptions of the target homogeneous space. -/
def restrictFamily (F : P →ₗ[K] (V →ₗ[K] W)) (S : Submodule K V) :
    P →ₗ[K] (S →ₗ[K] W) where
  toFun p := (F p).comp S.subtype
  map_add' p q := by ext x; simp
  map_smul' a p := by ext x; simp

@[simp] theorem restrictFamily_apply (F : P →ₗ[K] (V →ₗ[K] W))
    (S : Submodule K V) (p : P) (x : S) :
    restrictFamily F S p x = F p x := rfl

/-- In a product of operators, it suffices to show that the first part sends
the source subspace into a finite-dimensional intermediate subspace. -/
theorem mapRank_restrict_factor_le (S : Submodule K V) (I : Submodule K Z)
    [FiniteDimensional K I] (f : V →ₗ[K] Z) (g : Z →ₗ[K] W)
    (hf : ∀ x : S, f x ∈ I) :
    mapRank ((g.comp f).comp S.subtype) ≤ Module.finrank K I := by
  let f' : S →ₗ[K] I := (f.comp S.subtype).codRestrict I hf
  have h : (g.comp f).comp S.subtype = (g.comp I.subtype).comp f' := by
    ext x
    rfl
  rw [h]
  exact mapRank_factor_le f' (g.comp I.subtype)

/-- A rank measure associated with a linear family of linear maps. -/
def measure (F : P →ₗ[K] (V →ₗ[K] W)) (p : P) : ℕ := mapRank (F p)

@[simp] theorem measure_zero (F : P →ₗ[K] (V →ₗ[K] W)) :
    measure F 0 = 0 := by
  simp [measure]

theorem measure_smul (F : P →ₗ[K] (V →ₗ[K] W)) (a : K) (ha : a ≠ 0) (p : P) :
    measure F (a • p) = measure F p := by
  simpa only [measure, map_smul] using mapRank_smul (F p) a ha

theorem measure_smul_le [FiniteDimensional K V]
    (F : P →ₗ[K] (V →ₗ[K] W)) (a : K) (p : P) :
    measure F (a • p) ≤ measure F p := by
  simpa only [measure, map_smul] using mapRank_smul_le (F p) a

theorem measure_add_le [FiniteDimensional K V]
    (F : P →ₗ[K] (V →ₗ[K] W)) (p q : P) :
    measure F (p + q) ≤ measure F p + measure F q := by
  simpa only [measure, map_add] using mapRank_add_le (F p) (F q)

theorem measure_sum_le [FiniteDimensional K V] {ι : Type*}
    (F : P →ₗ[K] (V →ₗ[K] W)) (s : Finset ι) (p : ι → P) :
    measure F (∑ i ∈ s, p i) ≤ ∑ i ∈ s, measure F (p i) := by
  simpa only [measure, map_sum] using mapRank_sum_le s (fun i => F (p i))

/-- Scalar coefficients introduce no extra rank cost, including zero coefficients. -/
theorem measure_sum_smul_le [FiniteDimensional K V] {ι : Type*}
    (F : P →ₗ[K] (V →ₗ[K] W)) (s : Finset ι) (a : ι → K) (p : ι → P) :
    measure F (∑ i ∈ s, a i • p i) ≤ ∑ i ∈ s, measure F (p i) := by
  refine (measure_sum_le F s _).trans ?_
  exact Finset.sum_le_sum fun i _ => measure_smul_le F (a i) (p i)

/-- A sum of at most `s.card` contributions of rank at most `B` has rank at
most `s.card * B`. This is the gate-counting step for additive layers. -/
theorem measure_sum_smul_le_card_mul [FiniteDimensional K V] {ι : Type*}
    (F : P →ₗ[K] (V →ₗ[K] W)) (s : Finset ι) (a : ι → K) (p : ι → P)
    (B : ℕ) (hB : ∀ i ∈ s, measure F (p i) ≤ B) :
    measure F (∑ i ∈ s, a i • p i) ≤ s.card * B := by
  refine (measure_sum_smul_le F s a p).trans ?_
  simpa using Finset.sum_le_sum hB

/-- Each summand may factor through its own finite-dimensional intermediate
space, as occurs when bidegrees of the factors are fixed separately. -/
theorem mapRank_sum_factor_le [FiniteDimensional K V] {ι : Type*}
    {Z' : ι → Type y} [∀ i, AddCommGroup (Z' i)] [∀ i, Module K (Z' i)]
    [∀ i, FiniteDimensional K (Z' i)] (s : Finset ι)
    (f : ∀ i, V →ₗ[K] Z' i) (g : ∀ i, Z' i →ₗ[K] W) :
    mapRank (∑ i ∈ s, (g i).comp (f i)) ≤
      ∑ i ∈ s, Module.finrank K (Z' i) := by
  refine (mapRank_sum_le s _).trans ?_
  exact Finset.sum_le_sum fun i _ => mapRank_factor_le (f i) (g i)

theorem measure_le_sum_of_factorizations [FiniteDimensional K V] {ι : Type*}
    {Z' : ι → Type y} [∀ i, AddCommGroup (Z' i)] [∀ i, Module K (Z' i)]
    [∀ i, FiniteDimensional K (Z' i)]
    (F : P →ₗ[K] (V →ₗ[K] W)) (p : P) (s : Finset ι)
    (f : ∀ i, V →ₗ[K] Z' i) (g : ∀ i, Z' i →ₗ[K] W)
    (hF : F p = ∑ i ∈ s, (g i).comp (f i)) :
    measure F p ≤ ∑ i ∈ s, Module.finrank K (Z' i) := by
  rw [measure, hF]
  exact mapRank_sum_factor_le s f g

end RankMeasure
end Problem335

end

end OAI
