import OAI.Algebra.AuslanderReiten.Complete.SelfInjectiveComplex
import OAI.Algebra.AuslanderReiten.Modules.CoinducedEmbedding
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

structure FiniteLeftModule where
  carrier : ModuleCat.{u} R
  [scalar : Module k carrier]
  [tower : IsScalarTower k R carrier]
  [finite : Module.Finite k carrier]

attribute [instance] FiniteLeftModule.scalar FiniteLeftModule.tower FiniteLeftModule.finite

namespace FiniteLeftModule

variable {k R} [Module.Finite k R]

structure FreeCover (M : FiniteLeftModule k R) where
  rank : ℕ
  map : (Fin rank → R) →ₗ[R] M.carrier
  surjective : Function.Surjective map

noncomputable def cover (M : FiniteLeftModule k R) : FreeCover M := by
  let := Module.Finite.of_restrictScalars_finite k R M.carrier
  let h := Module.Finite.exists_fin' R M.carrier
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

noncomputable def syzygy (M : FiniteLeftModule k R) : FiniteLeftModule k R where
  carrier := ModuleCat.of R (LinearMap.ker M.cover.map)
  scalar := inferInstance
  tower := inferInstance
  finite := Module.Finite.of_injective
    ((LinearMap.ker M.cover.map).subtype.restrictScalars k) Subtype.val_injective

noncomputable def syzygies (M : FiniteLeftModule k R) : ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (syzygies M n).syzygy

noncomputable def envelopeRank (M : FiniteLeftModule k R) : ℕ :=
  Module.finrank k M.carrier

noncomputable def envelopeMap (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    M.carrier →ₗ[R] (Fin M.envelopeRank → R) := τ.finiteFreeEmbedding

theorem envelopeMap_injective (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    Function.Injective (M.envelopeMap τ) := τ.finiteFreeEmbedding_injective

noncomputable def cosyzygy (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    FiniteLeftModule k R where
  carrier := ModuleCat.of R ((Fin M.envelopeRank → R) ⧸ LinearMap.range (M.envelopeMap τ))
  scalar := inferInstance
  tower := inferInstance
  finite := inferInstance

noncomputable def cosyzygies (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ℕ → FiniteLeftModule k R
  | 0 => M
  | n + 1 => (cosyzygies τ M n).cosyzygy τ

noncomputable abbrev positiveTerm (M : FiniteLeftModule k R) (n : ℕ) :=
  Fin (M.syzygies n).cover.rank → R

noncomputable def positiveDifferential (M : FiniteLeftModule k R) (n : ℕ) :
    M.positiveTerm (n + 1) →ₗ[R] M.positiveTerm n :=
  (LinearMap.ker (M.syzygies n).cover.map).subtype.comp (M.syzygies (n + 1)).cover.map

theorem positiveDifferential_range (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.positiveDifferential n) = LinearMap.ker (M.syzygies n).cover.map := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((M.syzygies (n + 1)).cover.map y).property
  · intro hx
    obtain ⟨y, hy⟩ := (M.syzygies (n + 1)).cover.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

theorem positiveDifferential_kernel (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.ker (M.positiveDifferential n) = LinearMap.ker (M.syzygies (n + 1)).cover.map := by
  ext x
  change ((M.syzygies (n + 1)).cover.map x).val = 0 ↔ (M.syzygies (n + 1)).cover.map x = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem positiveDifferential_exact (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.positiveDifferential (n + 1)) =
      LinearMap.ker (M.positiveDifferential n) := by
  rw [positiveDifferential_range, positiveDifferential_kernel]

noncomputable abbrev negativeTerm (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (n : ℕ) :=
  Fin (M.cosyzygies τ n).envelopeRank → R

noncomputable def negativeDifferential (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    M.negativeTerm τ n →ₗ[R] M.negativeTerm τ (n + 1) :=
  ((M.cosyzygies τ (n + 1)).envelopeMap τ).comp
    (LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)).mkQ

theorem negativeDifferential_range (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.negativeDifferential τ n) =
      LinearMap.range ((M.cosyzygies τ (n + 1)).envelopeMap τ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)) y
    exact ⟨z, rfl⟩

theorem negativeDifferential_kernel (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.ker (M.negativeDifferential τ n) =
      LinearMap.range ((M.cosyzygies τ n).envelopeMap τ) := by
  ext x
  change ((M.cosyzygies τ (n + 1)).envelopeMap τ)
    ((LinearMap.range ((M.cosyzygies τ n).envelopeMap τ)).mkQ x) = 0 ↔ _
  exact (map_eq_zero_iff _ ((M.cosyzygies τ (n + 1)).envelopeMap_injective τ)).trans
    (Submodule.Quotient.mk_eq_zero _)

theorem negativeDifferential_exact (τ : FrobeniusTrace k R)
    (M : FiniteLeftModule k R) (n : ℕ) :
    LinearMap.range (M.negativeDifferential τ n) =
      LinearMap.ker (M.negativeDifferential τ (n + 1)) := by
  rw [negativeDifferential_range, negativeDifferential_kernel]

noncomputable def seam (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    M.positiveTerm 0 →ₗ[R] M.negativeTerm τ 0 :=
  (M.envelopeMap τ).comp M.cover.map

theorem seam_range (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    LinearMap.range (M.seam τ) = LinearMap.range (M.envelopeMap τ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := M.cover.surjective y
    exact ⟨z, rfl⟩

theorem seam_kernel (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    LinearMap.ker (M.seam τ) = LinearMap.ker M.cover.map := by
  ext x
  exact map_eq_zero_iff _ (M.envelopeMap_injective τ)

noncomputable def term (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) : ℤ → ModuleCat.{u} R
  | Int.ofNat n => ModuleCat.of R (M.positiveTerm n)
  | Int.negSucc n => ModuleCat.of R (M.negativeTerm τ n)

noncomputable def differential (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    (i : ℤ) → M.term τ (i + 1) ⟶ M.term τ i
  | Int.ofNat n => ModuleCat.ofHom (M.positiveDifferential n)
  | Int.negSucc 0 => ModuleCat.ofHom (M.seam τ)
  | Int.negSucc (n + 1) => ModuleCat.ofHom (M.negativeDifferential τ n)

theorem adjacent_exact (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (i : ℤ) :
    LinearMap.range (M.differential τ (i + 1)).hom =
      LinearMap.ker (M.differential τ i).hom := by
  cases i with
  | ofNat n => exact M.positiveDifferential_exact n
  | negSucc n =>
    cases n with
    | zero =>
      change LinearMap.range (M.positiveDifferential 0) = LinearMap.ker (M.seam τ)
      rw [positiveDifferential_range, seam_kernel]
      rfl
    | succ n =>
      cases n with
      | zero =>
        change LinearMap.range (M.seam τ) = LinearMap.ker (M.negativeDifferential τ 0)
        rw [seam_range, negativeDifferential_kernel]
        rfl
      | succ n => exact M.negativeDifferential_exact τ n

theorem differential_square (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (i : ℤ) :
    M.differential τ (i + 1) ≫ M.differential τ i = 0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.range_le_ker_iff.mp (M.adjacent_exact τ i).le

noncomputable def completeComplex (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of (M.term τ) (M.differential τ) (M.differential_square τ)

theorem completeComplex_exact (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) (n : ℤ) :
    LinearMap.range ((M.completeComplex τ).d (n + 1) n).hom =
      LinearMap.ker ((M.completeComplex τ).d n (n - 1)).hom := by
  have aux (i j : ℤ) (hi : i = j + 1) :
      LinearMap.range ((M.completeComplex τ).d (i + 1) i).hom =
        LinearMap.ker ((M.completeComplex τ).d i j).hom := by
    subst i
    simp only [completeComplex, ChainComplex.of_d]
    exact M.adjacent_exact τ j
  exact aux n (n - 1) (by omega)

theorem completeComplex_exactProjective (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    ExactProjectiveComplex (M.completeComplex τ) where
  finite n := by
    cases n with
    | ofNat n => exact inferInstanceAs (Module.Finite R (M.positiveTerm n))
    | negSucc n => exact inferInstanceAs (Module.Finite R (M.negativeTerm τ n))
  projective n := by
    cases n with
    | ofNat n => exact inferInstanceAs (Module.Projective R (M.positiveTerm n))
    | negSucc n => exact inferInstanceAs (Module.Projective R (M.negativeTerm τ n))
  exactAt := M.completeComplex_exact τ

theorem completeComplex_totallyAcyclic (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    TotallyAcyclicComplex (M.completeComplex τ) := by
  let := τ.regular_injective
  exact (M.completeComplex_exactProjective τ).totallyAcyclic

noncomputable def completeCokernelEquiv (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CompleteComparison.Cokernel (M.completeComplex τ) 0 ≃ₗ[R] M.carrier := by
  change (M.positiveTerm 0 ⧸ LinearMap.range (M.positiveDifferential 0)) ≃ₗ[R] M.carrier
  exact (Submodule.quotEquivOfEq _ _ (M.positiveDifferential_range 0)).trans
    (M.cover.map.quotKerEquivOfSurjective M.cover.surjective)

end FiniteLeftModule

theorem exists_finite_complete_resolution [Module.Finite k R]
    (τ : FrobeniusTrace k R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [Module.Finite k M] :
    ∃ P : ChainComplex (ModuleCat.{u} R) ℤ,
      TotallyAcyclicComplex P ∧ Nonempty (M ≃ₗ[R] CompleteComparison.Cokernel P 0) := by
  let X : FiniteLeftModule k R := { carrier := ModuleCat.of R M }
  exact ⟨X.completeComplex τ, X.completeComplex_totallyAcyclic τ,
    ⟨(X.completeCokernelEquiv τ).symm⟩⟩

end ArExplicit

end OAI
