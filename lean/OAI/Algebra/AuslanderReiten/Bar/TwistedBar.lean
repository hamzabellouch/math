import OAI.Algebra.AuslanderReiten.Bar.BarCasimir
import OAI.Algebra.AuslanderReiten.Modules.TwistedBimodule

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def twistEnveloping (h : R ≃ₐ[k] R) : Enveloping k R ≃ₐ[k] Enveloping k R :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[k] R) (AlgEquiv.op h)

@[instance_reducible] def twistedModule (h : R ≃ₐ[k] R) (n : ℕ) :
    Module (Enveloping k R) (object k R n) :=
  Module.compHom (object k R n) ((representation k R n).comp (twistEnveloping k R h).toAlgHom).toRingHom

def twistedObject (h : R ≃ₐ[k] R) (n : ℕ) : ModuleCat.{u} (Enveloping k R) :=
  letI := twistedModule k R h n
  ModuleCat.of (Enveloping k R) (object k R n)

instance twistedBaseModule (h : R ≃ₐ[k] R) (n : ℕ) : Module k (twistedObject k R h n) :=
  (object k R n).isModule

instance twistedModuleTower (h : R ≃ₐ[k] R) (n : ℕ) :
    IsScalarTower k (Enveloping k R) (twistedObject k R h n) :=
  IsScalarTower.of_algebraMap_smul (A := Enveloping k R) fun a x => by
    change ((representation k R n).comp (twistEnveloping k R h).toAlgHom)
      (algebraMap k (Enveloping k R) a) x = a • x
    rw [AlgHom.commutes]
    rfl

instance twistInvPair (h : R ≃ₐ[k] R) :
    RingHomInvPair (twistEnveloping k R h).toRingHom (twistEnveloping k R h).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (twistEnveloping k R h).toRingEquiv

instance twistInvPairSymm (h : R ≃ₐ[k] R) :
    RingHomInvPair (twistEnveloping k R h).symm.toRingHom (twistEnveloping k R h).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (twistEnveloping k R h).toRingEquiv

def twistedEquiv (h : R ≃ₐ[k] R) (n : ℕ) :
    twistedObject k R h n ≃ₛₗ[(twistEnveloping k R h).toRingHom] moduleObject k R n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem twistedFree (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Free (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let := free k R n
  exact Module.Free.of_equiv (twistedEquiv k R h (n + 1)).symm

theorem twistedProjective (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Projective (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let := twistedFree k R h n
  exact Module.Projective.of_free

theorem twistedFinite [Module.Finite k R] (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Finite (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let : Module.Finite k (twistedObject k R h (n + 1)) := finiteBase k R (n + 1)
  exact Module.Finite.of_restrictScalars_finite k (Enveloping k R) _

def twistedToOrdinary (h : R ≃ₐ[k] R) {n m : ℕ}
    (f : object k R n →ₗ[k] object k R m)
    (hl : ∀ a x, f (left k R n a x) = left k R m a (f x))
    (hr : ∀ a x, f (right k R n (MulOpposite.op (h a)) x) =
      right k R m (MulOpposite.op a) (f x)) :
    twistedObject k R h n →ₗ[Enveloping k R] moduleObject k R m where
  toAddHom := f.toAddHom
  map_smul' a x := by
    let y : object k R n := x
    change f (representation k R n (twistEnveloping k R h a) y) = representation k R m a (f y)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change f (left k R n a (right k R n (MulOpposite.op (h b.unop)) y)) =
        left k R m a (right k R m b (f y))
      rw [hl, hr, MulOpposite.op_unop]

def casimirInsertionMap (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ) (n : ℕ) :
    twistedObject k R h n →ₗ[Enveloping k R] moduleObject k R (n + 1) :=
  twistedToOrdinary k R h (casimirInsertion k R ξ n)
    (casimirInsertion_left k R ξ n) (fun a x => casimirInsertion_right k R ξ h hξ n a x)

def twistedDifferential (h : R ≃ₐ[k] R) (n : ℕ) :
    twistedObject k R h (n + 1) →ₗ[Enveloping k R] twistedObject k R h n where
  toAddHom := (boundary k R n).toAddHom
  map_smul' a x := (differential k R n).map_smul (twistEnveloping k R h a) x

variable [CharP k 2]

def twistedComplex (h : R ≃ₐ[k] R) : ChainComplex (ModuleCat.{u} (Enveloping k R)) ℕ :=
  ChainComplex.of (fun n => twistedObject k R h (n + 1))
    (fun n => ModuleCat.ofHom (X := twistedObject k R h (n + 2))
      (Y := twistedObject k R h (n + 1)) (twistedDifferential k R h (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R (n + 1))

@[simp] theorem twistedComplex_d (h : R ≃ₐ[k] R) (n : ℕ) :
    (twistedComplex k R h).d (n + 1) n = ModuleCat.ofHom
      (X := twistedObject k R h (n + 2)) (Y := twistedObject k R h (n + 1))
        (twistedDifferential k R h (n + 1)) := by
  simp only [twistedComplex, ChainComplex.of.d]
  apply Category.id_comp

theorem twistedDifferential_exact (h : R ≃ₐ[k] R) (n : ℕ) :
    LinearMap.range (twistedDifferential k R h (n + 1)) =
      LinearMap.ker (twistedDifferential k R h n) := by
  ext x
  change (∃ y, boundary k R (n + 1) y = x) ↔ boundary k R n x = 0
  exact SetLike.ext_iff.mp (boundary_exact k R n) x

def twistedAugmentation (h : R ≃ₐ[k] R) : twistedComplex k R h ⟶
    (ChainComplex.single₀ (ModuleCat.{u} (Enveloping k R))).obj (twistedObject k R h 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := twistedObject k R h 1) (Y := twistedObject k R h 0)
      (twistedDifferential k R h 0), by
      rw [twistedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R 0⟩

@[simp] theorem twistedAugmentation_zero (h : R ≃ₐ[k] R) :
    (twistedAugmentation k R h).f 0 = ModuleCat.ofHom (X := twistedObject k R h 1)
      (Y := twistedObject k R h 0) (twistedDifferential k R h 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem twistedComplex_exactAt (h : R ≃ₐ[k] R) (n : ℕ) :
    (twistedComplex k R h).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((twistedComplex k R h).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((twistedComplex k R h).d (n + 1) n).hom
  rw [twistedComplex_d, twistedComplex_d]
  exact twistedDifferential_exact k R h (n + 1)

def twistedResolution (h : R ≃ₐ[k] R) : ProjectiveResolution (twistedObject k R h 0) where
  complex := twistedComplex k R h
  projective n := by
    let := twistedProjective k R h n
    exact (twistedObject k R h (n + 1)).projective_of_categoryTheory_projective
  π := twistedAugmentation k R h
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((twistedComplex k R h).d 1 0).hom =
            LinearMap.ker ((twistedAugmentation k R h).f 0).hom
          rw [twistedComplex_d, twistedAugmentation_zero]
          exact twistedDifferential_exact k R h 0
        · rw [ModuleCat.epi_iff_surjective]
          intro x
          exact ⟨contraction k R 0 x, augmentation_contraction k R x⟩
      · exact (twistedComplex k R h).shape 0 0 (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact twistedComplex_exactAt k R h n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

theorem casimirInsertionMap_boundary (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (hz : boundary k R 0 ξ = 0) (n : ℕ) :
    (differential k R (n + 1)).comp (casimirInsertionMap k R h ξ hξ (n + 1)) +
      (casimirInsertionMap k R h ξ hξ n).comp (twistedDifferential k R h n) = 0 := by
  apply LinearMap.ext
  exact casimirInsertion_boundary k R ξ hz n

omit [CharP k 2] in

theorem casimirInsertionMap_boundary_zero (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (hz : boundary k R 0 ξ = 0) :
    (differential k R 1).comp (casimirInsertionMap k R h ξ hξ 1) =
      (casimirInsertionMap k R h ξ hξ 0).comp (twistedDifferential k R h 0) := by
  apply LinearMap.ext
  exact casimirInsertion_boundary_zero k R ξ hz

end ArExplicit.AbsoluteBar

end

end OAI
