import Mathlib
import OAI.GroupTheory.FiniteLattice.PerfectPreimage

namespace OAI

/-! Perfect covers, normal-subgroup fences and least perfect preimages. -/

namespace FiniteLatticeGap

section FiniteSimpleModule
variable {k A V : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k A]

include A

theorem simple_module_finite : FiniteDimensional k V := by
  have := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact Module.Finite.of_surjective
    ((LinearMap.toSpanSingleton A V v).restrictScalars k)
    (IsSimpleModule.toSpanSingleton_surjective A hv)
end FiniteSimpleModule

section SimpleFamily
variable {k A I : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Fintype I]
  (V : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
  [∀ i, IsSimpleModule A (V i)]
  (hdistinct : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))

include hdistinct

theorem simple_family_commutant_scalar (e : Module.End A (∀ i, V i)) :
    ∃ c : I → k, ∀ x i, e x i = c i • x i := by
  classical
  let : ∀ i, FiniteDimensional k (V i) := fun i => simple_module_finite (A := A)
  let block (i j : I) : V j →ₗ[A] V i :=
    (LinearMap.proj i).comp (e.comp (LinearMap.single A V j))
  have hoff (i j : I) (hij : i ≠ j) : block i j = 0 := by
    rcases (block i j).bijective_or_eq_zero with h | h
    · have := hdistinct j i (Ne.symm hij)
      exact isEmptyElim (LinearEquiv.ofBijective (block i j) h)
    · exact h
  have hdiag (i : I) : ∃ c : k, algebraMap k (Module.End A (V i)) c = block i i :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := A) (V := V i) k).2 (block i i)
  choose c hc using hdiag
  refine ⟨c, ?_⟩
  intro x i
  have hsum : e x = ∑ j, e (Pi.single j (x j)) := by
    rw [← map_sum, LinearMap.sum_single_apply]
  rw [hsum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact (congrArg (fun f : Module.End A (V i) => f (x i)) (hc i)).symm
  · intro j _ hji
    exact congrArg (fun f : V j →ₗ[A] V i => f (x j)) (hoff i j (Ne.symm hji))
  · simp

theorem simple_family_action_surjective :
    Function.Surjective
      (AlgHom.pi (fun i => Algebra.lsmul k (A := A) k (V i))) := by
  classical
  let : ∀ i, FiniteDimensional k (V i) := fun i => simple_module_finite (A := A)
  let W := ∀ i, V i
  let : Module.Finite (Module.End A W) W :=
    Module.Finite.of_restrictScalars_finite k (Module.End A W) W
  intro f
  let f' : Module.End (Module.End A W) W :=
    { toFun := fun x i => f i (x i)
      map_add' := by intro x y; ext i; exact (f i).map_add (x i) (y i)
      map_smul' := by
        intro e x
        obtain ⟨c, hc⟩ := simple_family_commutant_scalar (k := k) V hdistinct e
        ext i
        change f i (e x i) = e (fun j => f j (x j)) i
        rw [hc, hc, map_smul] }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) f'
  refine ⟨a, ?_⟩
  ext i v
  have hh := congrArg (fun z : Module.End (Module.End A W) W => z (Pi.single i v) i) ha
  simpa [f', Module.toModuleEnd_apply, W] using hh

theorem simple_family_degree_sum_le :
    ∑ i, (Module.finrank k (V i)) ^ 2 ≤ Module.finrank k A := by
  classical
  let : ∀ i, FiniteDimensional k (V i) := fun i => simple_module_finite (A := A)
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (AlgHom.pi (fun i => Algebra.lsmul k (A := A) k (V i))).toLinearMap)
    (simple_family_action_surjective (k := k) V hdistinct)
  simpa only [Module.finrank_pi_fintype, Module.finrank_linearMap, pow_two] using h

theorem simple_family_card_le : Fintype.card I ≤ Module.finrank k A := by
  classical
  let : ∀ i, FiniteDimensional k (V i) := fun i => simple_module_finite (A := A)
  have hone (i : I) : 1 ≤ (Module.finrank k (V i)) ^ 2 := by
    have := IsSimpleModule.nontrivial A (V i)
    have hp : 0 < Module.finrank k (V i) := Module.finrank_pos_iff.mpr inferInstance
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.ne_of_gt hp))
  calc
    Fintype.card I = ∑ _i : I, 1 := by simp
    _ ≤ ∑ i, (Module.finrank k (V i)) ^ 2 := Finset.sum_le_sum fun i _ => hone i
    _ ≤ Module.finrank k A := simple_family_degree_sum_le (k := k) V hdistinct

end SimpleFamily

theorem simple_family_card_le_order
    {k G I : Type*} [Field k] [IsAlgClosed k] [Group G] [Finite G] [Fintype I]
    (V : I → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module (MonoidAlgebra k G) (V i)]
    [∀ i, IsScalarTower k (MonoidAlgebra k G) (V i)]
    [∀ i, IsSimpleModule (MonoidAlgebra k G) (V i)]
    (hdistinct : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[MonoidAlgebra k G] V j)) :
    Fintype.card I ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  have h := simple_family_card_le (k := k) (A := MonoidAlgebra k G) V hdistinct
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G k)] at h
  simpa only [Nat.card_eq_fintype_card] using h



section Density
variable {k A V : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V]

theorem simple_action_surjective :
    Function.Surjective (Algebra.lsmul k (A := A) k V) := by
  let : Module.Finite (Module.End A V) V :=
    Module.Finite.of_restrictScalars_finite k (Module.End A V) V
  intro f
  let f' : Module.End (Module.End A V) V :=
    { f with
      map_smul' := by
        intro a v
        obtain ⟨c, rfl⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
          (A := A) (V := V) k).2 a
        simp }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) f'
  refine ⟨a, ?_⟩
  ext v
  exact congrArg (fun t : Module.End (Module.End A V) V => t v) ha

end Density

theorem irreducible_degree_sq_le_order
    {k G V : Type*} [Field k] [IsAlgClosed k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [Representation.IsIrreducible ρ] :
    (Module.finrank k V) ^ 2 ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (Algebra.lsmul k (A := MonoidAlgebra k G) k ρ.asModule).toLinearMap)
    (simple_action_surjective (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule))
  rw [Module.finrank_linearMap, ρ.asModuleEquiv.finrank_eq,
    Module.finrank_eq_card_basis (MonoidAlgebra.basis G k)] at h
  simpa [pow_two, Nat.card_eq_fintype_card] using h


open Module

section GaloisDescent
variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [AddCommGroup V] [Module L V]
  (ρ : Gal(L/K) → V →+ V)
  (h_one : ∀ v, ρ 1 v = v)
  (h_mul : ∀ g h v, ρ (g * h) v = ρ g (ρ h v))
  (h_smul : ∀ g a v, ρ g (a • v) = g a • ρ g v)

include h_one h_mul h_smul

theorem semilinear_fixed_span :
    Submodule.span L {v : V | ∀ g, ρ g v = v} = ⊤ := by
  classical
  let S : Set V := {v | ∀ g, ρ g v = v}
  let tr (v : V) := ∑ g : Gal(L/K), ρ g v
  have htr (v : V) : tr v ∈ S := by
    intro g
    simp only [tr, map_sum, ← h_mul]
    exact Fintype.sum_bijective (fun h : Gal(L/K) => g * h)
      (Group.mulLeft_bijective g) _ _ (fun _ => rfl)
  have hind : LinearIndependent L (fun g : Gal(L/K) => (g : L → L)) :=
    (linearIndependent_monoidHom L L).comp (fun g : Gal(L/K) => g.toMonoidHom)
      (fun g h he => AlgEquiv.ext fun a => DFunLike.congr_fun he a)
  by_contra hp
  obtain ⟨φ, hφ, hpφ⟩ := (Submodule.span L S).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hp)
  apply hφ
  ext v
  have ht (a : L) : ∑ g : Gal(L/K), g a * φ (ρ g v) = 0 := by
    have hh := hpφ (Submodule.subset_span (htr (a • v)))
    simpa only [LinearMap.mem_ker, tr, map_sum, h_smul, map_smul, smul_eq_mul] using hh
  have hsum : ∑ g : Gal(L/K), φ (ρ g v) • (g : L → L) = 0 := by
    ext a
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
      Pi.zero_apply] using ht a
  have hz := Fintype.linearIndependent_iff.mp hind (fun g => φ (ρ g v)) hsum
  simpa only [h_one, LinearMap.zero_apply] using hz 1

theorem semilinear_fixed_basis {ι : Type*} (b : Basis ι L V) :
    ∃ b' : Basis ι L V, ∀ i g, ρ g (b' i) = b' i := by
  classical
  let S : Set V := {v | ∀ g, ρ g v = v}
  have hS : ⊤ ≤ Submodule.span L S :=
    (semilinear_fixed_span ρ h_one h_mul h_smul).ge
  let b₀ := Basis.ofSpan hS
  let e := b₀.indexEquiv b
  refine ⟨b₀.reindex e, ?_⟩
  intro i g
  rw [Basis.reindex_apply]
  exact Basis.ofSpan_subset hS ⟨e.symm i, rfl⟩ g

end GaloisDescent

theorem matrix_hilbert90
    {K L n : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Fintype n] [DecidableEq n]
    (c : Gal(L/K) → Matrix n n L)
    (hc_one : c 1 = 1)
    (hc_mul : ∀ g h, c (g * h) = c g * (c h).map g) :
    ∃ B : Matrix n n L, IsUnit B ∧ ∀ g, c g * B.map g = B := by
  classical
  let ρ : Gal(L/K) → (n → L) →+ (n → L) := fun g =>
    { toFun := fun v => (c g).mulVec (fun i => g (v i))
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro v w
        simp only [Pi.add_apply, map_add]
        exact Matrix.mulVec_add _ _ _ }
  have h_one (v : n → L) : ρ 1 v = v := by
    simp [ρ, hc_one]
  have h_mul (g h : Gal(L/K)) (v : n → L) : ρ (g * h) v = ρ g (ρ h v) := by
    change (c (g * h)).mulVec (fun i => (g * h) (v i)) =
      (c g).mulVec (fun i => g ((c h).mulVec (fun j => h (v j)) i))
    rw [hc_mul, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    exact (g.toRingHom.map_mulVec (c h) (fun j => h (v j)) i).symm
  have h_smul (g : Gal(L/K)) (a : L) (v : n → L) :
      ρ g (a • v) = g a • ρ g v := by
    change (c g).mulVec (fun i => g (a • v i)) = _
    simp only [smul_eq_mul, map_mul]
    change (c g).mulVec (g a • (fun i => g (v i))) =
      g a • (c g).mulVec (fun i => g (v i))
    exact Matrix.mulVec_smul (c g) (g a) (fun i => g (v i))
  obtain ⟨b, hb⟩ := semilinear_fixed_basis ρ h_one h_mul h_smul (Pi.basisFun L n)
  let B : Matrix n n L := (Pi.basisFun L n).toMatrix b
  refine ⟨B, ?_, ?_⟩
  · refine ⟨⟨B, b.toMatrix (Pi.basisFun L n), ?_, ?_⟩, rfl⟩
    · simp [B, Basis.toMatrix_mul_toMatrix]
    · simp [B, Basis.toMatrix_mul_toMatrix]
  · intro g
    ext i j
    have hh := congrFun (hb j g) i
    simpa [ρ, B, Basis.toMatrix_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct] using hh

end FiniteLatticeGap

namespace FiniteLatticeGap

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section SemilinearTransport
variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (τ : Representation k G W)
  (φ : k ≃+* k) (e : V ≃ₛₗ[(φ : k →+* k)] W)
  (he : ∀ g v, e (ρ g v) = τ g (e v))

noncomputable def semilinearSubrepresentationEquiv :
    Subrepresentation τ ≃o Subrepresentation ρ where
  toFun s :=
    { toSubmodule := s.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change e (ρ g v) ∈ s.toSubmodule
        rw [he]
        exact s.apply_mem_toSubmodule g hv }
  invFun s :=
    { toSubmodule := s.toSubmodule.comap e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro g w hw
        change e.symm (τ g w) ∈ s.toSubmodule
        have hh : e.symm (τ g w) = ρ g (e.symm w) := by
          apply e.injective
          simp only [e.apply_symm_apply, he]
        rw [hh]
        exact s.apply_mem_toSubmodule g hw }
  left_inv s := by
    ext w
    change e (e.symm w) ∈ s.toSubmodule ↔ w ∈ s.toSubmodule
    rw [e.apply_symm_apply]
  right_inv s := by
    ext v
    change e.symm (e v) ∈ s.toSubmodule ↔ v ∈ s.toSubmodule
    rw [e.symm_apply_apply]
  map_rel_iff' := by
    intro s t
    constructor
    · intro h w hw
      change w ∈ s.toSubmodule at hw
      have hh := h (show e.symm w ∈ s.toSubmodule.comap e.toLinearMap by
        simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, e.apply_symm_apply] using hw)
      change e (e.symm w) ∈ t.toSubmodule at hh
      change w ∈ t.toSubmodule
      simpa only [e.apply_symm_apply] using hh
    · intro h v hv
      exact h hv

include he in

theorem semilinear_isIrreducible [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible τ :=
  (semilinearSubrepresentationEquiv ρ τ φ e he).isSimpleOrder_iff.mpr inferInstance

end SemilinearTransport

variable {k G n : Type*} [Field k] [Group G] [Fintype n] [DecidableEq n]

def matrixRepresentation (ρ : G →* Matrix n n k) : Representation k G (n → k) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ

def matrixTwist (ρ : G →* Matrix n n k) (φ : k ≃+* k) : G →* Matrix n n k :=
  φ.mapMatrix.toMonoidHom.comp ρ

def fieldColumnEquiv (φ : k ≃+* k) : (n → k) ≃ₛₗ[(φ : k →+* k)] (n → k) where
  toFun v i := φ (v i)
  invFun v i := φ.symm (v i)
  left_inv v := by ext i; exact φ.symm_apply_apply (v i)
  right_inv v := by ext i; exact φ.apply_symm_apply (v i)
  map_add' v w := by ext i; exact φ.map_add (v i) (w i)
  map_smul' a v := by ext i; exact φ.map_mul a (v i)

instance matrixTwist_irreducible (ρ : G →* Matrix n n k) (φ : k ≃+* k)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    Representation.IsIrreducible (matrixRepresentation (matrixTwist ρ φ)) := by
  apply semilinear_isIrreducible (matrixRepresentation ρ)
    (matrixRepresentation (matrixTwist ρ φ)) φ (fieldColumnEquiv φ)
  intro g v
  ext i
  exact φ.toRingHom.map_mulVec (ρ g) v i

theorem matrix_equiv_of_module_equiv (ρ τ : G →* Matrix n n k)
    (e : (matrixRepresentation ρ).asModule ≃ₗ[MonoidAlgebra k G]
      (matrixRepresentation τ).asModule) :
    ∃ C : Matrix n n k, IsUnit C ∧ ∀ g, C * ρ g = τ g * C := by
  let f := (Representation.IntertwiningMap.equivLinearMapAsModule
    (matrixRepresentation ρ) (matrixRepresentation τ)).symm e.toLinearMap
  have hf : Function.Bijective f := e.bijective
  let C := LinearMap.toMatrixAlgEquiv' f.toLinearMap
  refine ⟨C, ?_, ?_⟩
  · exact ((Module.End.isUnit_iff f.toLinearMap).mpr hf).map
      LinearMap.toMatrixAlgEquiv'
  · intro g
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul, C, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    change f.toLinearMap ∘ₗ (matrixRepresentation ρ) g =
      (matrixRepresentation τ) g ∘ₗ f.toLinearMap
    exact f.isIntertwining' g

theorem matrix_twist_period [IsAlgClosed k] [Finite G]
    (ρ : G →* Matrix n n k) (φ : k ≃+* k)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    ∃ i j : Fin (Nat.card G + 1), i < j ∧
      ∃ C : Matrix n n k, IsUnit C ∧
        ∀ g, C * (matrixTwist ρ (φ ^ (j : ℕ))) g =
          (matrixTwist ρ (φ ^ (i : ℕ))) g * C := by
  classical
  let τ (i : Fin (Nat.card G + 1)) :=
    matrixRepresentation (matrixTwist ρ (φ ^ (i : ℕ)))
  have hex : ∃ i j, i ≠ j ∧ Nonempty ((τ i).asModule ≃ₗ[MonoidAlgebra k G]
      (τ j).asModule) := by
    by_contra h
    have hb := simple_family_card_le_order (fun i => (τ i).asModule)
      (fun i j hij => ⟨fun e => h ⟨i, j, hij, ⟨e⟩⟩⟩)
    simp only [Fintype.card_fin] at hb
    omega
  obtain ⟨i, j, hij, ⟨e⟩⟩ := hex
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact ⟨i, j, hij, matrix_equiv_of_module_equiv _ _ e.symm⟩
  · exact ⟨j, i, hij, matrix_equiv_of_module_equiv _ _ e⟩

@[simp] theorem mapMatrix_comp (φ ψ : k ≃+* k) (A : Matrix n n k) :
    φ.mapMatrix (ψ.mapMatrix A) = (φ * ψ).mapMatrix A := rfl

@[simp] theorem mapMatrix_id (A : Matrix n n k) :
    (1 : k ≃+* k).mapMatrix A = A := rfl

theorem matrix_twist_period_bound [IsAlgClosed k] [Finite G]
    (ρ : G →* Matrix n n k) (φ : k ≃+* k)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    ∃ a : ℕ, 0 < a ∧ a ≤ Nat.card G ∧
      ∃ A : Matrix n n k, IsUnit A ∧
        ∀ g, ρ g * A = A * (φ ^ a).mapMatrix (ρ g) := by
  obtain ⟨i, j, hij, C, hC, hcomm⟩ := matrix_twist_period ρ φ
  let a : ℕ := (j : ℕ) - (i : ℕ)
  have hle : (i : ℕ) ≤ (j : ℕ) := Nat.le_of_lt hij
  have hpow : (φ ^ (i : ℕ))⁻¹ * φ ^ (j : ℕ) = φ ^ a := by
    rw [← Nat.add_sub_cancel' hle, pow_add, inv_mul_cancel_left]
  refine ⟨a, Nat.sub_pos_of_lt hij, ?_,
    (φ ^ (i : ℕ)).symm.mapMatrix C, hC.map _, ?_⟩
  · have := j.isLt
    dsimp [a]
    omega
  · intro g
    have hh := congrArg (φ ^ (i : ℕ)).symm.mapMatrix (hcomm g)
    change (φ ^ (i : ℕ)).symm.mapMatrix
      (C * (φ ^ (j : ℕ)).mapMatrix (ρ g)) =
      (φ ^ (i : ℕ)).symm.mapMatrix ((φ ^ (i : ℕ)).mapMatrix (ρ g) * C) at hh
    rw [map_mul, map_mul, mapMatrix_comp, mapMatrix_comp] at hh
    change _ * (((φ ^ (i : ℕ))⁻¹ * φ ^ (j : ℕ)).mapMatrix (ρ g)) =
      (((φ ^ (i : ℕ))⁻¹ * φ ^ (i : ℕ)).mapMatrix (ρ g)) * _ at hh
    rw [hpow, inv_mul_cancel, mapMatrix_id] at hh
    exact hh.symm

end FiniteLatticeGap

namespace FiniteLatticeGap
open Module

section FiniteFrobenius
variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L]
  [Algebra.IsAlgebraic E L] {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def matrixFrobEquiv (A : Matrix n n L) (hA : IsUnit A) :
    (n → L) ≃ₗ[E] (n → L) :=
  (LinearEquiv.piCongrRight fun _ : n =>
    (FiniteField.frobeniusAlgEquivOfAlgebraic E L).toLinearEquiv).trans
    ((LinearEquiv.ofBijective (Matrix.toLinAlgEquiv' A)
      ((Module.End.isUnit_iff _).mp (hA.map Matrix.toLinAlgEquiv'))).restrictScalars E)

@[simp] theorem matrixFrobEquiv_apply (A : Matrix n n L) (hA : IsUnit A) (v : n → L) :
    matrixFrobEquiv E L A hA v = A.mulVec (fun i => (v i) ^ Fintype.card E) := rfl

theorem matrixFrobEquiv_smul (A : Matrix n n L) (hA : IsUnit A) (a : L) (v : n → L) :
    matrixFrobEquiv E L A hA (a • v) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic E L) a • matrixFrobEquiv E L A hA v := by
  simp only [matrixFrobEquiv_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  exact Matrix.mulVec_smul A (a ^ Fintype.card E) (fun i => v i ^ Fintype.card E)

theorem matrixFrobEquiv_pow_smul (A : Matrix n n L) (hA : IsUnit A) (t : ℕ)
    (a : L) (v : n → L) :
    (matrixFrobEquiv E L A hA ^ t) (a • v) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic E L ^ t) a •
        (matrixFrobEquiv E L A hA ^ t) v := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [pow_succ', LinearEquiv.mul_apply, AlgEquiv.mul_apply, ih,
      matrixFrobEquiv_smul]

variable (J : Type*) [Field J] [Algebra E J] [Algebra L J]
  [Algebra.IsAlgebraic E J]

theorem matrixFrobEquiv_map (A : Matrix n n L) (hA : IsUnit A) (v : n → L) :
    matrixFrobEquiv E J ((algebraMap L J).mapMatrix A) (hA.map _) (fun i => algebraMap L J (v i)) =
      fun i => algebraMap L J (matrixFrobEquiv E L A hA v i) := by
  simp only [matrixFrobEquiv_apply, ← map_pow]
  ext i
  exact ((algebraMap L J).map_mulVec A (fun j => v j ^ Fintype.card E) i).symm

theorem matrixFrobEquiv_pow_map (A : Matrix n n L) (hA : IsUnit A) (t : ℕ) (v : n → L) :
    (matrixFrobEquiv E J ((algebraMap L J).mapMatrix A) (hA.map _) ^ t)
        (fun i => algebraMap L J (v i)) =
      fun i => algebraMap L J ((matrixFrobEquiv E L A hA ^ t) v i) := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [pow_succ', LinearEquiv.mul_apply, ih]
    exact matrixFrobEquiv_map E L J A hA ((matrixFrobEquiv E L A hA ^ t) v)

variable [Finite J]

theorem matrixFrobEquiv_pow_finrank (A : Matrix n n L) (hA : IsUnit A)
    (hdiv : orderOf (matrixFrobEquiv E L A hA) ∣ finrank E J) :
    matrixFrobEquiv E J ((algebraMap L J).mapMatrix A) (hA.map _) ^ finrank E J = 1 := by
  classical
  let S := matrixFrobEquiv E J ((algebraMap L J).mapMatrix A) (hA.map _)
  let d := finrank E J
  have hσ : FiniteField.frobeniusAlgEquivOfAlgebraic E J ^ d = 1 := by
    dsimp [d]
    rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic E J]
    exact pow_orderOf_eq_one _
  let T : (n → J) →ₗ[J] (n → J) :=
    { (S ^ d).toLinearMap.toAddHom with
      map_smul' := by
        intro a v
        change (S ^ d) (a • v) = a • (S ^ d) v
        rw [matrixFrobEquiv_pow_smul, hσ, AlgEquiv.one_apply] }
  have hTL : matrixFrobEquiv E L A hA ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have hT : T = LinearMap.id := by
    apply (Pi.basisFun J n).ext
    intro j
    have hh := matrixFrobEquiv_pow_map E L J A hA d ((Pi.basisFun L n) j)
    simp only [hTL, LinearEquiv.coe_one, id_eq] at hh
    have hsingle : (fun i => algebraMap L J ((Pi.basisFun L n) j i)) =
        (Pi.basisFun J n) j := by
      ext i
      by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
    rw [hsingle] at hh
    exact hh
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : (n → J) →ₗ[J] (n → J) => f v) hT

end FiniteFrobenius

variable (E J : Type*) [Field E] [Fintype E] [Field J] [Algebra E J]
  [Finite J] {n : Type*} [Fintype n] [DecidableEq n]

theorem frobenius_matrix_descent (A : Matrix n n J) (hA : IsUnit A)
    (horder : orderOf (matrixFrobEquiv E J A hA) ∣ finrank E J) :
    ∃ B : Matrix n n J, IsUnit B ∧ A * B.map (fun x => x ^ Fintype.card E) = B := by
  classical
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic E J
  let S := matrixFrobEquiv E J A hA
  have hgen : ∀ g : Gal(J/E), g ∈ Subgroup.zpowers σ := by
    intro g
    obtain ⟨r, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow E J).2 g
    exact (Subgroup.zpowers σ).pow_mem (Subgroup.mem_zpowers σ) _
  have hdiv : orderOf S ∣ orderOf σ := by
    dsimp [S, σ]
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact horder
  let γ := monoidHomOfForallMemZpowers hgen hdiv
  have hγ : γ σ = S := monoidHomOfForallMemZpowers_apply_gen hgen hdiv
  let ρ : Gal(J/E) → (n → J) →+ (n → J) := fun g => (γ g).toLinearMap.toAddMonoidHom
  have hone (v : n → J) : ρ 1 v = v := by
    change γ 1 v = v
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  have hmul (g h : Gal(J/E)) (v : n → J) : ρ (g * h) v = ρ g (ρ h v) := by
    change γ (g * h) v = γ g (γ h v)
    rw [map_mul, LinearEquiv.mul_apply]
  have hsmul (g : Gal(J/E)) (a : J) (v : n → J) : ρ g (a • v) = g a • ρ g v := by
    obtain ⟨r, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow E J).2 g
    change γ (σ ^ (r : ℕ)) (a • v) = (σ ^ (r : ℕ)) a • γ (σ ^ (r : ℕ)) v
    rw [map_pow, hγ]
    exact matrixFrobEquiv_pow_smul E J A hA r a v
  obtain ⟨b, hb⟩ := semilinear_fixed_basis ρ hone hmul hsmul (Pi.basisFun J n)
  let B : Matrix n n J := (Pi.basisFun J n).toMatrix b
  refine ⟨B, ?_, ?_⟩
  · refine ⟨⟨B, b.toMatrix (Pi.basisFun J n), ?_, ?_⟩, rfl⟩
    · simp [B, Basis.toMatrix_mul_toMatrix]
    · simp [B, Basis.toMatrix_mul_toMatrix]
  · ext i j
    have hh := hb j σ
    change γ σ (b j) = b j at hh
    rw [hγ] at hh
    have hi := congrFun hh i
    simpa [S, B, Basis.toMatrix_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi


end FiniteLatticeGap

namespace FiniteLatticeGap
open Module

theorem frobenius_lang
    (p : ℕ) [Fact p.Prime]
    {E k n : Type*} [Field E] [Fintype E] [CharP E p]
    [Field k] [IsAlgClosed k] [Algebra E k] [Algebra.IsAlgebraic E k]
    [Fintype n] [DecidableEq n]
    (A : Matrix n n k) (hA : IsUnit A) :
    ∃ B : Matrix n n k, IsUnit B ∧ A * B.map (fun x => x ^ Fintype.card E) = B := by
  classical
  let X : Set k := Set.range (fun ij : n × n => A ij.1 ij.2)
  let F : IntermediateField E k := IntermediateField.adjoin E X
  let : Finite X := (Set.finite_range (fun ij : n × n => A ij.1 ij.2)).to_subtype
  let : FiniteDimensional E F := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let : Finite F := Module.finite_of_finite E
  let : CharP F p := (Algebra.charP_iff E F p).mp inferInstance
  let A₀ : Matrix n n F := fun i j =>
    ⟨A i j, IntermediateField.subset_adjoin E X ⟨(i, j), rfl⟩⟩
  have hA₀map : (algebraMap F k).mapMatrix A₀ = A := rfl
  have hA₀ : IsUnit A₀ := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hz
    have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
    apply hdet
    rw [← hA₀map]
    rw [← RingHom.map_det, hz, map_zero]
  let : Finite ((n → F) ≃ₗ[E] (n → F)) :=
    Finite.of_injective (fun e : (n → F) ≃ₗ[E] (n → F) => (e : (n → F) → (n → F)))
      DFunLike.coe_injective
  let O := orderOf (matrixFrobEquiv E F A₀ hA₀)
  let : NeZero O := ⟨Nat.ne_of_gt (orderOf_pos _)⟩
  let J := FiniteField.Extension F p O
  let : Algebra E J := ((algebraMap F J).comp (algebraMap E F)).toAlgebra
  let : IsScalarTower E F J := IsScalarTower.of_algebraMap_eq' rfl
  have hdiv : O ∣ finrank E J := by
    rw [← Module.finrank_mul_finrank E F J, FiniteField.finrank_extension]
    exact dvd_mul_left O (finrank E F)
  have hpow := matrixFrobEquiv_pow_finrank E F J A₀ hA₀ hdiv
  obtain ⟨B₀, hB₀, hB₀eq⟩ := frobenius_matrix_descent E J
    ((algebraMap F J).mapMatrix A₀) (hA₀.map _) (orderOf_dvd_of_pow_eq_one hpow)
  let f : J →ₐ[F] k := IsAlgClosed.lift
  let B := f.toRingHom.mapMatrix B₀
  refine ⟨B, hB₀.map _, ?_⟩
  have hAm : f.toRingHom.mapMatrix ((algebraMap F J).mapMatrix A₀) = A := by
    ext i j
    exact f.commutes (A₀ i j)
  have hBm : f.toRingHom.mapMatrix (B₀.map (fun x => x ^ Fintype.card E)) =
      B.map (fun x => x ^ Fintype.card E) := by
    ext i j
    exact f.map_pow (B₀ i j) (Fintype.card E)
  have hh := congrArg f.toRingHom.mapMatrix hB₀eq
  rw [map_mul, hAm, hBm] at hh
  exact hh

end FiniteLatticeGap

namespace FiniteLatticeGap

theorem prime_power_frobenius_lang
    (p a : ℕ) [Fact p.Prime] (ha : 0 < a)
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n (AlgebraicClosure (ZMod p))) (hA : IsUnit A) :
    ∃ B : Matrix n n (AlgebraicClosure (ZMod p)), IsUnit B ∧
      A * B.map (fun x => x ^ (p ^ a)) = B := by
  classical
  let E := GaloisField p a
  let k := AlgebraicClosure (ZMod p)
  let : Fintype E := Fintype.ofFinite E
  let f : E →ₐ[ZMod p] k := IsAlgClosed.lift
  let : Algebra E k := f.toAlgebra
  let : IsScalarTower (ZMod p) E k :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra.IsAlgebraic E k := Algebra.IsAlgebraic.tower_top (K := ZMod p) E
  have hcard : Fintype.card E = p ^ a := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p a (Nat.ne_of_gt ha)
  obtain ⟨B, hB, hBeq⟩ := frobenius_lang p (E := E) (k := k) A hA
  exact ⟨B, hB, hcard ▸ hBeq⟩

theorem finite_group_field_of_definition
    (p : ℕ) [Fact p.Prime] {G n : Type*} [Group G] [Finite G]
    [Fintype n] [DecidableEq n]
    (ρ : G →* Matrix n n (AlgebraicClosure (ZMod p)))
    [Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ)] :
    ∃ a : ℕ, 0 < a ∧ a ≤ Nat.card G ∧
      ∃ B : Matrix n n (AlgebraicClosure (ZMod p)), IsUnit B ∧
        ∀ g i j, ((B⁻¹ * ρ g * B) i j) ^ (p ^ a) = (B⁻¹ * ρ g * B) i j := by
  classical
  let k := AlgebraicClosure (ZMod p)
  let φ : k ≃+* k := frobeniusEquiv k p
  let : Representation.IsIrreducible (matrixRepresentation ρ) :=
    (inferInstance : Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ))
  obtain ⟨a, ha, habound, A, hA, hcomm⟩ := matrix_twist_period_bound ρ φ
  obtain ⟨B, hB, hLang⟩ := prime_power_frobenius_lang p a ha A hA
  have hφ (z : k) : (φ ^ a) z = z ^ (p ^ a) := by
    rw [RingAut.coe_pow]
    change ((fun x : k => x ^ p)^[a]) z = z ^ (p ^ a)
    rw [pow_iterate]
  have hLang' : A * (φ ^ a).mapMatrix B = B := by
    convert hLang using 2
    ext i j
    exact hφ (B i j)
  refine ⟨a, ha, habound, B, hB, ?_⟩
  intro g i j
  let C := B⁻¹ * ρ g * B
  have hBC : B * C = ρ g * B := by
    dsimp [C]
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB), one_mul]
  have htwist : (φ ^ a).mapMatrix B * (φ ^ a).mapMatrix C =
      (φ ^ a).mapMatrix (ρ g) * (φ ^ a).mapMatrix B := by
    calc
      _ = (φ ^ a).mapMatrix (B * C) := (map_mul _ B C).symm
      _ = (φ ^ a).mapMatrix (ρ g * B) := congrArg _ hBC
      _ = _ := map_mul _ (ρ g) B
  have heq : B * (φ ^ a).mapMatrix C = ρ g * B := by
    calc
      B * (φ ^ a).mapMatrix C = (A * (φ ^ a).mapMatrix B) *
          (φ ^ a).mapMatrix C := by rw [hLang']
      _ = A * ((φ ^ a).mapMatrix B * (φ ^ a).mapMatrix C) := mul_assoc _ _ _
      _ = A * ((φ ^ a).mapMatrix (ρ g) * (φ ^ a).mapMatrix B) := by rw [htwist]
      _ = (A * (φ ^ a).mapMatrix (ρ g)) * (φ ^ a).mapMatrix B := (mul_assoc _ _ _).symm
      _ = (ρ g * A) * (φ ^ a).mapMatrix B := by rw [hcomm]
      _ = ρ g * B := by rw [mul_assoc, hLang']
  have he := hB.mul_left_cancel (heq.trans hBC.symm)
  have hh := congrArg (fun M : Matrix n n k => M i j) he
  exact (hφ (C i j)).symm.trans hh



section SurjectiveRepresentations
variable {k G H V : Type*} [Field k] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module k V]

def subrepresentationSurjectiveEquiv (σ : Representation k H V)
    (f : G →* H) (hf : Function.Surjective f) :
    Subrepresentation (σ.comp f) ≃o Subrepresentation σ where
  toFun U := ⟨U.toSubmodule, by
    intro h v hv
    obtain ⟨g, rfl⟩ := hf h
    exact U.apply_mem_toSubmodule g hv⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
  left_inv U := by cases U; rfl
  right_inv U := by cases U; rfl
  map_rel_iff' := Iff.rfl

theorem irreducible_of_comp_surjective (σ : Representation k H V)
    (f : G →* H) (hf : Function.Surjective f)
    [Representation.IsIrreducible (σ.comp f)] : Representation.IsIrreducible σ :=
  (subrepresentationSurjectiveEquiv σ f hf).isSimpleOrder_iff.mp inferInstance

end SurjectiveRepresentations

section PerfectImage
variable {k n H : Type*} [Field k] [Fintype n] [DecidableEq n]
  [Group H]

theorem irreducible_central_scalar [IsAlgClosed k]
    (ρ : H →* Matrix n n k) [Representation.IsIrreducible (matrixRepresentation ρ)]
    (z : H) (hz : z ∈ Subgroup.center H) : ∃ c : k, ρ z = c • (1 : Matrix n n k) := by
  let σ := matrixRepresentation ρ
  let f : Representation.IntertwiningMap σ σ :=
    ⟨σ z, fun g => by
      change σ z * σ g = σ g * σ z
      rw [← map_mul, ← map_mul]
      exact congrArg σ ((Subgroup.mem_center_iff.mp hz g).symm)⟩
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := σ)).2 f
  refine ⟨c, Matrix.toLinAlgEquiv'.injective ?_⟩
  rw [map_smul, map_one]
  exact (congrArg Representation.IntertwiningMap.toLinearMap hc).symm

theorem perfect_det_one [Group.IsPerfect H] (ρ : H →* Matrix n n k) (g : H) :
    Matrix.det (ρ g) = 1 := by
  let f := Matrix.GeneralLinearGroup.det.comp ρ.toHomUnits
  let := Group.IsPerfect.range f
  have he : f.rangeRestrict g = 1 := Subsingleton.elim _ _
  exact congrArg (fun z : f.range => ((z : kˣ) : k)) he

theorem matrix_irreducible_dimension_pos
    (ρ : H →* Matrix n n k) [Representation.IsIrreducible (matrixRepresentation ρ)] :
    0 < Fintype.card n := by
  let := IsSimpleModule.nontrivial (MonoidAlgebra k H) (matrixRepresentation ρ).asModule
  have h := Module.finrank_pos (R := k) (M := (matrixRepresentation ρ).asModule)
  rwa [(matrixRepresentation ρ).asModuleEquiv.finrank_eq, Module.finrank_pi] at h

theorem perfect_irreducible_center_card [IsAlgClosed k] [Group.IsPerfect H]
    (ρ : H →* Matrix n n k) (hρ : Function.Injective ρ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    Nat.card (Subgroup.center H) ≤ Fintype.card n := by
  classical
  have hn := matrix_irreducible_dimension_pos ρ
  let : NeZero (Fintype.card n) := ⟨hn.ne'⟩
  choose c hc using fun z : Subgroup.center H => irreducible_central_scalar ρ z z.property
  have hroot (z : Subgroup.center H) : c z ^ Fintype.card n = 1 := by
    have he := perfect_det_one ρ (z : H)
    rw [hc z, Matrix.det_smul, Matrix.det_one, mul_one] at he
    exact he
  have hne (z : Subgroup.center H) : c z ≠ 0 := by
    intro he
    have hr := hroot z
    simp only [he, zero_pow hn.ne', zero_ne_one] at hr
  let f : Subgroup.center H → rootsOfUnity (Fintype.card n) k := fun z =>
    ⟨Units.mk0 (c z) (hne z), (mem_rootsOfUnity _ _).mpr <| Units.ext <| hroot z⟩
  have hinj : Function.Injective f := by
    intro z w hzw
    have he : c z = c w := congrArg (fun x : rootsOfUnity (Fintype.card n) k =>
      ((x : kˣ) : k)) hzw
    apply Subtype.ext
    apply hρ
    rw [hc z, hc w, he]
  exact (Nat.card_le_card_of_injective f hinj).trans (card_rootsOfUnity k (Fintype.card n))

theorem perfect_irreducible_image_card [IsAlgClosed k] [Finite H] [Group.IsPerfect H]
    (ρ : H →* Matrix n n k) (hρ : Function.Injective ρ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    Fintype.card n ≤ Nat.card (H ⧸ Subgroup.center H) ∧
      Nat.card H ≤ (Nat.card (H ⧸ Subgroup.center H)) ^ 2 := by
  have hdegree := irreducible_degree_sq_le_order (matrixRepresentation ρ)
  rw [Module.finrank_pi] at hdegree
  have hc := perfect_irreducible_center_card ρ hρ
  have hcard : Nat.card H ≤ Fintype.card n * Nat.card (H ⧸ Subgroup.center H) := by
    rw [← (Subgroup.center H).card_mul_index, Subgroup.index_eq_card]
    exact Nat.mul_le_mul_right _ hc
  have hn := Nat.le_of_mul_le_mul_left
    (by simpa only [pow_two] using hdegree.trans hcard) (matrix_irreducible_dimension_pos ρ)
  refine ⟨hn, hcard.trans ?_⟩
  simpa only [pow_two] using Nat.mul_le_mul_right (Nat.card (H ⧸ Subgroup.center H)) hn

end PerfectImage

theorem central_quotient_card_le_of_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card (H ⧸ Subgroup.center H) ≤ Nat.card (G ⧸ Subgroup.center G) := by
  have hc : Subgroup.center G ≤ (Subgroup.center H).comap f := by
    intro z hz
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨g, rfl⟩ := hf h
    simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp hz g)
  let q := QuotientGroup.map (Subgroup.center G) (Subgroup.center H) f hc
  apply Nat.card_le_card_of_surjective q
  intro y
  induction y using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨g, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem irreducible_perfect_cover_bounds
    (p : ℕ) [Fact p.Prime] {K n : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] [Fintype n] [DecidableEq n]
    (ρ : K →* Matrix n n (AlgebraicClosure (ZMod p)))
    [Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ)] :
    Fintype.card n ≤ Nat.card (K ⧸ Subgroup.center K) ∧
    ∃ a : ℕ, 0 < a ∧ a ≤ (Nat.card (K ⧸ Subgroup.center K)) ^ 2 ∧
      ∃ B : Matrix n n (AlgebraicClosure (ZMod p)), IsUnit B ∧
        ∀ g i j, ((B⁻¹ * ρ g * B) i j) ^ (p ^ a) = (B⁻¹ * ρ g * B) i j := by
  classical
  let k := AlgebraicClosure (ZMod p)
  let I := ρ.toHomUnits.range
  let π : K →* I := ρ.toHomUnits.rangeRestrict
  let τ : I →* Matrix n n k := (Units.coeHom _).comp I.subtype
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective _
  let : Finite I := Finite.of_surjective π hπ
  let : Group.IsPerfect I := Group.IsPerfect.range ρ.toHomUnits
  let : Representation.IsIrreducible ((matrixRepresentation τ).comp π) :=
    (inferInstance : Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ))
  let : Representation.IsIrreducible (matrixRepresentation τ) :=
    irreducible_of_comp_surjective (matrixRepresentation τ) π hπ
  have hτ : Function.Injective τ := Units.val_injective.comp Subtype.val_injective
  obtain ⟨hdim, hcard⟩ := perfect_irreducible_image_card τ hτ
  have hquot := central_quotient_card_le_of_surjective π hπ
  refine ⟨hdim.trans hquot, ?_⟩
  let : Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp τ) :=
    (inferInstance : Representation.IsIrreducible (matrixRepresentation τ))
  obtain ⟨a, ha, hab, B, hB, hfix⟩ := finite_group_field_of_definition p τ
  have hcard' : Nat.card I ≤ (Nat.card (K ⧸ Subgroup.center K)) ^ 2 :=
    hcard.trans (by nlinarith)
  refine ⟨a, ha, hab.trans hcard', B, hB, ?_⟩
  intro g i j
  exact hfix (π g) i j


open Subgroup
attribute [local instance] Classical.propDecidable

structure ChiefNormalSeries (G : Type*) [Group G] where
  length : ℕ
  node : Fin (length+1) → Subgroup G
  bottom : node 0 = ⊥
  top : node (Fin.last length) = ⊤
  increasing : StrictMono node
  normal : ∀ i, (node i).Normal
  saturated : ∀ (i : Fin length) (N : Subgroup G), N.Normal →
    node i.castSucc ≤ N → N ≤ node i.succ → N = node i.castSucc ∨ N = node i.succ

attribute [instance] ChiefNormalSeries.normal

namespace ChiefNormalSeries
variable {G : Type*} [Group G] [Finite G] (s : ChiefNormalSeries G)

def factor (i : Fin s.length) : Subgroup (G ⧸ s.node i.castSucc) :=
  (s.node i.succ).map (QuotientGroup.mk' (s.node i.castSucc))

noncomputable def nonabelianCount : ℕ :=
  ∑ i : Fin s.length, if Group.IsSolvable (s.factor i) then 0 else 1

end ChiefNormalSeries

namespace PerfectCoverChiefObstruction

variable {T : Type*} [Group T]

def coordPrefix (n k : ℕ) : Subgroup (Fin n → T) where
  carrier := {g | ∀ j, k ≤ j.val → g j = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  inv_mem' := by
    intro a ha j hj
    simp [ha j hj]

instance prefix_normal (n k : ℕ) : (coordPrefix (T := T) n k).Normal := by
  refine ⟨?_⟩
  intro a ha b j hj
  change b j * a j * (b j)⁻¹ = 1
  simp [ha j hj]

lemma prefix_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    coordPrefix (T := T) n i ≤ coordPrefix n j := by
  intro g hg k hk
  exact hg k (hij.trans hk)

lemma single_mem_coordPrefix (n k : ℕ) (i : Fin n) (t : T) (hi : i.val < k) :
    Pi.mulSingle i t ∈ coordPrefix n k := by
  intro j hj
  have hji : j ≠ i := by intro h; subst j; omega
  simp [hji]

lemma prefix_strictMono [Nontrivial T] (n : ℕ) :
    StrictMono (fun k : Fin (n+1) => coordPrefix (T := T) n k.val) := by
  intro i j hij
  refine lt_iff_le_not_ge.mpr ⟨prefix_mono n hij.le, ?_⟩
  obtain ⟨t, ht⟩ := exists_ne (1 : T)
  let c : Fin n := ⟨i.val, by omega⟩
  intro h
  have hmem := h (single_mem_coordPrefix n j.val c t (by exact hij))
  have hone := hmem c (le_refl i.val)
  exact ht (by simpa [c] using hone)

lemma eval_surjective (n : ℕ) (i : Fin n) :
    Function.Surjective (Pi.evalMonoidHom (fun _ : Fin n => T) i) := by
  intro t
  exact ⟨Pi.mulSingle i t, by simp⟩

lemma prefix_saturated [IsSimpleGroup T] (n : ℕ) (i : Fin n)
    (N : Subgroup (Fin n → T)) (hN : N.Normal)
    (hl : coordPrefix n i.val ≤ N) (hu : N ≤ coordPrefix n (i.val+1)) :
    N = coordPrefix n i.val ∨ N = coordPrefix n (i.val+1) := by
  let e := Pi.evalMonoidHom (fun _ : Fin n => T) i
  have he : Function.Surjective e := eval_surjective n i
  obtain h | h := (hN.map e he).eq_bot_or_eq_top
  · left
    refine le_antisymm ?_ hl
    intro g hg j hj
    by_cases hji : j = i
    · subst j
      have : e g ∈ N.map e := ⟨g, hg, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · apply hu hg j
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
  · right
    refine le_antisymm hu ?_
    intro g hg
    have : e g ∈ N.map e := by rw [h]; trivial
    obtain ⟨b, hb, heval⟩ := this
    have hquot : g * b⁻¹ ∈ coordPrefix n i.val := by
      intro j hj
      by_cases hji : j = i
      · subst j
        change g i * (b i)⁻¹ = 1
        change b i = g i at heval
        simp [heval]
      · have hsucc : i.val+1 ≤ j.val := by
          have : j.val ≠ i.val := fun h => hji (Fin.ext h)
          omega
        change g j * (b j)⁻¹ = 1
        simp [hg j hsucc, hu hb j hsucc]
    have := N.mul_mem (hl hquot) hb
    simpa only [inv_mul_cancel_right] using this

def powerChiefSeries [IsSimpleGroup T] (n : ℕ) : ChiefNormalSeries (Fin n → T) where
  length := n
  node := fun k => coordPrefix n k.val
  bottom := by
    apply le_antisymm
    · intro g hg
      apply Subgroup.mem_bot.mpr
      funext j
      exact hg j (Nat.zero_le _)
    · exact bot_le
  top := by
    apply top_unique
    intro g _ j hj
    change n ≤ j.val at hj
    omega
  increasing := prefix_strictMono n
  normal := fun _ => inferInstance
  saturated := prefix_saturated n

lemma prefix_le_eval_ker (n : ℕ) (i : Fin n) :
    coordPrefix (T := T) n i.val ≤ (Pi.evalMonoidHom (fun _ : Fin n => T) i).ker := by
  intro g hg
  exact hg i (le_refl _)

def factorEval [IsSimpleGroup T] [Finite T] (n : ℕ) (i : Fin n) :
    (powerChiefSeries (T := T) n).factor i →* T :=
  (QuotientGroup.lift (coordPrefix n i.val)
    (Pi.evalMonoidHom (fun _ : Fin n => T) i) (prefix_le_eval_ker n i)).comp
    ((powerChiefSeries n).factor i).subtype

lemma factorEval_surjective [IsSimpleGroup T] [Finite T] (n : ℕ) (i : Fin n) :
    Function.Surjective (factorEval (T := T) n i) := by
  intro t
  let g : Fin n → T := Pi.mulSingle i t
  have hg : g ∈ coordPrefix n (i.val+1) := single_mem_coordPrefix n (i.val+1) i t (by omega)
  refine ⟨⟨QuotientGroup.mk' (coordPrefix n i.val) g, ⟨g, hg, rfl⟩⟩, ?_⟩
  change g i = t
  simp [g]

lemma factorEval_injective [IsSimpleGroup T] [Finite T] (n : ℕ) (i : Fin n) :
    Function.Injective (factorEval (T := T) n i) := by
  apply (factorEval (T := T) n i).ker_eq_bot_iff.mp
  apply bot_unique
  rintro ⟨q, hq⟩ hk
  obtain ⟨g, hg, rfl⟩ := hq
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  change (g : (Fin n → T) ⧸ coordPrefix n i.val) = 1
  apply (QuotientGroup.eq_one_iff g).mpr
  intro j hj
  by_cases hji : j = i
  · subst j
    exact hk
  · have hs : i.val + 1 ≤ j.val := by
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
    exact hg j hs

noncomputable def factorEvalEquiv [IsSimpleGroup T] [Finite T] (n : ℕ) (i : Fin n) :
    (powerChiefSeries (T := T) n).factor i ≃* T :=
  MulEquiv.ofBijective (factorEval n i) ⟨factorEval_injective n i, factorEval_surjective n i⟩

lemma powerChiefSeries_factor_perfect [IsSimpleGroup T] [Finite T]
    [Group.IsPerfect T] (n : ℕ) (i : Fin n) :
    Group.IsPerfect ((powerChiefSeries (T := T) n).factor i) :=
  Group.IsPerfect.ofSurjective (f := (factorEvalEquiv n i).symm.toMonoidHom)
    (factorEvalEquiv n i).symm.surjective

lemma powerChiefSeries_count [IsSimpleGroup T] [Finite T]
    [Group.IsPerfect T] (n : ℕ) :
    (powerChiefSeries (T := T) n).nonabelianCount = n := by
  have hn (i : Fin n) : ¬ Group.IsSolvable ((powerChiefSeries (T := T) n).factor i) := by
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable T
      (Group.isSolvable_of_surjective (factorEval_surjective n i))
  unfold ChiefNormalSeries.nonabelianCount
  change (∑ i : Fin n, if Group.IsSolvable ((powerChiefSeries (T := T) n).factor i)
    then 0 else 1) = n
  simp [hn]

lemma perfect_power [Group.IsPerfect T] (n : ℕ) : Group.IsPerfect (Fin n → T) := by
  refine ⟨?_⟩
  have h := Subgroup.commutator_pi_pi_of_finite
    (fun _ : Fin n => (⊤ : Subgroup T)) (fun _ : Fin n => (⊤ : Subgroup T))
  simpa only [Subgroup.pi_top, ← commutator_def,
    Group.IsPerfect.commutator_eq_top] using h

theorem no_perfect_group_chief_bound (r : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (_ : Group.IsPerfect G)
      (s : ChiefNormalSeries G), s.nonabelianCount = r := by
  let T := alternatingGroup (Fin 5)
  let : IsSimpleGroup T := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect T := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Fin r → T) := perfect_power r
  exact ⟨Fin r → T, inferInstance, inferInstance, inferInstance,
    powerChiefSeries r, powerChiefSeries_count r⟩

def PerfectCoverEstimates (K : Type) [Group K] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : K →* Matrix n n (AlgebraicClosure (ZMod p))),
    Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ) →
    Fintype.card n ≤ Nat.card (K ⧸ Subgroup.center K) ∧
    ∃ a : ℕ, 0 < a ∧ a ≤ (Nat.card (K ⧸ Subgroup.center K)) ^ 2 ∧
      ∃ B : Matrix n n (AlgebraicClosure (ZMod p)), IsUnit B ∧
        ∀ g i j, ((B⁻¹ * ρ g * B) i j) ^ (p ^ a) = (B⁻¹ * ρ g * B) i j

theorem perfectCoverEstimates (K : Type) [Group K] [Finite K]
    [Group.IsPerfect K] : PerfectCoverEstimates K := by
  intro p hp n hn hd ρ hρ
  let := hρ
  exact irreducible_perfect_cover_bounds p ρ

theorem cover_estimates_with_many_chief_layers (r : ℕ) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (_ : Group.IsPerfect G)
      (s : ChiefNormalSeries G), s.nonabelianCount = r ∧ PerfectCoverEstimates G ∧
        ∀ i, PerfectCoverEstimates (s.factor i) := by
  let T := alternatingGroup (Fin 5)
  let : IsSimpleGroup T := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect T := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Fin r → T) := perfect_power r
  refine ⟨Fin r → T, inferInstance, inferInstance, inferInstance,
    powerChiefSeries r, powerChiefSeries_count r, perfectCoverEstimates _, ?_⟩
  intro i
  let := powerChiefSeries_factor_perfect (T := T) r i
  exact perfectCoverEstimates ((powerChiefSeries (T := T) r).factor i)

theorem cover_estimates_do_not_imply_five_chief_layers :
    ¬ (∀ (G : Type) (_ : Group G) (_ : Finite G) (_ : Group.IsPerfect G),
      ∀ (s : ChiefNormalSeries G), PerfectCoverEstimates G →
      (∀ i, ¬ Group.IsSolvable (s.factor i) → PerfectCoverEstimates (s.factor i)) →
      s.nonabelianCount ≤ 5) := by
  intro h
  obtain ⟨G, gG, fG, pG, s, hs, hb, hl⟩ := cover_estimates_with_many_chief_layers 6
  have hh := h G gG fG pG s hb (fun i _ => hl i)
  omega


end PerfectCoverChiefObstruction
end FiniteLatticeGap

namespace FiniteLattice

def Fenced {α : Type*} [Lattice α] (a b : α) : Prop :=
  (∃ c, a < c ∧ c < b) ∧
    ∀ c, a < c → c < b →
      ∃ u v, a < u ∧ u < v ∧ v < b ∧
        c ⊓ u = a ∧ c ⊓ v = a ∧ c ⊔ u = b ∧ c ⊔ v = b

theorem Fenced.not_modular {α : Type*} [Lattice α] {a b : α}
    (h : Fenced a b) : ¬ IsModularLattice α := by
  intro hm
  let := hm
  obtain ⟨c, hca, hcb⟩ := h.1
  obtain ⟨u, v, hau, huv, hvb, hcu, hcv, hsu, hsv⟩ := h.2 c hca hcb
  have heq := sup_inf_assoc_of_le c huv.le
  rw [sup_comm u c, hsu, inf_eq_right.mpr hvb.le, hcv,
    sup_eq_left.mpr hau.le] at heq
  exact huv.ne heq.symm

theorem Fenced.not_modular_interval {α : Type*} [Lattice α] {a b : α}
    (h : Fenced a b) : ¬ IsModularLattice (Set.Icc a b) := by
  intro hm
  let := hm
  obtain ⟨c, hca, hcb⟩ := h.1
  obtain ⟨u, v, hau, huv, hvb, hcu, hcv, hsu, hsv⟩ := h.2 c hca hcb
  let c' : Set.Icc a b := ⟨c, hca.le, hcb.le⟩
  let u' : Set.Icc a b := ⟨u, hau.le, huv.le.trans hvb.le⟩
  let v' : Set.Icc a b := ⟨v, hau.le.trans huv.le, hvb.le⟩
  have heq := congrArg (fun x : Set.Icc a b => x.val)
    (sup_inf_assoc_of_le c' (show u' ≤ v' from huv.le))
  change (u ⊔ c) ⊓ v = u ⊔ (c ⊓ v) at heq
  rw [sup_comm u c, hsu, inf_eq_right.mpr hvb.le, hcv,
    sup_eq_left.mpr hau.le] at heq
  exact huv.ne heq.symm

section NormalSubgroupTest

variable {G : Type*} [Group G]

theorem normal_sup_inf_le (U V R : Subgroup G) [R.Normal] (hUV : U ≤ V) :
    (U ⊔ R) ⊓ V ≤ U ⊔ (R ⊓ V) := by
  intro x hx
  obtain ⟨u, hu, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx.1
  have hrV : r ∈ V := by
    have h := V.mul_mem (V.inv_mem (hUV hu)) hx.2
    simpa only [inv_mul_cancel_left] using h
  exact (U ⊔ (R ⊓ V)).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hr, hrV⟩)

theorem normal_test (D R : Subgroup G) [R.Normal]
    (hf : Fenced D (⊤ : Subgroup G)) : R ≤ D ∨ D ⊔ R = ⊤ := by
  by_cases hRD : R ≤ D
  · exact Or.inl hRD
  right
  by_contra htop
  have hDC : D < D ⊔ R := lt_of_le_of_ne le_sup_left (by
    intro heq
    exact hRD (heq ▸ le_sup_right))
  have hCT : D ⊔ R < ⊤ := lt_top_iff_ne_top.mpr htop
  obtain ⟨U, V, hDU, hUV, hVT, hCU, hCV, hsupU, hsupV⟩ :=
    hf.2 (D ⊔ R) hDC hCT
  have hsup : U ⊔ R = ⊤ := by
    calc
      U ⊔ R = (D ⊔ R) ⊔ U := by
        rw [sup_right_comm, sup_eq_right.mpr hDU.le, sup_comm]
      _ = ⊤ := hsupU
  have hRV : R ⊓ V ≤ D := by
    calc
      R ⊓ V ≤ (D ⊔ R) ⊓ V := inf_le_inf_right V le_sup_right
      _ = D := hCV
  have hVU : V ≤ U := by
    calc
      V = (U ⊔ R) ⊓ V := by rw [hsup, top_inf_eq]
      _ ≤ U ⊔ (R ⊓ V) := normal_sup_inf_le U V R hUV.le
      _ ≤ U := sup_le le_rfl (hRV.trans hDU.le)
  exact hUV.not_ge hVU

end NormalSubgroupTest


end FiniteLattice

end OAI
