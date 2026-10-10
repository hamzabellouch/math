import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Order.ModularLattice
import Mathlib.Tactic.Abel

namespace OAI

section

/-!
Complements adapted to an affine restriction. The prescribed directions are
contained in a small summand, and the complementary directions are mapped into
the prescribed target subspace. This is ordinary finite-dimensional geometry;
no Fourier inequality or pseudorandomness hypothesis is used.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionComplement

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F]

/-- Enlarge prescribed directions by at most the rank of `L`, leaving a
complement on which `L` vanishes. -/
theorem exists_bounded_complement_of_linearMap
    (V1 : Submodule K E) (L : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker L ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (LinearMap.range L) := by
  obtain ⟨D, hD⟩ := (LinearMap.ker L).exists_isCompl
  let U : Submodule K E := V1 ⊔ D
  have hcover : Codisjoint (LinearMap.ker L) U :=
    hD.codisjoint.mono_right le_sup_right
  obtain ⟨E0, hE0, hcompl⟩ := hcover.exists_isCompl
  refine ⟨U, E0, le_sup_left, hE0, hcompl.symm, ?_⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl hD
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hDdim : Module.finrank K D = Module.finrank K (LinearMap.range L) := by
    omega
  exact (Submodule.finrank_add_le_finrank_add_finrank V1 D).trans
    (by rw [hDdim])

/-- Split the domain while preserving `V1` and mapping all complementary
directions into `W`. The extra dimension is at most the codimension of `W`. -/
theorem exists_bounded_complement [FiniteDimensional K F]
    (V1 : Submodule K E) (W : Submodule K F) (T : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker (W.mkQ.comp T) ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (F ⧸ W) := by
  obtain ⟨U, E0, hV1, hE0, hcompl, hdim⟩ :=
    exists_bounded_complement_of_linearMap V1 (W.mkQ.comp T)
  refine ⟨U, E0, hV1, hE0, hcompl, hdim.trans ?_⟩
  exact Nat.add_le_add_left (Submodule.finrank_le (LinearMap.range (W.mkQ.comp T))) _

end UniqueGamesTheorem.Inverse.KMSAffineRestrictionComplement

end

section

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Split off the coordinate measured by `a`, using the prescribed vector `t`.
The kernel coordinate is exactly `x - a x • t`. -/
def splitEquiv (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    F ≃ₗ[K] (a.ker × K) where
  toFun x := (⟨x - a x • t, by simp [LinearMap.mem_ker, ht]⟩, a x)
  invFun p := (p.1 : F) + p.2 • t
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - a (x + y) • t = (x - a x • t) + (y - a y • t)
      rw [map_add, add_smul]
      abel
    · exact a.map_add x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - a (c • x) • t = c • (x - a x • t)
      simp [smul_sub, smul_smul]
    · exact a.map_smul c x
  left_inv x := by
    change x - a x • t + a x • t = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : a (p.1 : F) = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : F) + p.2 • t - a ((p.1 : F) + p.2 • t) • t = p.1
      simp [hp, ht]
    · change a ((p.1 : F) + p.2 • t) = p.2
      simp [hp, ht]

@[simp] theorem splitEquiv_apply_snd (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    (splitEquiv a t ht x).2 = a x := rfl

@[simp] theorem splitEquiv_apply_fst_coe (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    ((splitEquiv a t ht x).1 : F) = x - a x • t := rfl

@[simp] theorem splitEquiv_symm_apply (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (p : a.ker × K) :
    (splitEquiv a t ht).symm p = (p.1 : F) + p.2 • t := rfl

@[simp] theorem splitEquiv_symm_apply_zero (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : (splitEquiv a t ht).symm (b, 0) = (b : F) := by
  simp

@[simp] theorem splitEquiv_apply_ker (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : splitEquiv a t ht (b : F) = (b, 0) := by
  apply (splitEquiv a t ht).symm.injective
  simp

@[simp] theorem splitEquiv_apply_unit (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    splitEquiv a t ht t = (0, 1) := by
  apply (splitEquiv a t ht).symm.injective
  simp

/-- A functional with a unit preimage has a kernel of codimension one. -/
theorem finrank_eq_ker_add_one [FiniteDimensional K F]
    (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    Module.finrank K F = Module.finrank K a.ker + 1 := by
  have h := (splitEquiv a t ht).finrank_eq
  simpa [Module.finrank_prod] using h

end UniqueGamesTheorem.Inverse.KMSAnalyticFunctionalSplit

end

section

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

/-- Data of one common coordinate and compatible section vectors. All maps
and all smaller spaces below are constructed from these original data. -/
structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def targetEquiv (s : CompatibleSplitting π A) : K ≃ₗ[F2] (s.K0 × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv s.functional s.targetVector
    s.functional_targetVector

def leftEquiv (s : CompatibleSplitting π A) : I ≃ₗ[F2] (s.J × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

def rightEquiv (s : CompatibleSplitting π A) : F ≃ₗ[F2] (s.B × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

/-- The remaining part of the left surjection is its literal restriction. -/
def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

/-- The remaining part of the right surjection is its literal restriction. -/
def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

@[simp] theorem leftMap_apply_val (s : CompatibleSplitting π A) (x : s.J) :
    (s.leftMap x : K) = π x := rfl

@[simp] theorem rightMap_apply_val (s : CompatibleSplitting π A) (x : s.B) :
    (s.rightMap x : K) = A x := rfl

theorem leftMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.leftMap := by
  intro y
  obtain ⟨x, hx⟩ := s.left_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (π x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

theorem rightMap_surjective (s : CompatibleSplitting π A) :
    Function.Surjective s.rightMap := by
  intro y
  obtain ⟨x, hx⟩ := s.right_surjective y.val
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change s.functional (A x) = 0
    rw [hx]
    exact y.property
  · apply Subtype.ext
    exact hx

@[simp] theorem leftEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    s.leftEquiv.symm x = (x.1 : I) + x.2 • s.leftVector := rfl

@[simp] theorem rightEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    s.rightEquiv.symm x = (x.1 : F) + x.2 • s.rightVector := rfl

@[simp] theorem targetEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.K0 × F2) :
    s.targetEquiv.symm x = (x.1 : K) + x.2 • s.targetVector := rfl

theorem left_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    π (s.leftEquiv.symm x) = s.targetEquiv.symm (s.leftMap x.1, x.2) := by
  change π ((x.1 : I) + x.2 • s.leftVector) = π x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.leftVector_image]

theorem right_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    A (s.rightEquiv.symm x) = s.targetEquiv.symm (s.rightMap x.1, x.2) := by
  change A ((x.1 : F) + x.2 • s.rightVector) = A x.1 + x.2 • s.targetVector
  rw [map_add, map_smul, s.rightVector_image]

/-- Both changes of coordinates use the same final binary coordinate. -/
theorem left_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (π.comp s.leftEquiv.symm.toLinearMap) =
      s.leftMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (π (s.leftEquiv.symm x)) = (s.leftMap x.1, x.2)
  rw [s.left_symm_apply, s.targetEquiv.apply_symm_apply]

theorem right_conjugation (s : CompatibleSplitting π A) :
    s.targetEquiv.toLinearMap.comp (A.comp s.rightEquiv.symm.toLinearMap) =
      s.rightMap.prodMap (LinearMap.id : F2 →ₗ[F2] F2) := by
  apply LinearMap.ext
  intro x
  change s.targetEquiv (A (s.rightEquiv.symm x)) = (s.rightMap x.1, x.2)
  rw [s.right_symm_apply, s.targetEquiv.apply_symm_apply]

theorem target_finrank [FiniteDimensional F2 K] (s : CompatibleSplitting π A) :
    Module.finrank F2 K = Module.finrank F2 s.K0 + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one s.functional s.targetVector
    s.functional_targetVector

theorem left_finrank [FiniteDimensional F2 I] (s : CompatibleSplitting π A) :
    Module.finrank F2 I = Module.finrank F2 s.J + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

theorem right_finrank [FiniteDimensional F2 F] (s : CompatibleSplitting π A) :
    Module.finrank F2 F = Module.finrank F2 s.B + 1 :=
  KMSAnalyticFunctionalSplit.finrank_eq_ker_add_one (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

end CompatibleSplitting

/-- Positive target dimension supplies a basis coordinate; surjectivity
supplies its two lifts. No additional splitting hypothesis is required. -/
theorem exists_compatibleSplitting [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : Nonempty (CompatibleSplitting π A) := by
  classical
  let b := Module.finBasis F2 K
  let j : Fin (Module.finrank F2 K) := ⟨0, hdim⟩
  obtain ⟨i, hi⟩ := hπ (b j)
  obtain ⟨f, hf⟩ := hA (b j)
  refine ⟨⟨b.coord j, b j, ?_, i, hi, f, hf, hπ, hA⟩⟩
  simp

def chooseSplit [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : CompatibleSplitting π A :=
  Classical.choice (exists_compatibleSplitting π A hπ hA hdim)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticCompatibleSplitting

end

section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The chosen block compression: restrict to `B`, then forget `A`. -/
def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

/-- Coordinates of a map whose compression is `(z,0)`. -/
structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

/-- Assemble the three blocks. The last coordinate vanishes on `B`. -/
def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

/-- Extract the unique coordinates from an actual compressed-fiber element. -/
def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

/-- An exact compressed-fiber parametrization, valid over any ring. -/
def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

/-- Equality of assembled maps forces equality of every chosen coordinate;
there are no hidden change-of-basis fibers in this parametrization. -/
theorem assemble_injective (z : B →ₗ[R] W) :
    Function.Injective (assemble (R := R) (A := A) (D := D) (C := C) (z := z)) := by
  intro p q h
  have hh : (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm p =
      (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm q := Subtype.ext h
  exact (compressedFiberEquiv (A := A) (D := D) (C := C) z).symm.injective hh

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

end OAI
