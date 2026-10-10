import OAI.MathematicalPhysics.Heisenberg.Model

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical

open scoped ComplexConjugate BigOperators
namespace Heisenberg

instance quasiLocalNormedRing (d ℓ : ℕ) : NormedRing (QuasiLocal d ℓ) :=
  SubringClass.toNormedRing (quasiLocalAlgebra d ℓ)

instance quasiLocalStarRing (d ℓ : ℕ) : StarRing (QuasiLocal d ℓ) :=
  (quasiLocalAlgebra d ℓ).starRing

instance quasiLocalNormedAlgebra (d ℓ : ℕ) : NormedAlgebra ℂ (QuasiLocal d ℓ) :=
  SubalgebraClass.toNormedAlgebra (quasiLocalAlgebra d ℓ)

instance quasiLocalAddCommGroup (d ℓ : ℕ) : AddCommGroup (QuasiLocal d ℓ) :=
  (SubringClass.toRing (quasiLocalAlgebra d ℓ)).toAddCommGroup

instance quasiLocalAddCommMonoid (d ℓ : ℕ) : AddCommMonoid (QuasiLocal d ℓ) :=
  (quasiLocalAddCommGroup d ℓ).toAddCommMonoid

instance quasiLocalAddMonoid (d ℓ : ℕ) : AddMonoid (QuasiLocal d ℓ) :=
  (quasiLocalAddCommMonoid d ℓ).toAddMonoid

instance quasiLocalAddZeroClass (d ℓ : ℕ) : AddZeroClass (QuasiLocal d ℓ) :=
  (quasiLocalAddMonoid d ℓ).toAddZeroClass

instance quasiLocalAddCommMagma (d ℓ : ℕ) : AddCommMagma (QuasiLocal d ℓ) :=
  (quasiLocalAddCommMonoid d ℓ).toAddCommMagma

instance quasiLocalStarMul (d ℓ : ℕ) : StarMul (QuasiLocal d ℓ) :=
  (quasiLocalAlgebra d ℓ).starRing.toStarMul

instance quasiLocalModule (d ℓ : ℕ) : Module ℂ (QuasiLocal d ℓ) :=
  (SubalgebraClass.toNormedAlgebra (quasiLocalAlgebra d ℓ)).toNormedSpace.toModule

@[simp] theorem matrixUnit_mul_same (d ℓ : ℕ) (x : Site d) (a b c e : Level ℓ) :
    matrixUnit d ℓ x a b * matrixUnit d ℓ x c e =
      if b = c then matrixUnit d ℓ x a e else 0 := by
  classical
  ext v z
  change (matrixUnit d ℓ x a b) ((matrixUnit d ℓ x c e) v) z = _
  by_cases hbc : b = c
  · subst c
    simp only [matrixUnit_apply, Finsupp.update_apply, ite_true]
    by_cases hza : z x = a <;> simp [hza]
  · simp only [matrixUnit_apply, Finsupp.update_apply, hbc, ite_false]
    by_cases hza : z x = a <;> simp [hza, hbc]

@[simp] theorem matrixUnit_diagonal_sum (d ℓ : ℕ) (x : Site d) :
    ∑ a : Level ℓ, matrixUnit d ℓ x a a = 1 := by
  classical
  ext v z
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    matrixUnit_apply, one_apply_eq_self]
  rw [Finset.sum_ite_eq]
  simp [Finsupp.update_self]

theorem matrixUnits_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    (a b c e : Level ℓ) :
    Commute (matrixUnit d ℓ x a b) (matrixUnit d ℓ y c e) := by
  classical
  change _ * _ = _ * _
  ext v z
  change matrixUnit d ℓ x a b (matrixUnit d ℓ y c e v) z =
    matrixUnit d ℓ y c e (matrixUnit d ℓ x a b v) z
  simp only [matrixUnit_apply]
  by_cases hx : z x = a <;> by_cases hy : z y = c <;>
    simp [hx, hy, Finsupp.update_apply, hxy, Ne.symm hxy, Finsupp.update_comm z hxy]

@[simp] theorem localUnit_mul_same (d ℓ : ℕ) (x : Site d) (a b c e : Level ℓ) :
    localUnit d ℓ x a b * localUnit d ℓ x c e =
      if b = c then localUnit d ℓ x a e else 0 := by
  classical
  apply Subtype.ext
  change matrixUnit d ℓ x a b * matrixUnit d ℓ x c e = _
  rw [matrixUnit_mul_same]
  split_ifs <;> rfl

@[simp] theorem localUnit_diagonal_sum (d ℓ : ℕ) (x : Site d) :
    ∑ a : Level ℓ, localUnit d ℓ x a a = 1 := by
  apply Subtype.ext
  change (quasiLocalAlgebra d ℓ).subtype (∑ a : Level ℓ, localUnit d ℓ x a a) =
    (quasiLocalAlgebra d ℓ).subtype 1
  rw [map_sum, map_one]
  exact matrixUnit_diagonal_sum d ℓ x

theorem localUnits_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    (a b c e : Level ℓ) :
    Commute (localUnit d ℓ x a b) (localUnit d ℓ y c e) := by
  change _ * _ = _ * _
  apply Subtype.ext
  exact (matrixUnits_commute hxy a b c e).eq

@[simp] theorem star_l2Projection {ι : Type*} (p : ι → Prop) :
    star (l2Projection p) = l2Projection p := by
  classical
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [lp.inner_eq_tsum, l2Projection_apply]
  apply tsum_congr
  intro i
  by_cases h : p i <;> simp [h]

@[simp] theorem star_l2Reindex {ι : Type*} (e : Equiv.Perm ι) :
    star ((l2Reindex e).toContinuousLinearEquiv.toContinuousLinearMap) =
      (l2Reindex e.symm).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  have h := (l2Reindex e).inner_map_map (l2Reindex e.symm v) w
  have he : l2Reindex e (l2Reindex e.symm v) = v := by
    ext i
    simp
  rw [he] at h
  exact h.symm

@[simp] theorem configPerm_swap_symm (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    (configPerm d ℓ x (Equiv.swap a b)).symm = configPerm d ℓ x (Equiv.swap a b) := by
  classical
  ext c
  simp [configPerm, Equiv.symm_swap]

@[simp] theorem star_matrixUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    star (matrixUnit d ℓ x a b) = matrixUnit d ℓ x b a := by
  classical
  change star (l2Projection (fun c : Configuration d ℓ => c x = a) *
    (l2Reindex (configPerm d ℓ x (Equiv.swap a b))).toContinuousLinearEquiv.toContinuousLinearMap) = _
  rw [star_mul, star_l2Projection, star_l2Reindex, configPerm_swap_symm]
  ext v z
  change l2Reindex (configPerm d ℓ x (Equiv.swap a b))
    (l2Projection (fun c : Configuration d ℓ => c x = a) v) z = _
  simp only [l2Reindex_apply, l2Projection_apply, matrixUnit_apply]
  change (if ((z.update x ((Equiv.swap a b).symm (z x))) x) = a then
      v (z.update x ((Equiv.swap a b).symm (z x))) else 0) =
    if z x = b then v (z.update x a) else 0
  simp only [Finsupp.update_apply, ite_true, Equiv.symm_swap]
  by_cases h : z x = b
  · simp [h]
  · have hn : Equiv.swap a b (z x) ≠ a := by
      intro he
      have := congrArg (Equiv.swap a b) he
      simp at this
      exact h this
    simp only [h, hn, ite_false]

@[simp] theorem star_localUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    star (localUnit d ℓ x a b) = localUnit d ℓ x b a := by
  apply Subtype.ext
  exact star_matrixUnit d ℓ x a b

@[simp] theorem star_spinZ (d ℓ : ℕ) (x : Site d) :
    star (spinZ d ℓ x) = spinZ d ℓ x := by
  simp [spinZ, star_sum, star_smul]

@[simp] theorem star_spinX (d ℓ : ℕ) (x : Site d) :
    star (spinX d ℓ x) = spinX d ℓ x := by
  simp [spinX, spinMinus, star_smul, add_comm]

@[simp] theorem star_spinY (d ℓ : ℕ) (x : Site d) :
    star (spinY d ℓ x) = spinY d ℓ x := by
  simp only [spinY, spinMinus, star_smul, star_sub, star_star]
  rw [← neg_sub (spinPlus d ℓ x) (star (spinPlus d ℓ x)), smul_neg, ← neg_smul]
  congr 1
  simp

@[simp] theorem spinZ_mul_localUnit (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    spinZ d ℓ x * localUnit d ℓ x a b =
      (magneticLevel ℓ a : ℂ) • localUnit d ℓ x a b := by
  classical
  simp only [spinZ, Finset.sum_mul, smul_mul_assoc, localUnit_mul_same]
  simp [smul_ite]

@[simp] theorem localUnit_mul_spinZ (d ℓ : ℕ) (x : Site d) (a b : Level ℓ) :
    localUnit d ℓ x a b * spinZ d ℓ x =
      (magneticLevel ℓ b : ℂ) • localUnit d ℓ x a b := by
  classical
  simp only [spinZ, Finset.mul_sum, mul_smul_comm, localUnit_mul_same]
  simp [smul_ite]

lemma magneticLevel_succ (ℓ : ℕ) (k : Fin ℓ) :
    magneticLevel ℓ k.succ = magneticLevel ℓ k.castSucc + 1 := by
  simp [magneticLevel]
  ring

theorem spinZ_spinPlus (d ℓ : ℕ) (x : Site d) :
    spinZ d ℓ x * spinPlus d ℓ x =
      spinPlus d ℓ x * spinZ d ℓ x + spinPlus d ℓ x := by
  classical
  simp only [spinPlus, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, spinZ_mul_localUnit, localUnit_mul_spinZ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [magneticLevel_succ, Complex.ofReal_add, Complex.ofReal_one,
    smul_smul, smul_smul, ← add_smul]
  congr 1
  ring

theorem spinZ_spinMinus (d ℓ : ℕ) (x : Site d) :
    spinZ d ℓ x * spinMinus d ℓ x =
      spinMinus d ℓ x * spinZ d ℓ x - spinMinus d ℓ x := by
  have h := congrArg star (spinZ_spinPlus d ℓ x)
  simp only [star_mul, star_add, star_spinZ] at h
  change spinZ d ℓ x * star (spinPlus d ℓ x) = _
  rw [eq_sub_iff_add_eq]
  exact h.symm

def localAlgebra (d ℓ : ℕ) (F : Set (Site d)) : StarSubalgebra ℂ (QuasiLocal d ℓ) :=
  StarAlgebra.adjoin ℂ {A | ∃ x ∈ F, ∃ a b, A = localUnit d ℓ x a b}

lemma localUnit_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d}
    (hx : x ∈ F) (a b : Level ℓ) : localUnit d ℓ x a b ∈ localAlgebra d ℓ F :=
  StarAlgebra.subset_adjoin ℂ _ ⟨x, hx, a, b, rfl⟩

lemma spinZ_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinZ d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k k) _

lemma spinPlus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinPlus d ℓ x ∈ localAlgebra d ℓ F := by
  apply Subalgebra.sum_mem
  intro k _
  exact (localAlgebra d ℓ F).smul_mem (localUnit_mem_localAlgebra d ℓ F hx k.succ k.castSucc) _

lemma spinMinus_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinMinus d ℓ x ∈ localAlgebra d ℓ F :=
  star_mem (spinPlus_mem_localAlgebra d ℓ F hx)

lemma spinX_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinX d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).add_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

lemma spinY_mem_localAlgebra (d ℓ : ℕ) (F : Set (Site d)) {x : Site d} (hx : x ∈ F) :
    spinY d ℓ x ∈ localAlgebra d ℓ F :=
  (localAlgebra d ℓ F).smul_mem ((localAlgebra d ℓ F).sub_mem
    (spinPlus_mem_localAlgebra d ℓ F hx) (spinMinus_mem_localAlgebra d ℓ F hx)) _

theorem localAlgebras_commute {d ℓ : ℕ} {F G : Set (Site d)} (hFG : Disjoint F G)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ F) (hB : B ∈ localAlgebra d ℓ G) :
    Commute A B := by
  have hg (x : Site d) (hx : x ∈ F) (a b : Level ℓ) :
      localAlgebra d ℓ G ≤ StarSubalgebra.centralizer ℂ {localUnit d ℓ x a b} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨y, hy, c, e, rfl⟩
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp hFG hx) (h ▸ hy)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨(localUnits_commute hxy a b c e).eq, by
      rw [star_localUnit]
      exact (localUnits_commute hxy b a c e).eq⟩
  have hle : localAlgebra d ℓ F ≤ StarSubalgebra.centralizer ℂ {B} := by
    apply StarAlgebra.adjoin_le
    rintro _ ⟨x, hx, a, b, rfl⟩
    have h₁ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hg x hx a b hB)) _ (Set.mem_singleton _)
    have h₂ := ((StarSubalgebra.mem_centralizer_iff ℂ).mp
      (hg x hx a b (star_mem hB))) _ (Set.mem_singleton _)
    change _ ∈ StarSubalgebra.centralizer ℂ _
    rw [StarSubalgebra.mem_centralizer_iff ℂ]
    rintro _ rfl
    exact ⟨h₁.1.symm, h₂.1.symm⟩
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA)) B (Set.mem_singleton B)).1.symm

lemma singleton_local_commute {d ℓ : ℕ} {x y : Site d} (hxy : x ≠ y)
    {A B : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ {x})
    (hB : B ∈ localAlgebra d ℓ {y}) : Commute A B :=
  localAlgebras_commute (Set.disjoint_singleton.mpr hxy) hA hB

lemma nearestNeighbor_ne {d : ℕ} {x y : Site d} (h : NearestNeighbor x y) : x ≠ y := by
  intro he
  subst y
  simp [NearestNeighbor] at h

theorem star_hamiltonian (d ℓ : ℕ) (Λ : Finset (Site d)) :
    star (hamiltonian d ℓ Λ) = hamiltonian d ℓ Λ := by
  classical
  simp only [hamiltonian, star_neg, star_sum, star_add, star_mul,
    star_spinX, star_spinY, star_spinZ]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hxy := nearestNeighbor_ne (Finset.mem_filter.mp he).2.1
  have hX := singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {e.1} rfl)
    (spinX_mem_localAlgebra d ℓ {e.2} rfl)
  have hY := singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {e.1} rfl)
    (spinY_mem_localAlgebra d ℓ {e.2} rfl)
  have hZ := singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {e.1} rfl)
    (spinZ_mem_localAlgebra d ℓ {e.2} rfl)
  rw [hX.eq, hY.eq, hZ.eq]

instance quasiLocalComplete (d ℓ : ℕ) : CompleteSpace (QuasiLocal d ℓ) :=
  (StarSubalgebra.isClosed_topologicalClosure _).completeSpace_coe

instance quasiLocalRationalAlgebra (d ℓ : ℕ) : NormedAlgebra ℚ (QuasiLocal d ℓ) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

lemma imaginaryTime_skew (t : ℝ) : Complex.I * (t : ℂ) ∈ skewAdjoint ℂ := by
  change star (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ))
  simp

lemma hamiltonian_selfAdjoint (d ℓ : ℕ) (Λ : Finset (Site d)) :
    IsSelfAdjoint (hamiltonian d ℓ Λ) := star_hamiltonian d ℓ Λ

lemma timeHamiltonian_skew (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    (Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ ∈ skewAdjoint (QuasiLocal d ℓ) :=
  IsSelfAdjoint.smul_mem_skewAdjoint (imaginaryTime_skew t) (hamiltonian_selfAdjoint d ℓ Λ)

lemma finiteUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (timeHamiltonian_skew d ℓ Λ t)

lemma finiteInverseUnitary (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) ∈ unitary (QuasiLocal d ℓ) := by
  convert finiteUnitary d ℓ Λ (-t) using 1; simp

theorem norm_finiteDynamics (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    ‖finiteDynamics d ℓ Λ t A‖ = ‖A‖ := by
  rw [finiteDynamics, CStarRing.norm_mul_mem_unitary _ (finiteInverseUnitary d ℓ Λ t),
    CStarRing.norm_mem_unitary_mul _ (finiteUnitary d ℓ Λ t)]

lemma finiteDynamics_add (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A B : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (A + B) = finiteDynamics d ℓ Λ t A + finiteDynamics d ℓ Λ t B := by
  simp [finiteDynamics, mul_add, add_mul]

lemma finiteDynamics_smul (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (c : ℂ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (c • A) = c • finiteDynamics d ℓ Λ t A := by
  simp [finiteDynamics]

lemma finiteDynamics_sub (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A B : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (A - B) = finiteDynamics d ℓ Λ t A - finiteDynamics d ℓ Λ t B := by
  simp [finiteDynamics, mul_sub, sub_mul]

theorem finiteDynamics_isometry (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    Isometry (finiteDynamics d ℓ Λ t) := by
  apply Isometry.of_dist_eq
  intro A B
  simp only [dist_eq_norm, ← finiteDynamics_sub, norm_finiteDynamics]

@[simp] theorem finiteDynamics_zero (d ℓ : ℕ) (Λ : Finset (Site d)) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ 0 A = A := by
  simp [finiteDynamics]

lemma exp_time_star (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    star (NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ)) =
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) := by
  rw [NormedSpace.star_exp, star_smul, star_hamiltonian]
  simp

theorem finiteDynamics_star (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (star A) = star (finiteDynamics d ℓ Λ t A) := by
  rw [finiteDynamics, finiteDynamics, ← exp_time_star]
  simp only [star_mul, star_star]
  exact mul_assoc _ _ _

lemma exp_time_inverse_left (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) *
      NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) = 1 := by
  rw [← exp_time_star]
  exact Unitary.star_mul_self_of_mem (finiteUnitary d ℓ Λ t)

lemma exp_time_inverse_right (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) *
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) = 1 := by
  rw [← exp_time_star]
  exact Unitary.mul_star_self_of_mem (finiteUnitary d ℓ Λ t)

@[simp] theorem finiteDynamics_one (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    finiteDynamics d ℓ Λ t 1 = 1 := by
  simp only [finiteDynamics, mul_one, exp_time_inverse_right]

theorem finiteDynamics_mul (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) (A B : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ t (A * B) =
      finiteDynamics d ℓ Λ t A * finiteDynamics d ℓ Λ t B := by
  let U := NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ)
  let V := NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ)
  have hVU : V * U = 1 := exp_time_inverse_left d ℓ Λ t
  change U * (A * B) * V = (U * A * V) * (U * B * V)
  calc
    U * (A * B) * V = U * A * (V * U) * B * V := by rw [hVU]; simp [mul_assoc]
    _ = (U * A * V) * (U * B * V) := by simp [mul_assoc]

lemma exp_time_add (d ℓ : ℕ) (Λ : Finset (Site d)) (s t : ℝ) :
    NormedSpace.exp ((Complex.I * ((s + t : ℝ) : ℂ)) • hamiltonian d ℓ Λ) =
      NormedSpace.exp ((Complex.I * (s : ℂ)) • hamiltonian d ℓ Λ) *
      NormedSpace.exp ((Complex.I * (t : ℂ)) • hamiltonian d ℓ Λ) := by
  rw [Complex.ofReal_add, mul_add, add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl _).smul_left _ |>.smul_right _)

lemma exp_time_neg (d ℓ : ℕ) (Λ : Finset (Site d)) (t : ℝ) :
    NormedSpace.exp ((Complex.I * ((-t : ℝ) : ℂ)) • hamiltonian d ℓ Λ) =
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • hamiltonian d ℓ Λ) := by
  simp

theorem finiteDynamics_group (d ℓ : ℕ) (Λ : Finset (Site d)) (s t : ℝ) (A : QuasiLocal d ℓ) :
    finiteDynamics d ℓ Λ (s + t) A =
      finiteDynamics d ℓ Λ s (finiteDynamics d ℓ Λ t A) := by
  simp only [finiteDynamics, ← exp_time_neg, neg_add_rev, exp_time_add]
  simp only [mul_assoc]

@[simp] lemma translation_localUnit (d ℓ : ℕ) (x y : Site d) (a b : Level ℓ) :
    translation d ℓ x (localUnit d ℓ y a b) = localUnit d ℓ (x+y) a b := by
  apply Subtype.ext
  exact relabel_matrixUnit d ℓ (Equiv.addLeft x) y a b

lemma norm_translation (d ℓ : ℕ) (x : Site d) (A : QuasiLocal d ℓ) :
    ‖translation d ℓ x A‖ = ‖A‖ :=
  (StarAlgEquiv.isometry (operatorRelabel d ℓ (Equiv.addLeft x))).norm_map_of_map_zero
    (map_zero _) _

@[simp] lemma translation_spinZ (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinZ d ℓ y) = spinZ d ℓ (x+y) := by
  simp only [spinZ, map_sum, map_smul, translation_localUnit]
@[simp] lemma translation_spinPlus (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinPlus d ℓ y) = spinPlus d ℓ (x+y) := by
  simp only [spinPlus, map_sum, map_smul, translation_localUnit]
@[simp] lemma translation_spinMinus (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinMinus d ℓ y) = spinMinus d ℓ (x+y) := by
  simp only [spinMinus, map_star, translation_spinPlus]
@[simp] lemma translation_spinX (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinX d ℓ y) = spinX d ℓ (x+y) := by simp [spinX]
@[simp] lemma translation_spinY (d ℓ : ℕ) (x y : Site d) :
    translation d ℓ x (spinY d ℓ y) = spinY d ℓ (x+y) := by simp [spinY]

def bond (d ℓ : ℕ) (x y : Site d) : QuasiLocal d ℓ :=
  spinX d ℓ x * spinX d ℓ y + spinY d ℓ x * spinY d ℓ y + spinZ d ℓ x * spinZ d ℓ y

def bondBound (d ℓ : ℕ) : ℝ :=
  ‖spinX d ℓ 0‖^2 + ‖spinY d ℓ 0‖^2 + ‖spinZ d ℓ 0‖^2

lemma bondBound_nonneg (d ℓ : ℕ) : 0 ≤ bondBound d ℓ := by unfold bondBound; positivity

lemma norm_bond_le (d ℓ : ℕ) (x y : Site d) : ‖bond d ℓ x y‖ ≤ bondBound d ℓ := by
  have hX (x : Site d) : ‖spinX d ℓ x‖ = ‖spinX d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinX d ℓ 0)
  have hY (x : Site d) : ‖spinY d ℓ x‖ = ‖spinY d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinY d ℓ 0)
  have hZ (x : Site d) : ‖spinZ d ℓ x‖ = ‖spinZ d ℓ 0‖ := by
    simpa using norm_translation d ℓ x (spinZ d ℓ 0)
  calc
    ‖bond d ℓ x y‖ ≤ (‖spinX d ℓ x‖*‖spinX d ℓ y‖ +
        ‖spinY d ℓ x‖*‖spinY d ℓ y‖) + ‖spinZ d ℓ x‖*‖spinZ d ℓ y‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)))
        (norm_mul_le _ _))
    _ = bondBound d ℓ := by simp only [hX, hY, hZ, bondBound, pow_two]

lemma bond_mem_local {d ℓ : ℕ} {F : Set (Site d)} {x y : Site d}
    (hx : x ∈ F) (hy : y ∈ F) : bond d ℓ x y ∈ localAlgebra d ℓ F := by
  apply (localAlgebra d ℓ F).add_mem
  · exact (localAlgebra d ℓ F).add_mem
      ((localAlgebra d ℓ F).mul_mem (spinX_mem_localAlgebra d ℓ F hx)
        (spinX_mem_localAlgebra d ℓ F hy))
      ((localAlgebra d ℓ F).mul_mem (spinY_mem_localAlgebra d ℓ F hx)
        (spinY_mem_localAlgebra d ℓ F hy))
  · exact (localAlgebra d ℓ F).mul_mem (spinZ_mem_localAlgebra d ℓ F hx)
      (spinZ_mem_localAlgebra d ℓ F hy)

lemma localAlgebra_mono {d ℓ : ℕ} {F G : Set (Site d)} (h : F ⊆ G) :
    localAlgebra d ℓ F ≤ localAlgebra d ℓ G := by
  apply StarAlgebra.adjoin_mono
  rintro A ⟨x, hx, a, b, rfl⟩
  exact ⟨x, h hx, a, b, rfl⟩

end Heisenberg
end

end OAI
