import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert
import OAI.Analysis.IrrationalRotation.Rotation.RotationDiagonalState
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

def unitaryU : unitary (Hilbert →L[ℂ] Hilbert) := ⟨U, U_mem_unitary⟩

def unitaryV (θ : ℝ) : unitary (Hilbert →L[ℂ] Hilbert) :=
  ⟨V θ, V_mem_unitary θ⟩

def shiftUnitaryHom : Multiplicative ℤ →* unitary (Hilbert →L[ℂ] Hilbert) where
  toFun m := ⟨(WeightedShift.shift m.toAdd).toLinearIsometry.toContinuousLinearMap.compLpL
    2 circleMeasure, WeightedShift.fieldShift_mem_unitary m.toAdd⟩
  map_one' := Subtype.ext WeightedShift.fieldShift_zero
  map_mul' m n := Subtype.ext (WeightedShift.fieldShift_add m.toAdd n.toAdd)

theorem unitaryU_zpow (m : ℤ) :
    ((unitaryU ^ m : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) =
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure := by
  have h := map_zpow shiftUnitaryHom (Multiplicative.ofAdd (1 : ℤ)) m
  have hm : (Multiplicative.ofAdd (1 : ℤ)) ^ m = Multiplicative.ofAdd m := by
    change Multiplicative.ofAdd (m • (1 : ℤ)) = _
    simp
  rw [hm] at h
  exact congrArg Subtype.val h.symm

private theorem fourier_zero_map : (fourier 0 : C(Circle, ℂ)) = 1 := by
  ext x
  exact fourier_zero

private theorem fourier_add_map (m n : ℤ) :
    (fourier (m + n) : C(Circle, ℂ)) = fourier m * fourier n := by
  ext x
  exact fourier_add

def characterUnitaryHom (θ : ℝ) : Multiplicative ℤ →* unitary (Hilbert →L[ℂ] Hilbert) where
  toFun n := ⟨representation θ (fourier n.toAdd), by
    unfold representation
    apply WeightedShift.fieldDiagonal_mem_unitary
    exact Filter.Eventually.of_forall fun x k => Circle.norm_coe _⟩
  map_one' := Subtype.ext (by
    change representation θ (fourier 0) = 1
    rw [fourier_zero_map, representation_one])
  map_mul' m n := Subtype.ext (by
    change representation θ (fourier (m.toAdd + n.toAdd)) =
      representation θ (fourier m.toAdd) * representation θ (fourier n.toAdd)
    exact (congrArg (representation θ) (fourier_add_map m.toAdd n.toAdd)).trans
      (representation_mul θ (fourier m.toAdd) (fourier n.toAdd)))

theorem unitaryV_zpow (θ : ℝ) (n : ℤ) :
    ((unitaryV θ ^ n : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) =
      representation θ (fourier n) := by
  have h := map_zpow (characterUnitaryHom θ) (Multiplicative.ofAdd (1 : ℤ)) n
  have hn : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (n • (1 : ℤ)) = _
    simp
  rw [hn] at h
  exact congrArg Subtype.val h.symm

theorem vacuumFunctional_shift_representation (θ : ℝ) (m : ℤ) (a : C(Circle, ℂ)) :
    vacuumFunctional
      ((WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure *
        representation θ a) = if m = 0 then ∫ x, a x ∂circleMeasure else 0 := by
  by_cases hm : m = 0
  · subst m
    rw [WeightedShift.fieldShift_zero, one_mul, ite_eq_left rfl,
      vacuumFunctional_representation]
  · rw [ite_eq_right hm]
    change inner ℂ vacuum
      ((WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure
        (representation θ a vacuum)) = 0
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    have hv : vacuum =ᵐ[circleMeasure] fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) :=
      Lp.coeFn_const 2 circleMeasure _
    filter_upwards [hv, WeightedShift.fieldShift_ae m (representation θ a vacuum),
        representation_coordinates_ae θ a vacuum] with x hv hs ha
    rw [hv, hs, lp.inner_single_left]
    change inner ℂ (1 : ℂ) (representation θ a vacuum x (0 - m)) = 0
    rw [ha (0 - m), hv]
    simp [lp.single_apply, hm]

theorem shift_representation_vacuum_ae (θ : ℝ) (m : ℤ) (a : C(Circle, ℂ)) :
    ((WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure *
      representation θ a) vacuum =ᵐ[circleMeasure]
        fun x => a x • (lp.single 2 m (1 : ℂ) : Fiber) := by
  have hv : vacuum =ᵐ[circleMeasure] fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) :=
    Lp.coeFn_const 2 circleMeasure _
  filter_upwards [hv, WeightedShift.fieldShift_ae m (representation θ a vacuum),
      representation_coordinates_ae θ a vacuum] with x hv hs ha
  apply lp.ext
  funext k
  change ((WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 circleMeasure
    (representation θ a vacuum)) x k = a x * (lp.single 2 m (1 : ℂ) : Fiber) k
  rw [hs]
  change representation θ a vacuum x (k - m) = _
  rw [ha (k - m), hv]
  by_cases hkm : k = m
  · subst k
    simp [lp.single_apply, action]
  · have hsub : k - m ≠ 0 := sub_ne_zero.mpr hkm
    simp [lp.single_apply, hkm, hsub]

theorem unitary_zpow_mem_algebra (θ : ℝ)
    (W : unitary (Hilbert →L[ℂ] Hilbert)) (hW : (W : Hilbert →L[ℂ] Hilbert) ∈ algebra θ)
    (n : ℤ) : ((W ^ n : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) ∈ algebra θ := by
  cases n with
  | ofNat n =>
      simpa using (algebra θ).pow_mem hW n
  | negSucc n =>
      have hp : ((W : Hilbert →L[ℂ] Hilbert) ^ (n + 1)) ∈ algebra θ :=
        pow_mem hW (n + 1)
      simpa [zpow_negSucc, ← Unitary.star_eq_inv] using
        (star_mem hp : star ((W : Hilbert →L[ℂ] Hilbert) ^ (n + 1)) ∈ algebra θ)

theorem unitary_monomial_mem_algebra (θ : ℝ) (m n : ℤ) :
    (((unitaryU ^ m : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) *
      ((unitaryV θ ^ n : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert)) ∈
        algebra θ :=
  (algebra θ).mul_mem (unitary_zpow_mem_algebra θ unitaryU (U_mem_algebra θ) m)
    (unitary_zpow_mem_algebra θ (unitaryV θ) (V_mem_algebra θ) n)

theorem integral_fourier_circle (n : ℤ) :
    (∫ x : Circle, fourier n x ∂circleMeasure) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn]
    change (∫ x : Circle, fourier n x ∂volume) = 0
    exact integral_eq_zero_of_add_right_eq_neg (μ := volume)
      (fourier_add_half_inv_index hn (by norm_num))

theorem vacuumFunctional_unitary_zpowers (θ : ℝ) (m n : ℤ) :
    vacuumFunctional
      (((unitaryU ^ m : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) *
        ((unitaryV θ ^ n : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert)) =
      if m = 0 ∧ n = 0 then 1 else 0 := by
  rw [unitaryU_zpow, unitaryV_zpow, vacuumFunctional_shift_representation,
    integral_fourier_circle]
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]

def monomialVector (θ : ℝ) (mn : ℤ × ℤ) : Hilbert :=
  (((unitaryU ^ mn.1 * unitaryV θ ^ mn.2 : unitary (Hilbert →L[ℂ] Hilbert)) :
    Hilbert →L[ℂ] Hilbert)) vacuum

theorem monomialVector_ae (θ : ℝ) (mn : ℤ × ℤ) :
    monomialVector θ mn =ᵐ[circleMeasure]
      fun x => fourier mn.2 x • (lp.single 2 mn.1 (1 : ℂ) : Fiber) := by
  change (((unitaryU ^ mn.1 : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert) *
    ((unitaryV θ ^ mn.2 : unitary (Hilbert →L[ℂ] Hilbert)) : Hilbert →L[ℂ] Hilbert)) vacuum =ᵐ[_] _
  rw [unitaryU_zpow, unitaryV_zpow]
  exact shift_representation_vacuum_ae θ mn.1 (fourier mn.2)

theorem inner_monomialVector (θ : ℝ) (mn rs : ℤ × ℤ) :
    inner ℂ (monomialVector θ mn) (monomialVector θ rs) = if mn = rs then 1 else 0 := by
  rcases mn with ⟨m, n⟩
  rcases rs with ⟨r, s⟩
  rw [L2.inner_def]
  by_cases hmr : m = r
  · subst r
    have hpoint : (fun x => inner ℂ (monomialVector θ (m, n) x)
        (monomialVector θ (m, s) x)) =ᵐ[circleMeasure] fun x => fourier (s - n) x := by
      filter_upwards [monomialVector_ae θ (m, n), monomialVector_ae θ (m, s)] with x hn hs
      rw [hn, hs]
      have hi : inner ℂ (lp.single 2 m (1 : ℂ) : Fiber)
          (lp.single 2 m (1 : ℂ) : Fiber) = 1 := by
        rw [lp.inner_single_left]
        simp [lp.single_apply]
      rw [inner_smul_left, inner_smul_right, hi, mul_one]
      rw [← fourier_neg, mul_comm, ← fourier_add]
      rfl
    rw [integral_congr_ae hpoint, integral_fourier_circle]
    simp [sub_eq_zero, eq_comm]
  · rw [ite_eq_right (by simpa only [Prod.mk.injEq] using fun h => hmr h.1)]
    apply integral_eq_zero_of_ae
    filter_upwards [monomialVector_ae θ (m, n), monomialVector_ae θ (r, s)] with x hn hs
    rw [hn, hs, inner_smul_left, inner_smul_right, lp.inner_single_left]
    simp [lp.single_apply, hmr]

theorem orthonormal_monomialVector (θ : ℝ) : Orthonormal ℂ (monomialVector θ) := by
  rw [orthonormal_iff_ite]
  exact inner_monomialVector θ

end Invariant233.Rotation

end

end OAI
