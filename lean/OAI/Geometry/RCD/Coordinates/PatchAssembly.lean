import OAI.Geometry.RCD.Coordinates.MetricIteration
import OAI.Geometry.RCD.Coordinates.PatchJetBounds
import OAI.Geometry.RCD.Coordinates.PatchSecondDerivative

namespace OAI

/-!
# Patch fields as input to the analytic iteration

The frozen covector transformation sends the actual patch field to an
actual cutoff-affine patch field with conjugated positive operators.
The estimates here use only patch geometry and cutoff derivatives; no
coordinate iterate or estimate for its derivatives is an input.
-/

open Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace

noncomputable section

attribute [local instance] Classical.propDecidable

namespace RegularPointCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Exact affine displacement under the frozen dual transformation. -/
theorem frozenConjugate_normalized_displacement {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (D : E →L[ℝ] E) (x c z : E) :
    frozenConjugate T D (z - r⁻¹ • T (c - x)) =
      r⁻¹ • (T.symm : E →L[ℝ] E).adjoint (D (frozenSource r T x z - c)) := by
  have harg : T.symm (z - r⁻¹ • T (c - x)) =
      r⁻¹ • (frozenSource r T x z - c) := by
    simp only [map_sub, map_smul, ContinuousLinearEquiv.symm_apply_apply,
      frozenSource, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr, one_smul]
    module
  simp only [frozenConjugate, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    harg, map_smul]

/-- Frozen normalization is an exact identity between finite patch fields. -/
theorem normalizedCovector_patchField {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (x : E) (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) :
    normalizedCovector r T x (patchField s phi D c) =
      patchField s (fun j z => phi j (frozenSource r T x z))
        (fun j => frozenConjugate T (D j)) (fun j => r⁻¹ • T (c j - x)) := by
  funext z
  simp only [normalizedCovector, patchField, map_sum, Finset.smul_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [frozenConjugate_normalized_displacement hr]
  module

omit [CompleteSpace E] in
/-- A cutoff active after normalization was active at the original center.
Continuity alone gives the inclusion needed for an overlap bound. -/
theorem mem_tsupport_frozen_cutoff {r : ℝ} (T : E ≃L[ℝ] E) (x : E)
    (phi : E → ℝ) (hz : (0 : E) ∈ tsupport (fun z => phi (frozenSource r T x z))) :
    x ∈ tsupport phi := by
  have hs : Continuous (frozenSource r T x) := by unfold frozenSource; fun_prop
  have h := tsupport_comp_subset_preimage phi hs hz
  simpa [frozenSource] using h

omit [CompleteSpace E] in
/-- The number of active cutoffs does not increase under normalization. -/
theorem frozen_cutoff_active_card_le {r : ℝ} (T : E ≃L[ℝ] E) (x : E)
    (s : Finset ι) (phi : ι → E → ℝ) :
    (s.filter (fun j => (0 : E) ∈ tsupport (fun z => phi j (frozenSource r T x z)))).card ≤
      (s.filter (fun j => x ∈ tsupport (phi j))).card := by
  classical
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
    mem_tsupport_frozen_cutoff T x (phi j) (Finset.mem_filter.mp hj).2⟩

omit [CompleteSpace E] in
/-- Cutoff smoothness at the center transports through the frozen affine map. -/
theorem contDiffAt_frozen_cutoff {r : ℝ} (T : E ≃L[ℝ] E) (x : E)
    {phi : E → ℝ} {m : ℕ} (hphi : ContDiffAt ℝ m phi x) :
    ContDiffAt ℝ m (fun z => phi (frozenSource r T x z)) 0 := by
  have hp : ContDiffAt ℝ m phi (frozenSource r T x 0) := by
    simpa [frozenSource] using hphi
  apply hp.comp
  unfold frozenSource
  fun_prop

/-- Small displacement energy gives the normalized affine value bound.
The local energy budget `energy ≤ epsilon` is what makes this linear in
`epsilon`, including when the positive mass operator is degenerate. -/
theorem normalized_patch_displacement_le {r epsilon C energy : ℝ}
    (hr : 0 < r) (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (henergy : 0 ≤ energy) (hbudget : energy ≤ epsilon)
    (T : E ≃L[ℝ] E) (D : E →L[ℝ] E) (x c : E)
    (hD : D.IsPositive) (hsmall : ∀ y, ⟪y, D y⟫_ℝ ≤ epsilon * ‖T y‖ ^ 2)
    (hvalue : ⟪x - c, D (x - c)⟫_ℝ ≤ C * r ^ 2 * energy) :
    ‖frozenConjugate T D ((0 : E) - r⁻¹ • T (c - x))‖ ≤ epsilon * Real.sqrt C := by
  rw [frozenConjugate_normalized_displacement hr.ne']
  simp only [frozenSource, map_zero, smul_zero, add_zero, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  have hv := frozen_positive_form_value_le T hD hepsilon hC hr.le henergy hsmall (x - c) hvalue
  calc
    _ ≤ r⁻¹ * (Real.sqrt epsilon * Real.sqrt C * r * Real.sqrt energy) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)
    _ = Real.sqrt epsilon * Real.sqrt C * Real.sqrt energy := by field_simp
    _ ≤ Real.sqrt epsilon * Real.sqrt C * Real.sqrt epsilon :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbudget) (by positivity)
    _ = (Real.sqrt epsilon) ^ 2 * Real.sqrt C := by ring
    _ = _ := by rw [Real.sq_sqrt hepsilon]

/-- The factorial target weight absorbs the Gevrey-two cutoff weight. -/
theorem factorial_sq_le_majorant_scale (m : ℕ) :
    (m.factorial : ℝ) ^ 2 ≤ factorialMajorant m * (m.factorial : ℝ) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hf : (1 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)
  have hc : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 3 * (m.factorial : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm) hf
  calc
    _ = 1 * (m.factorial : ℝ) ^ 2 := by ring
    _ ≤ (((m : ℝ) + 1) ^ 3 * (m.factorial : ℝ)) * (m.factorial : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by unfold factorialMajorant; rw [Nat.factorial_succ]; push_cast; ring

/-- Actual normalized correction jets with a fixed base, independent of
order and of the full net size. Only active patches enter the estimate. -/
theorem normalized_patchField_jet_le
    (T : E ≃L[ℝ] E) (x : E) (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (m : ℕ)
    {r epsilon C energy L N F B : ℝ}
    (hr : 0 < r) (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (henergy : 0 ≤ energy) (hbudget : energy ≤ epsilon) (hL : 1 ≤ L)
    (hcard : ((s.filter (fun j => x ∈ tsupport (phi j))).card : ℝ) ≤ N)
    (hD : ∀ j ∈ s, x ∈ tsupport (phi j) → (D j).IsPositive)
    (hsmall : ∀ j ∈ s, x ∈ tsupport (phi j) → ∀ y,
      ⟪y, D j y⟫_ℝ ≤ epsilon * ‖T y‖ ^ 2)
    (hvalue : ∀ j ∈ s, x ∈ tsupport (phi j) →
      ⟪x - c j, D j (x - c j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x)
    (hcutoff : ∀ j ∈ s, x ∈ tsupport (phi j) → ∀ q ≤ m,
      ‖iteratedFDeriv ℝ q (fun z => phi j (frozenSource r T x z)) 0‖ ≤
        L ^ (q + 1) * (q.factorial : ℝ) ^ 2)
    (hF : patchJetBase N (Real.sqrt C) L ≤ F)
    (hB : patchJetBase N (Real.sqrt C) L ≤ B) :
    ‖iteratedFDeriv ℝ m (normalizedCovector r T x (patchField s phi D c)) 0‖ ≤
      epsilon * F * factorialMajorant m * jetCoefficientScale B m := by
  let J := patchJetBase N (Real.sqrt C) L
  have hJ : 1 ≤ J := patchJetBase_ge_one hL
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hB0 : 0 ≤ B := hJ0.trans hB
  have hF0 : 0 ≤ F := hJ0.trans hF
  have hactive : ∀ j ∈ s, (0 : E) ∈ tsupport (fun z => phi j (frozenSource r T x z)) →
      x ∈ tsupport (phi j) := fun j _ hj => mem_tsupport_frozen_cutoff T x (phi j) hj
  rw [normalizedCovector_patchField hr.ne']
  have hb := patchField_scaled_gevrey_two_active s
    (fun j z => phi j (frozenSource r T x z)) (fun j => frozenConjugate T (D j))
    (fun j => r⁻¹ • T (c j - x)) (0 : E) m
    (r := 1) hepsilon (by norm_num) (Real.sqrt_nonneg C) hL
    ((show ((s.filter (fun j => (0 : E) ∈
      tsupport (fun z => phi j (frozenSource r T x z)))).card : ℝ) ≤
        ((s.filter (fun j => x ∈ tsupport (phi j))).card : ℝ) by
          exact_mod_cast frozen_cutoff_active_card_le T x s phi).trans hcard)
    (fun j hj ha => frozen_positive_form_mixed_opNorm_le T (hD j hj (hactive j hj ha))
      hepsilon (hsmall j hj (hactive j hj ha)))
    (fun j hj ha => by
      simpa using normalized_patch_displacement_le hr hepsilon hC henergy hbudget T (D j) x (c j)
        (hD j hj (hactive j hj ha)) (hsmall j hj (hactive j hj ha)) (hvalue j hj (hactive j hj ha)))
    (fun j hj => contDiffAt_frozen_cutoff T x (hphi j hj))
    (fun j hj ha q hq => by simpa using hcutoff j hj (hactive j hj ha) q hq)
  simp only [one_pow, one_mul, mul_one] at hb
  calc
    _ ≤ epsilon * J ^ (m + 1) * (m.factorial : ℝ) ^ 2 := hb
    _ = epsilon * (J * J ^ m) * (m.factorial : ℝ) ^ 2 := by rw [pow_succ]; ring
    _ ≤ epsilon * (F * B ^ m) * (factorialMajorant m * (m.factorial : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul hF (pow_le_pow_left₀ hJ0 hB m) (by positivity) hF0) hepsilon
      · exact factorial_sq_le_majorant_scale m
      · positivity
      · positivity
    _ = _ := by unfold jetCoefficientScale; ring

omit [CompleteSpace E] in
/-- Local smoothness of the full finite patch field. -/
theorem contDiffAt_patchField (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) {m : ℕ}
    (hphi : ∀ j ∈ s, ContDiffAt ℝ m (phi j) x) :
    ContDiffAt ℝ m (patchField s phi D c) x := by
  apply ContDiffAt.sum
  intro j hj
  exact (hphi j hj).smul ((D j).contDiff.contDiffAt.comp x
    (contDiffAt_id.sub contDiffAt_const))

omit [CompleteSpace E] in
/-- At the testing point the field is the sum over active patches. -/
theorem patchField_eq_active_at (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x : E) :
    patchField s phi D c x =
      patchField (s.filter (fun j => x ∈ tsupport (phi j))) phi D c x := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hz : phi j x = 0 := image_eq_zero_of_notMem_tsupport
    (fun hx => hnot (Finset.mem_filter.mpr ⟨hj, hx⟩))
  simp [hz]

omit [CompleteSpace E] in
/-- The first derivative also restricts to active patches. -/
theorem fderiv_patchField_eq_active_at (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x xi : E)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 1 (phi j) x) :
    fderiv ℝ (patchField s phi D c) x xi =
      fderiv ℝ (patchField (s.filter (fun j => x ∈ tsupport (phi j))) phi D c) x xi := by
  have h := congrArg (fun A => A (fun _ => xi))
    (iteratedFDeriv_patchField_eq_active s phi D c x 1 hphi)
  simpa only [iteratedFDeriv_one_apply] using h

omit [CompleteSpace E] in
/-- The actual second directional derivative restricts to active patches. -/
theorem diagonalSecond_patchField_eq_active_at (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x xi : E)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 2 (phi j) x) :
    diagonalSecond (patchField s phi D c) x xi =
      diagonalSecond (patchField (s.filter (fun j => x ∈ tsupport (phi j))) phi D c) x xi := by
  rw [diagonalSecond_eq (contDiffAt_patchField s phi D c x hphi),
    diagonalSecond_eq (contDiffAt_patchField _ phi D c x
      (fun j hj => hphi j (Finset.mem_filter.mp hj).1)),
    iteratedFDeriv_patchField_eq_active s phi D c x 2 hphi]

/-- All four directional hypotheses of the analytic iteration follow
from the actual finite patches, with one common coefficient. -/
theorem patchField_directional_bounds
    (T : E ≃L[ℝ] E) (s : Finset ι) (phi : ι → E → ℝ)
    (D : ι → E →L[ℝ] E) (c : ι → E) (x xi : E) {N : ℕ}
    {epsilon C K r energy F : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hr : 0 < r) (henergy : 0 ≤ energy)
    (hcard : (s.filter (fun j => x ∈ tsupport (phi j))).card ≤ N)
    (hphi : ∀ j ∈ s, ContDiffAt ℝ 2 (phi j) x)
    (hD : ∀ j ∈ s, x ∈ tsupport (phi j) → (D j).IsPositive)
    (hphi0 : ∀ j ∈ s, x ∈ tsupport (phi j) → 0 ≤ phi j x)
    (hphi1 : ∀ j ∈ s, x ∈ tsupport (phi j) → phi j x ≤ 1)
    (hZ : ∀ y, ⟪y, patchMass (s.filter (fun j => x ∈ tsupport (phi j))) D y⟫_ℝ ≤
      epsilon * ‖T y‖ ^ 2)
    (hw : ∀ j ∈ s, x ∈ tsupport (phi j) →
      ⟪x - c j, D j (x - c j)⟫_ℝ ≤ C * r ^ 2 * energy)
    (hfirst : ∀ j ∈ s, x ∈ tsupport (phi j) → |fderiv ℝ (phi j) x xi| ≤ K / r * ‖T xi‖)
    (hsecond : ∀ j ∈ s, x ∈ tsupport (phi j) →
      |diagonalSecond (phi j) x xi| ≤ K / r ^ 2 * ‖T xi‖ ^ 2)
    (hF1 : 1 ≤ F) (hFvalue : (N : ℝ) * Real.sqrt C ≤ F)
    (hFerror : (N : ℝ) * K * Real.sqrt C ≤ F)
    (hFsecond : 2 * K * Real.sqrt (N : ℝ) ≤ F)
    (hFlinear : K * Real.sqrt ((N : ℝ) * C) ≤ F) :
    let active := s.filter (fun j => x ∈ tsupport (phi j))
    let Z := ⟪xi, patchMass active D xi⟫_ℝ
    let S := patchPrincipal active (fun j => phi j x) D
    ‖(T.symm : E →L[ℝ] E).adjoint (patchField s phi D c x)‖ ≤
        F * Real.sqrt epsilon * r * Real.sqrt energy ∧
    ‖(T.symm : E →L[ℝ] E).adjoint (fderiv ℝ (patchField s phi D c) x xi)‖ ≤
        F * Real.sqrt epsilon * (Real.sqrt Z + Real.sqrt energy * ‖T xi‖) ∧
    ‖(T.symm : E →L[ℝ] E).adjoint (diagonalSecond (patchField s phi D c) x xi)‖ ≤
        F / r * (Real.sqrt Z * ‖T xi‖ + Real.sqrt energy * ‖T xi‖ ^ 2) ∧
    |⟪xi, fderiv ℝ (patchField s phi D c) x xi - S xi⟫_ℝ| ≤
        F * Real.sqrt Z * Real.sqrt energy * ‖T xi‖ := by
  let active := s.filter (fun j => x ∈ tsupport (phi j))
  have hd : ∀ j ∈ active, (D j).IsPositive :=
    fun j hj => hD j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hp : ∀ j ∈ active, ContDiffAt ℝ 2 (phi j) x :=
    fun j hj => hphi j (Finset.mem_filter.mp hj).1
  have hp0 : ∀ j ∈ active, 0 ≤ phi j x :=
    fun j hj => hphi0 j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hp1 : ∀ j ∈ active, phi j x ≤ 1 :=
    fun j hj => hphi1 j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hsmall : ∀ j ∈ active, ∀ y, ⟪y, D j y⟫_ℝ ≤ epsilon * ‖T y‖ ^ 2 :=
    fun j hj y => (patch_form_le_mass active D hd hj y).trans (hZ y)
  have hv : ∀ j ∈ active, ⟪x - c j, D j (x - c j)⟫_ℝ ≤ C * r ^ 2 * energy :=
    fun j hj => hw j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hdf : ∀ j ∈ active, |fderiv ℝ (phi j) x xi| ≤ K / r * ‖T xi‖ :=
    fun j hj => hfirst j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hd2 : ∀ j ∈ active, |diagonalSecond (phi j) x xi| ≤ K / r ^ 2 * ‖T xi‖ ^ 2 :=
    fun j hj => hsecond j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have heq := fderiv_patchField_eq_active_at s phi D c x xi
    (fun j hj => (hphi j hj).of_le (by norm_num))
  have hdecomp := fderiv_patchField_apply active phi (fun j => fderiv ℝ (phi j) x) D c x xi
    (fun j hj => (hp j hj).differentiableAt (by norm_num) |>.hasFDerivAt)
  change fderiv ℝ (patchField s phi D c) x xi = _ at heq
  have hvb := patchField_frozen_value_le T active phi D c x hcard hepsilon hC hr henergy hd
    hsmall hv (fun j hj => abs_le.mpr ⟨by linarith [hp0 j hj], hp1 j hj⟩)
  have hpb := patchPrincipal_frozen_norm_le T active (fun j => phi j x) D hepsilon hd hp0 hp1 hZ xi
  have heb := patchCutoffError_frozen_norm_le T active D (fun j => x - c j)
    (fun j => fderiv ℝ (phi j) x xi) xi hcard hepsilon hC hK hr henergy hd hsmall hv hdf
  have hs2 := patchField_second_directional_frozen_le T active phi D c x xi hcard hepsilon
    hepsilon1 hC hK hr henergy hp hd hZ hv hdf hd2
  have hl := patchCutoffError_diagonal_le T active D (fun j => x - c j)
    (fun j => fderiv ℝ (phi j) x xi) xi hcard hC hK hr henergy hd hv hdf
  dsimp only
  constructor
  · rw [patchField_eq_active_at s phi D c x]
    have hraw := (div_le_iff₀ hr).1 hvb
    have hcoeff := mul_le_mul_of_nonneg_right hFvalue
      (by positivity : 0 ≤ Real.sqrt epsilon * r * Real.sqrt energy)
    exact hraw.trans (by nlinarith [hcoeff])
  constructor
  · rw [heq, hdecomp, map_add]
    refine (norm_add_le _ _).trans ((add_le_add hpb heb).trans ?_)
    calc
      _ = (1 : ℝ) * (Real.sqrt epsilon * Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ) +
          ((N : ℝ) * K * Real.sqrt C) * (Real.sqrt epsilon * Real.sqrt energy * ‖T xi‖) := by ring
      _ ≤ F * (Real.sqrt epsilon * Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ) +
          F * (Real.sqrt epsilon * Real.sqrt energy * ‖T xi‖) :=
        add_le_add (mul_le_mul_of_nonneg_right hF1 (by positivity))
          (mul_le_mul_of_nonneg_right hFerror (by positivity))
      _ = _ := by ring
  constructor
  · rw [diagonalSecond_patchField_eq_active_at s phi D c x xi hphi]
    have hb : (N : ℝ) * K * Real.sqrt C * Real.sqrt energy * ‖T xi‖ ^ 2 +
        2 * K * Real.sqrt (N : ℝ) * Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ * ‖T xi‖ ≤
        F * (Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ * ‖T xi‖ + Real.sqrt energy * ‖T xi‖ ^ 2) := by
      have hcoeff1 := mul_le_mul_of_nonneg_right hFerror
        (by positivity : 0 ≤ Real.sqrt energy * ‖T xi‖ ^ 2)
      have hcoeff2 := mul_le_mul_of_nonneg_right hFsecond
        (by positivity : 0 ≤ Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ * ‖T xi‖)
      nlinarith [hcoeff1, hcoeff2]
    calc
      _ ≤ F * (Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ * ‖T xi‖ +
          Real.sqrt energy * ‖T xi‖ ^ 2) / r :=
        (le_div_iff₀ hr).2 (by simpa only [diagonalSecond, active, mul_comm] using hs2.trans hb)
      _ = _ := by ring
  · rw [heq, hdecomp, add_sub_cancel_left]
    have hcoeff := mul_le_mul_of_nonneg_right hFlinear
      (by positivity : 0 ≤ Real.sqrt ⟪xi, patchMass active D xi⟫_ℝ * Real.sqrt energy * ‖T xi‖)
    exact hl.trans (by nlinarith [hcoeff])

/-- Only cutoffs whose closed support contains the point are active. -/
def activePatches (s : Finset ι) (phi : ι → E → ℝ) (x : E) : Finset ι :=
  s.filter (fun j => x ∈ tsupport (phi j))

/-- Geometric patch data before the coordinate iteration. The assumptions
are on cutoffs, positive mass operators, displacement energies and their
cumulative budgets; no estimate on the resulting field is assumed. -/
structure PatchIterationGeometry (Ω : Set E) (r0 Theta epsilon : ℝ)
    (N : ℕ) (C K L : ℝ) where
  patches : ℕ → Finset ι
  cutoff : ℕ → ι → E → ℝ
  operator : ℕ → ι → E →L[ℝ] E
  center : ℕ → ι → E
  frozen : ℕ → E → E ≃L[ℝ] E
  energy : ℕ → E → ℝ
  frozen_mono : ∀ i x, x ∈ Ω → ∀ xi, ‖frozen i x xi‖ ≤ ‖frozen (i + 1) x xi‖
  cutoff_smooth : ∀ i j, j ∈ patches i → ∀ x ∈ Ω, ∀ m : ℕ, ContDiffAt ℝ m (cutoff i j) x
  active_card : ∀ i x, x ∈ Ω → (activePatches (patches i) (cutoff i) x).card ≤ N
  energy_nonneg : ∀ i x, x ∈ Ω → 0 ≤ energy i x
  energy_budget : ∀ k x, x ∈ Ω → (∑ i ∈ Finset.range k, energy i x) ≤ epsilon
  operator_positive : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → (operator i j).IsPositive
  cutoff_nonneg : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → 0 ≤ cutoff i j x
  cutoff_le_one : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → cutoff i j x ≤ 1
  mass_small : ∀ i x, x ∈ Ω → ∀ xi,
    ⟪xi, patchMass (activePatches (patches i) (cutoff i) x) (operator i) xi⟫_ℝ ≤
      epsilon * ‖frozen i x xi‖ ^ 2
  center_energy : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) →
    ⟪x - center i j, operator i j (x - center i j)⟫_ℝ ≤
      C * (iterationRadius r0 i) ^ 2 * energy i x
  cutoff_first : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → ∀ xi,
    |fderiv ℝ (cutoff i j) x xi| ≤ K / iterationRadius r0 i * ‖frozen i x xi‖
  cutoff_second : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → ∀ xi,
    |diagonalSecond (cutoff i j) x xi| ≤
      K / (iterationRadius r0 i) ^ 2 * ‖frozen i x xi‖ ^ 2
  cutoff_jets : ∀ i j, j ∈ patches i → ∀ x ∈ Ω,
    x ∈ tsupport (cutoff i j) → ∀ m,
    ‖iteratedFDeriv ℝ m
      (fun z => cutoff i j (frozenSource (iterationRadius r0 i) (frozen i x) x z)) 0‖ ≤
        L ^ (m + 1) * (m.factorial : ℝ) ^ 2
  mass_budget : ∀ k x, x ∈ Ω → ∀ xi,
    ‖xi‖ ^ 2 + (∑ i ∈ Finset.range k,
      ⟪xi, patchMass (activePatches (patches i) (cutoff i) x) (operator i) xi⟫_ℝ) ≤
        Theta * ‖frozen k x xi‖ ^ 2
  principal_budget : ∀ k x, x ∈ Ω → ∀ xi,
    ‖frozen k x xi‖ ^ 2 ≤ Theta * (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k,
      ⟪xi, patchPrincipal (activePatches (patches i) (cutoff i) x)
        (fun j => cutoff i j x) (operator i) xi⟫_ℝ)

/-- One explicit coefficient covers all directional and higher-jet
bounds of the finite patch field. -/
def patchAssemblyCoefficient (N : ℕ) (C K L : ℝ) : ℝ :=
  1 + patchJetBase N (Real.sqrt C) L + (N : ℝ) * Real.sqrt C +
    (N : ℝ) * K * Real.sqrt C + 2 * K * Real.sqrt (N : ℝ) +
    K * Real.sqrt ((N : ℝ) * C)

theorem patchAssemblyCoefficient_bounds (N : ℕ) {C K L : ℝ}
    (hK : 0 ≤ K) (hL : 1 ≤ L) :
    1 ≤ patchAssemblyCoefficient N C K L ∧
    patchJetBase N (Real.sqrt C) L ≤ patchAssemblyCoefficient N C K L ∧
    (N : ℝ) * Real.sqrt C ≤ patchAssemblyCoefficient N C K L ∧
    (N : ℝ) * K * Real.sqrt C ≤ patchAssemblyCoefficient N C K L ∧
    2 * K * Real.sqrt (N : ℝ) ≤ patchAssemblyCoefficient N C K L ∧
    K * Real.sqrt ((N : ℝ) * C) ≤ patchAssemblyCoefficient N C K L := by
  have h0 : 0 ≤ patchJetBase N (Real.sqrt C) L :=
    zero_le_one.trans (patchJetBase_ge_one hL)
  have h1 : 0 ≤ (N : ℝ) * Real.sqrt C := by positivity
  have h2 : 0 ≤ (N : ℝ) * K * Real.sqrt C := by positivity
  have h3 : 0 ≤ 2 * K * Real.sqrt (N : ℝ) := by positivity
  have h4 : 0 ≤ K * Real.sqrt ((N : ℝ) * C) := by positivity
  unfold patchAssemblyCoefficient
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

namespace PatchIterationGeometry

variable {Ω : Set E} {r0 Theta epsilon C K L : ℝ} {N : ℕ}

omit [CompleteSpace E] in
/-- An individual nonnegative defect is bounded by the cumulative budget. -/
theorem energy_le (p : PatchIterationGeometry (ι := ι) Ω r0 Theta epsilon N C K L)
    (i : ℕ) (x : E) (hx : x ∈ Ω) : p.energy i x ≤ epsilon := by
  have hi : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (Nat.lt_succ_self i)
  exact (Finset.single_le_sum (fun j _ => p.energy_nonneg j x hx) hi).trans
    (p.energy_budget (i + 1) x hx)

/-- Assemble the analytic iteration inputs from genuine finite patch
fields. The four field bounds and every correction jet are conclusions
of the patch calculus, rather than fields of the geometric input. -/
def toAnalyticIterationData
    (p : PatchIterationGeometry (ι := ι) Ω r0 Theta epsilon N C K L)
    (hr0 : 0 < r0) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 1 ≤ L) {F B : ℝ}
    (hF1 : 1 ≤ F) (hFvalue : (N : ℝ) * Real.sqrt C ≤ F)
    (hFerror : (N : ℝ) * K * Real.sqrt C ≤ F)
    (hFsecond : 2 * K * Real.sqrt (N : ℝ) ≤ F)
    (hFlinear : K * Real.sqrt ((N : ℝ) * C) ≤ F)
    (hFjet : patchJetBase N (Real.sqrt C) L ≤ F)
    (hB : patchJetBase N (Real.sqrt C) L ≤ B) :
    AnalyticIterationData Ω r0 Theta F B epsilon := by
  have hd (i : ℕ) (x : E) (hx : x ∈ Ω) :
      ∀ j ∈ activePatches (p.patches i) (p.cutoff i) x, (p.operator i j).IsPositive := by
    intro j hj
    exact p.operator_positive i j (Finset.mem_filter.mp hj).1 x hx (Finset.mem_filter.mp hj).2
  have hb (i : ℕ) (x : E) (hx : x ∈ Ω) (xi : E) :=
    patchField_directional_bounds (p.frozen i x) (p.patches i) (p.cutoff i) (p.operator i)
      (p.center i) x xi hepsilon hepsilon1 hC hK (iterationRadius_pos hr0 i)
      (p.energy_nonneg i x hx) (p.active_card i x hx)
      (fun j hj => p.cutoff_smooth i j hj x hx 2)
      (fun j hj ha => p.operator_positive i j hj x hx ha)
      (fun j hj ha => p.cutoff_nonneg i j hj x hx ha)
      (fun j hj ha => p.cutoff_le_one i j hj x hx ha) (p.mass_small i x hx)
      (fun j hj ha => p.center_energy i j hj x hx ha)
      (fun j hj ha => p.cutoff_first i j hj x hx ha xi)
      (fun j hj ha => p.cutoff_second i j hj x hx ha xi)
      hF1 hFvalue hFerror hFsecond hFlinear
  refine {
    frozen := p.frozen
    correction := fun i => patchField (p.patches i) (p.cutoff i) (p.operator i) (p.center i)
    principal := fun i x => patchPrincipal (activePatches (p.patches i) (p.cutoff i) x)
      (fun j => p.cutoff i j x) (p.operator i)
    mass := fun i x => patchMass (activePatches (p.patches i) (p.cutoff i) x) (p.operator i)
    energy := p.energy
    frozen_mono := p.frozen_mono
    correction_smooth := fun i x hx m => contDiffAt_patchField _ _ _ _ _
      (fun j hj => p.cutoff_smooth i j hj x hx m)
    energy_nonneg := p.energy_nonneg
    energy_budget := p.energy_budget
    mass_nonneg := fun i x hx xi => (patchMass_isPositive _ _ (hd i x hx)).inner_nonneg_right xi
    principal_nonneg := ?_
    principal_le_mass := ?_
    mass_budget := p.mass_budget
    principal_budget := p.principal_budget
    value_bound := fun i x hx => (hb i x hx 0).1
    first_bound := fun i x hx xi => (hb i x hx xi).2.1
    second_bound := fun i x hx xi => (hb i x hx xi).2.2.1
    linear_bound := fun i x hx xi => (hb i x hx xi).2.2.2
    correction_jets := ?_ }
  · intro i x hx xi
    exact (patch_principal_isPositive _ _ _
      (fun j hj => p.cutoff_nonneg i j (Finset.mem_filter.mp hj).1 x hx (Finset.mem_filter.mp hj).2)
      (hd i x hx)).inner_nonneg_right xi
  · intro i x hx xi
    exact patchPrincipal_form_le_mass _ _ _ (hd i x hx)
      (fun j hj => p.cutoff_le_one i j (Finset.mem_filter.mp hj).1 x hx (Finset.mem_filter.mp hj).2) xi
  · intro i x hx m
    apply normalized_patchField_jet_le (N := (N : ℝ)) (p.frozen i x) x (p.patches i) (p.cutoff i)
      (p.operator i) (p.center i) m (iterationRadius_pos hr0 i) hepsilon hC
      (p.energy_nonneg i x hx) (p.energy_le i x hx) hL
      (by exact_mod_cast p.active_card i x hx)
      (fun j hj ha => p.operator_positive i j hj x hx ha)
    · intro j hj ha xi
      exact (patch_form_le_mass _ _ (hd i x hx) (Finset.mem_filter.mpr ⟨hj, ha⟩) xi).trans
        (p.mass_small i x hx xi)
    · exact fun j hj ha => p.center_energy i j hj x hx ha
    · exact fun j hj => p.cutoff_smooth i j hj x hx m
    · exact fun j hj ha q _ => p.cutoff_jets i j hj x hx ha q
    · exact hFjet
    · exact hB

/-- The explicit patch constants supply a canonical field coefficient
and jet base, with no dependence on a coordinate iterate. -/
def toCanonicalAnalyticIterationData
    (p : PatchIterationGeometry (ι := ι) Ω r0 Theta epsilon N C K L)
    (hr0 : 0 < r0) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 1 ≤ L) :
    AnalyticIterationData Ω r0 Theta (patchAssemblyCoefficient N C K L)
      (patchJetBase N (Real.sqrt C) L) epsilon := by
  have hb := patchAssemblyCoefficient_bounds N (C := C) hK hL
  exact p.toAnalyticIterationData hr0 hepsilon hepsilon1 hC hK hL
    hb.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2 hb.2.1 le_rfl

end PatchIterationGeometry

/-- Geometric patches and cumulative budgets supply the field estimates and
correction jets for the finite analytic iteration. -/
theorem exists_patch_metric_iteration [FiniteDimensional ℝ E]
    (N : ℕ) {Theta C K L : ℝ} (hTheta : 1 ≤ Theta)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 1 ≤ L) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (Ω : Set E), IsOpen Ω → ∀ (r0 : ℝ), 0 < r0 →
      ∀ p : PatchIterationGeometry (ι := ι) Ω r0 Theta epsilon N C K L,
      let v := fun i => patchField (p.patches i) (p.cutoff i) (p.operator i) (p.center i)
      ∀ k x, x ∈ Ω →
        (∀ m : ℕ, ContDiffAt ℝ m (metricIterate v k) x) ∧
        (∀ xi, (4 * Theta)⁻¹ * ‖p.frozen k x xi‖ ^ 2 ≤ ‖fderiv ℝ (metricIterate v k) x xi‖ ^ 2 ∧
          ‖fderiv ℝ (metricIterate v k) x xi‖ ^ 2 ≤ (4 * Theta) * ‖p.frozen k x xi‖ ^ 2) ∧
        (∀ m, 2 ≤ m →
          ‖iteratedFDeriv ℝ m (normalizedCoordinates (iterationRadius r0 k)
            (p.frozen k x) x (metricIterate v k)) 0‖ ≤
              (patchJetBase N (Real.sqrt C) L) ^ (m - 1) * (m.factorial : ℝ) ^ 3) := by
  have hF := (patchAssemblyCoefficient_bounds N (C := C) hK hL).1
  have hB : 1 ≤ patchJetBase (N : ℝ) (Real.sqrt C) L := patchJetBase_ge_one hL
  obtain ⟨epsilon, hepsilon, he1, hmain⟩ := exists_analytic_metric_iteration (E := E) hTheta hF hB
  refine ⟨epsilon, hepsilon, he1, ?_⟩
  intro Ω hΩ r0 hr0 p
  dsimp only
  intro k x hx
  exact hmain Ω hΩ r0 hr0 (p.toCanonicalAnalyticIterationData hr0 hepsilon.le he1 hC hK hL) k x hx

end RegularPointCoordinates

end

end OAI
