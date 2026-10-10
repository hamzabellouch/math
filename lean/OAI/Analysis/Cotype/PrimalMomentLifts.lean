import OAI.Analysis.Cotype.DualMomentLifts
import OAI.Analysis.Cotype.FiniteSupDual
import OAI.Analysis.Cotype.QuotientLifts

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def singleL2Linear (a : Ω) : X →ₗ[ℝ] PiLp 2 (fun _ : Ω => X) where
  toFun x := PiLp.single 2 a x
  map_add' x y := PiLp.single_add 2 a
  map_smul' c x := by ext b; simp [PiLp.single_apply, smul_ite]

def singleL2 (a : Ω) : X →L[ℝ] PiLp 2 (fun _ : Ω => X) :=
  (singleL2Linear (X := X) a).mkContinuous 1
    (fun x => by simp [singleL2Linear, PiLp.norm_single])

@[simp] theorem singleL2_apply (a : Ω) (x : X) : singleL2 a x = PiLp.single 2 a x := rfl

def tupleDualCoordinates (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) : Ω → (X →L[ℝ] ℝ) :=
  fun i => ψ.comp (singleL2 i)

theorem tupleDual_eq (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ψ = finiteL2Dual (tupleDualCoordinates ψ) := by
  ext z
  have hs : (∑ i : Ω, PiLp.single 2 i (z i)) = z := by ext j; simp
  simp only [finiteL2Dual_apply, tupleDualCoordinates, ContinuousLinearMap.comp_apply, singleL2_apply]
  rw [← map_sum, hs]

def momentSupLinear (m : ℕ) : (Cube m → X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X f)
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

theorem moment_norm_le_sup {m : ℕ} (f : Cube m → X) (i : Fin m) :
    ‖moment X f i‖ ≤ ‖f‖ := by
  calc
    _ ≤ average (fun u => ‖sign (u i) • f u‖) := norm_average_le _
    _ ≤ average (fun _ : Cube m => ‖f‖) := average_mono (fun u => by
      have h := norm_le_pi_norm f u
      cases u i <;> simpa using h)
    _ = _ := by simp [average]

theorem momentSupLinear_bound (m : ℕ) (f : Cube m → X) :
    ‖momentSupLinear m f‖ ≤ Real.sqrt m * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  calc
    _ ≤ ∑ _ : Fin m, ‖f‖^2 := Finset.sum_le_sum (fun i _ =>
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (moment_norm_le_sup f i))
    _ = _ := by simp

def momentSup (m : ℕ) : (Cube m → X) →L[ℝ] PiLp 2 (fun _ : Fin m => X) :=
  (momentSupLinear (X := X) m).mkContinuous (Real.sqrt m) (momentSupLinear_bound m)

@[simp] theorem momentSup_apply (m : ℕ) (f : Cube m → X) (i : Fin m) :
    momentSup m f i = moment X f i := rfl

theorem momentSup_surjective (m : ℕ) : Function.Surjective (momentSup (X := X) m) := by
  intro z
  refine ⟨rademacherSum X (fun i => z i), ?_⟩
  ext i
  exact moment_rademacherSum X (fun i => z i) i

theorem momentSup_adjoint (m : ℕ) (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ψ.comp (momentSup m) = (Fintype.card (Cube m) : ℝ)⁻¹ •
      finiteSupDual (rademacherSum (X →L[ℝ] ℝ) (tupleDualCoordinates ψ)) := by
  ext f
  calc
    ψ (momentSup m f) = finiteL2Dual (tupleDualCoordinates ψ) (momentSup m f) :=
      congrArg (fun t : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ => t (momentSup m f)) (tupleDual_eq ψ)
    _ = _ := by
      simp only [finiteL2Dual_apply, momentSup_apply, moment, average, map_smul, map_sum,
        smul_apply, finiteSupDual_apply, rademacherSum, sum_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem momentSup_dual_bound {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D)
    (ψ : PiLp 2 (fun _ : Fin m => X) →L[ℝ] ℝ) :
    ‖ψ‖ ≤ (24*D) * ‖ψ.comp (momentSup m)‖ := by
  have hψ : ‖ψ‖ ≤ ‖(toLp 2 (tupleDualCoordinates ψ) : PiLp 2 (fun _ : Fin m => (X →L[ℝ] ℝ)))‖ := by
    calc
      _ = ‖finiteL2Dual (tupleDualCoordinates ψ)‖ := congrArg norm (tupleDual_eq ψ)
      _ ≤ _ := finiteL2Dual_norm_le _
  have h := (hD.2 (tupleDualCoordinates ψ)).trans
    (mul_le_mul_of_nonneg_left (rademacher_L2_le_twentyfour_L1 (tupleDualCoordinates ψ)) hD.1)
  rw [PiLp.norm_eq_of_L2] at hψ
  have hh := hψ.trans h
  rw [momentSup_adjoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (Cube m) : ℝ)⁻¹), finiteSupDual_norm]
  simpa only [average, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hh

theorem exists_primal_moment_lift [CompleteSpace X] {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (x : Fin m → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ P : Cube m → X, (∀ u, ‖P u‖ ≤ 1) ∧
      ∀ i, moment X P i = (1 / (2 * 24 * D * Real.sqrt m)) • x i := by
  have hDp : 0 < D := lt_of_lt_of_le (by norm_num) hDone
  have hmp : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  let a : ℝ := 1 / (2 * 24 * D * Real.sqrt m)
  have ha : 0 < a := by dsimp [a]; positivity
  let z : PiLp 2 (fun _ : Fin m => X) := a • toLp 2 x
  obtain ⟨P, hP, hn⟩ := quotient_lift_norm_le_two (momentSup (X := X) m)
    (momentSup_surjective m) (show 0 < 24*D by positivity) (momentSup_dual_bound hD) z
  have hxnorm : ‖(toLp 2 x : PiLp 2 (fun _ : Fin m => X))‖ ≤ Real.sqrt m := by
    rw [PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        simpa using (sq_le_sq₀ (norm_nonneg (x i)) (by positivity)).mpr (hx i))
      _ = _ := by simp
  have hz : ‖z‖ ≤ a * Real.sqrt m := by
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hxnorm ha.le
  have hcoeff : 2 * (24*D) * (a * Real.sqrt m) = 1 := by dsimp [a]; field_simp
  have hPn : ‖P‖ ≤ 1 := hn.trans ((mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq hcoeff)
  refine ⟨P, fun u => (norm_le_pi_norm P u).trans hPn, ?_⟩
  intro i
  exact congrArg (fun w : PiLp 2 (fun _ : Fin m => X) => w i) hP

end Cotype

end

end OAI
