import OAI.Analysis.Cotype.RademacherComparison
import OAI.Analysis.Cotype.FiniteL2Dual

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def rademacherL1Linear (m : ℕ) :
    PiLp 2 (fun _ : Fin m => X) →ₗ[ℝ] PiLp 1 (fun _ : Cube m => X) where
  toFun z := toLp 1 (rademacherSum X (fun i => z i))
  map_add' z w := by ext u; simp [rademacherSum, smul_add, Finset.sum_add_distrib]
  map_smul' c z := by ext u; simp [rademacherSum, Finset.smul_sum, smul_smul, mul_comm]

def momentL1Linear (m : ℕ) :
    PiLp 1 (fun _ : Cube m => X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X (fun u => f u))
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

@[simp] theorem momentL1_rademacherL1 (m : ℕ) (z : PiLp 2 (fun _ : Fin m => X)) :
    momentL1Linear m (rademacherL1Linear m z) = z := by
  ext i
  exact moment_rademacherSum X (fun i => z i) i

theorem rademacherL1_lower {m : ℕ} {D : ℝ} (hD : FixedCotypeBound X m D)
    (z : PiLp 2 (fun _ : Fin m => X)) :
    ‖z‖ ≤ (24 * D * (Fintype.card (Cube m) : ℝ)⁻¹) * ‖rademacherL1Linear m z‖ := by
  have h := (hD.2 (fun i => z i)).trans
    (mul_le_mul_of_nonneg_left (rademacher_L2_le_twentyfour_L1 (fun i => z i)) hD.1)
  rw [← PiLp.norm_eq_of_L2] at h
  simpa only [rademacherL1Linear, LinearMap.coe_mk, AddHom.coe_mk, PiLp.norm_eq_of_L1,
    ofLp_toLp, average, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

def singleL1Linear {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    X →ₗ[ℝ] PiLp 1 (fun _ : Ω => X) where
  toFun x := PiLp.single 1 a x
  map_add' x y := PiLp.single_add 1 a
  map_smul' c x := by ext b; simp [PiLp.single_apply, smul_ite]

def singleL1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    X →L[ℝ] PiLp 1 (fun _ : Ω => X) :=
  (singleL1Linear (X := X) a).mkContinuous 1
    (fun x => by simp [singleL1Linear, PiLp.norm_single])

@[simp] theorem singleL1_apply {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) (x : X) :
    singleL1 a x = PiLp.single 1 a x := rfl

theorem finiteL2Dual_tuple_unit_bound {m : ℕ} (y : Fin m → (X →L[ℝ] ℝ))
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖(toLp 2 y : PiLp 2 (fun _ : Fin m => (X →L[ℝ] ℝ)))‖ ≤ Real.sqrt m := by
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
      simpa using (sq_le_sq₀ (norm_nonneg (y i)) (by positivity)).mpr (hy i))
    _ = _ := by simp

theorem exists_dual_moment_lift_of_bound {m : ℕ} {D c : ℝ}
    (hD : FixedCotypeBound X m D) (hc : 0 ≤ c)
    (hsize : c * Real.sqrt m * (24 * D) ≤ 1)
    (y : Fin m → (X →L[ℝ] ℝ)) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ∃ Z : Cube m → (X →L[ℝ] ℝ), (∀ u, ‖Z u‖ ≤ 1) ∧
      ∀ i, moment (X →L[ℝ] ℝ) Z i = c • y i := by
  let V := rademacherL1Linear (X := X) m
  let p := V.range
  let F : p →ₗ[ℝ] ℝ := c • (finiteL2DualLinear y).comp ((momentL1Linear m).comp p.subtype)
  let C := c * Real.sqrt m * (24 * D) * (Fintype.card (Cube m) : ℝ)⁻¹
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))
    (mul_nonneg (by positivity) hD.1)) (by positivity)
  have hF (z : PiLp 2 (fun _ : Fin m => X)) (hz : V z ∈ p) :
      F ⟨V z, hz⟩ = c * finiteL2DualLinear y z := by
    change c • finiteL2DualLinear y (momentL1Linear m (rademacherL1Linear m z)) = _
    rw [momentL1_rademacherL1]
    rfl
  have hFbound (t : p) : ‖F t‖ ≤ C * ‖t‖ := by
    rcases t with ⟨_, z, rfl⟩
    erw [hF]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc]
    have hz := rademacherL1_lower hD z
    have hyz := (finiteL2DualLinear_bound y z).trans
      (mul_le_mul_of_nonneg_right (finiteL2Dual_tuple_unit_bound y hy) (norm_nonneg z))
    calc
      _ ≤ c * (Real.sqrt m * ‖z‖) := mul_le_mul_of_nonneg_left hyz hc
      _ ≤ c * (Real.sqrt m * ((24*D*(Fintype.card (Cube m) : ℝ)⁻¹) * ‖V z‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg _)) hc
      _ = _ := by dsimp [C]; ring
  let Fc := F.mkContinuous C hFbound
  obtain ⟨h, hext, hnorm⟩ := exists_extension_norm_eq p Fc
  have hn : ‖h‖ ≤ C := hnorm.le.trans (Fc.opNorm_le_bound hC hFbound)
  let Z : Cube m → (X →L[ℝ] ℝ) := fun u =>
    (Fintype.card (Cube m) : ℝ) • h.comp (singleL1 u)
  refine ⟨Z, ?_, ?_⟩
  · intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖(Fintype.card (Cube m) : ℝ) * h (singleL1 u x)‖ ≤ 1 * ‖x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    have hh := (h.le_opNorm (singleL1 u x)).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    simp only [singleL1_apply, PiLp.norm_single] at hh
    have hcard : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hcoeff : (Fintype.card (Cube m) : ℝ) * C ≤ 1 := by
      dsimp [C]
      convert hsize using 1
      field_simp
    exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)])
  · intro i
    ext x
    have hs : (∑ u : Cube m, sign (u i) • singleL1 u x) =
        V (PiLp.single 2 i x) := by
      ext v
      simp [singleL1_apply, PiLp.single_apply, V, rademacherL1Linear, rademacherSum, Pi.single_apply]
    have hh := hext ⟨V (PiLp.single 2 i x), ⟨PiLp.single 2 i x, rfl⟩⟩
    change h (V (PiLp.single 2 i x)) = F ⟨V (PiLp.single 2 i x), _⟩ at hh
    erw [hF] at hh
    have hcard : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    calc
      (moment (X →L[ℝ] ℝ) Z i) x = h (∑ u : Cube m, sign (u i) • singleL1 u x) := by
        simp only [moment, average, smul_apply, sum_apply, Z, ContinuousLinearMap.comp_apply,
          smul_eq_mul, map_sum, map_smul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        field_simp
      _ = c * y i x := by
        rw [hs, hh]
        simp [finiteL2DualLinear, PiLp.single_apply, apply_ite]
      _ = (c • y i) x := rfl

theorem exists_dual_moment_lift {m : ℕ} (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound X m D) (hDone : 1 ≤ D)
    (y : Fin m → (X →L[ℝ] ℝ)) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ∃ Z : Cube m → (X →L[ℝ] ℝ), (∀ u, ‖Z u‖ ≤ 1) ∧
      ∀ i, moment (X →L[ℝ] ℝ) Z i = (1 / (2 * 24 * D * Real.sqrt m)) • y i := by
  have hDp : 0 < D := lt_of_lt_of_le (by norm_num) hDone
  have hmp : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  apply exists_dual_moment_lift_of_bound hD (by positivity) _ y hy
  have he : (1 / (2 * 24 * D * Real.sqrt m)) * Real.sqrt m * (24 * D) = (1/2 : ℝ) := by
    field_simp
  rw [he]
  norm_num

end Cotype

end

end OAI
