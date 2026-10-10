import OAI.Analysis.Cotype.IndependentSigns
import OAI.Analysis.Cotype.TypeCotypeDuality

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem QuadraticTypeBound.one_le [Nontrivial X] {n : ℕ} (hn : 0 < n)
    {A : ℝ} (h : QuadraticTypeBound X n A) : 1 ≤ A := by
  classical
  obtain ⟨u,hu⟩ := exists_ne (0 : X)
  let v : X := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := by
    rw [show v = ‖u‖⁻¹ • u from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let i : Fin n := ⟨0,hn⟩
  let x : Fin n → X := fun j => if j = i then v else 0
  have hs : (∑ j, ‖x j‖^2) = 1 := by simp [x,apply_ite,hv]
  have hr (ε : Cube n) : ‖rademacherSum X x ε‖^2 = 1 := by
    simp only [rademacherSum,x,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    cases ε i <;> simp [hv]
  have hh := h x
  simpa only [cubeL2_sq,hr,average_const_value,hs,mul_one] using hh

theorem exists_type_extrapolation_parameters {n : ℕ} (hn : 1 < n) {A : ℝ}
    (hA : 0 ≤ A) (hAn : A < n) :
    ∃ p r : ℝ, 1 < p ∧ p ≤ 2 ∧ 1 < r ∧ r^p = n ∧
      0 ≤ Real.sqrt (A*n)*r⁻¹ ∧ Real.sqrt (A*n)*r⁻¹ < 1 := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsA : Real.sqrt (A*n) < n := by
    apply (Real.sqrt_lt' hn0).mpr
    nlinarith
  have hsn : Real.sqrt (n : ℝ) < n := by
    apply (Real.sqrt_lt' hn0).mpr
    nlinarith
  let t := max (Real.sqrt (A*n)) (Real.sqrt (n : ℝ))
  have ht : t < n := max_lt hsA hsn
  let r := (t+n)/2
  have htr : t < r := by dsimp [r]; linarith
  have hrn : r < n := by dsimp [r]; linarith
  have hsqr : Real.sqrt (n : ℝ) < r := (le_max_right _ _).trans_lt htr
  have hs1 : 1 < Real.sqrt (n : ℝ) := by
    exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hn1)
  have hr : 1 < r := hs1.trans hsqr
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hlog : Real.log r < Real.log n := Real.log_lt_log hr0 hrn
  have hnsq : (n : ℝ) < r^2 := by nlinarith [Real.sq_sqrt hn0.le,Real.sqrt_nonneg (n : ℝ)]
  have hlog2 : Real.log n < 2*Real.log r := by
    have hh := Real.log_lt_log hn0 hnsq
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  let p := Real.log n / Real.log r
  have hp : 1 < p := (one_lt_div hlr).mpr hlog
  have hp2 : p ≤ 2 := (div_le_iff₀ hlr).mpr hlog2.le
  have hrp : r^p = (n : ℝ) := by
    rw [Real.rpow_def_of_pos hr0]
    have he : Real.log r * p = Real.log n := by dsimp [p]; field_simp
    rw [he,Real.exp_log hn0]
  refine ⟨p,r,hp,hp2,hr,hrp,mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr hr0.le),?_⟩
  have hAr : Real.sqrt (A*n) < r := (le_max_left _ _).trans_lt htr
  exact (mul_inv_lt_iff₀ hr0).mpr (by simpa using hAr)

theorem hasType_of_normalized_bound {p D : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hD : 0 ≤ D)
    (h : ∀ (n : ℕ) (x : Fin n → X), (∑ i, ‖x i‖^p) ≤ 1 →
      cubeL2 X (rademacherSum X x) ≤ D) : HasType X p := by
  classical
  have hp0 : 0 < p := by linarith
  refine ⟨hp,hp2,D,hD,fun n x => ?_⟩
  let S : ℝ := ∑ i, ‖x i‖^p
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hz : S = 0
  · have hx : ∀ i, x i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Real.rpow_nonneg (norm_nonneg (x j)) p)
        (Finset.mem_univ i)
      change ‖x i‖^p ≤ S at hi
      rw [hz] at hi
      by_contra hxi
      have hh := Real.rpow_pos_of_pos (norm_pos_iff.mpr hxi) p
      linarith
    simp [hx,rademacherSum,cubeL2,average,Real.zero_rpow (ne_of_gt hp0) ]
    positivity
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  let r := S^(1/p)
  have hr : 0 < r := Real.rpow_pos_of_pos hS0 _
  have hrp : r^p = S := by
    dsimp [r]
    rw [← Real.rpow_mul hS,div_mul_cancel₀ 1 (ne_of_gt hp0),Real.rpow_one]
  let y : Fin n → X := fun i => r⁻¹ • x i
  have hy : (∑ i, ‖y i‖^p) = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hr.le),
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg _),← Finset.mul_sum]
    change (r⁻¹)^p*S = 1
    rw [Real.inv_rpow hr.le,hrp,inv_mul_cancel₀ hz]
  have he : rademacherSum X y = fun ε => r⁻¹ • rademacherSum X x ε := by
    funext ε
    simp only [y,rademacherSum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have hh := h n y hy.le
  rw [he,cubeL2_smul,abs_of_nonneg (inv_nonneg.mpr hr.le)] at hh
  have hh' := (inv_mul_le_iff₀ hr).mp hh
  simpa only [r,S,mul_comm] using hh'

end Cotype

end

end OAI
