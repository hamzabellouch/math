import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CountertermProgram

namespace OAI

/-! The actual scalar direct-interaction offset is one half of the
ordered off-diagonal Coulomb sum. The finite list evaluator excludes only
identical coordinates; injectivity identifies that test with the diagonal. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CoulombPairSum

abbrev Point := ℚ×ℚ
abbrev Input := ℕ×List Point

def offsite (rho p : ℕ) (a b : Point) : ℚ :=
  if CoulombPairEvaluation.squaredDistance a b = 0 then 0
  else CoulombPairEvaluation.approximate rho p a b

def row (rho p : ℕ) (a : Point) (sites : List Point) : ℚ :=
  (sites.map (offsite rho p a)).sum

def total (rho p : ℕ) (sites : List Point) : ℚ :=
  (sites.map (fun a => row rho p a sites)).sum/2

def exactTotal (freq : ℝ) {m : ℕ} (u : Fin m → Point) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, if i=j then 0 else
    localizedCoulombCoeff freq (PlanarForcingProgram.position (u i))
      (PlanarForcingProgram.position (u j))

theorem row_error (rho p : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → Point) (hu : Function.Injective u) (i : Fin m) :
    |(row rho p (u i) (List.ofFn u):ℝ)-
      ∑ j, if i=j then 0 else localizedCoulombCoeff (GaussianFrequency.frequency rho)
        (PlanarForcingProgram.position (u i)) (PlanarForcingProgram.position (u j))| ≤
      (m:ℝ)/(p+1:ℝ) := by
  simp only [row,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Rat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j : Fin m, 1/(p+1:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i=j
      · subst j
        simp only [offsite,CountertermEvaluation.squaredDistance_eq_zero,ite_true,
          Rat.cast_zero,sub_self,abs_zero]
        positivity
      · have hij : u i ≠ u j := fun he => h (hu he)
        simpa only [offsite,CountertermEvaluation.squaredDistance_eq_zero,
          ite_eq_right hij,ite_eq_right h,one_div] using
          CoulombPairEvaluation.approximation_error rho p hrho (u i) (u j)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem total_error (rho p : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → Point) (hu : Function.Injective u) :
    |(total rho p (List.ofFn u):ℝ)-exactTotal (GaussianFrequency.frequency rho) u| ≤
      (m:ℝ)^2/(2*(p+1:ℝ)) := by
  have he : (total rho p (List.ofFn u):ℝ)-exactTotal (GaussianFrequency.frequency rho) u =
      (∑ i, ((row rho p (u i) (List.ofFn u):ℝ)-
        ∑ j, if i=j then 0 else localizedCoulombCoeff (GaussianFrequency.frequency rho)
          (PlanarForcingProgram.position (u i)) (PlanarForcingProgram.position (u j))))/2 := by
    simp only [total,exactTotal,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
      Rat.cast_div,Rat.cast_sum,Rat.cast_ofNat,Finset.sum_sub_distrib]
    ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => row_error rho p hrho u hu i))
  apply (div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 2)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hp : (p:ℝ)+1 ≠ 0 := by positivity
  field_simp [hp]

def precision (m P : ℕ) : ℕ := (m+1)^2*(P+1)
def value (rho : ℕ) (x : Input) : ℚ := total rho (precision x.2.length x.1) x.2

theorem precision_budget (m P : ℕ) :
    (m:ℝ)^2/(2*(precision m P+1:ℝ)) ≤ 1/(P+1:ℝ) := by
  have hp : 0 < (P:ℝ)+1 := by positivity
  have hd : 0 < 2*((precision m P:ℝ)+1) := by positivity
  apply (div_le_div_iff₀ hd hp).mpr
  simp only [precision,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
  have hs : (m:ℝ)^2 ≤ 2*((m:ℝ)+1)^2 := by
    nlinarith [show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m]
  nlinarith only [mul_le_mul_of_nonneg_right hs hp.le]

theorem error (rho P : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → Point) (hu : Function.Injective u) :
    |(value rho (P,List.ofFn u):ℝ)-exactTotal (GaussianFrequency.frequency rho) u| ≤
      1/(P+1:ℝ) := by
  have h := total_error rho (precision m P) hrho u hu
  simpa only [value,List.length_ofFn] using h.trans (precision_budget m P)

end ContinuumCoulomb.CoulombPairSum

end

end OAI
