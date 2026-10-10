import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CoulombPairProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableHopping
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserVelocityNumerics
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarFieldBounds

namespace OAI

/-! Actual well-depth counterterms are finite sums of certified Coulomb
entries divided by the fixed onsite hopping. A fixed positive denominator
guard makes every rational evaluation well defined. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.CountertermEvaluation

private theorem guard_exists (rho : ℕ) : ∃ C : ℕ, 1 ≤ C ∧
    2 ≤ (C:ℝ)*planarHopping 0 ∧
    localizedPotentialBound (GaussianFrequency.frequency rho) ≤ C ∧
    planarWellDerivativeConstant ≤ C := by
  let B := 1+2/planarHopping 0+
    localizedPotentialBound (GaussianFrequency.frequency rho)+planarWellDerivativeConstant
  obtain ⟨C,hC⟩ := exists_nat_gt B
  have hT := planarHopping_positive 0
  have hV := localizedPotentialBound_nonnegative (GaussianFrequency.frequency rho)
  have hW := planarWellDerivativeConstant_positive
  have h1 : (1:ℝ) ≤ C := by
    dsimp [B] at hC
    have hp : 0 ≤ 2/planarHopping 0 := by positivity
    linarith
  refine ⟨C,by exact_mod_cast h1,?_,?_,?_⟩
  · apply (div_le_iff₀ hT).mp
    dsimp [B] at hC
    linarith
  · dsimp [B] at hC
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hT.le]
  · dsimp [B] at hC
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hT.le]

def guard (rho : ℕ) : ℕ := Classical.choose (guard_exists rho)

theorem guard_bounds (rho : ℕ) : 1 ≤ guard rho ∧
    2 ≤ (guard rho:ℝ)*planarHopping 0 ∧
    localizedPotentialBound (GaussianFrequency.frequency rho) ≤ guard rho ∧
    planarWellDerivativeConstant ≤ guard rho := Classical.choose_spec (guard_exists rho)

def denominator (rho p : ℕ) : ℚ :=
  max 1 ((guard rho:ℚ)*ComputableHopping.approximate ((1,p),0))

def entry (rho p : ℕ) (a b : ℚ×ℚ) : ℚ :=
  (guard rho:ℚ)*CoulombPairEvaluation.approximate rho p a b / denominator rho p

theorem entry_error (rho p : ℕ) (hrho : 0 < rho) (a b : ℚ×ℚ) :
    |(entry rho p a b:ℝ)-
      localizedCoulombCoeff (GaussianFrequency.frequency rho)
        (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)/planarHopping 0| ≤
      2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  let C : ℝ := guard rho
  let T : ℝ := planarHopping 0
  let A : ℝ := localizedCoulombCoeff (GaussianFrequency.frequency rho)
    (PlanarForcingProgram.position a) (PlanarForcingProgram.position b)
  let ε : ℝ := ((p:ℝ)+1)⁻¹
  have hC : 1 ≤ C := by dsimp [C]; exact_mod_cast (guard_bounds rho).1
  have hCp : 0 < C := by linarith
  have hT : 0 < T := planarHopping_positive 0
  have hCT : 1 ≤ C*T := by have h := (guard_bounds rho).2.1; dsimp [C,T]; linarith
  have hf : 0 < GaussianFrequency.frequency rho := by
    apply Real.sqrt_pos.mpr
    change 0 < 4*Real.pi*(rho:ℝ)
    positivity
  have hA : |A| ≤ C := by
    rw [abs_of_nonneg (localizedCoulombCoeff_nonnegative _ _ _)]
    exact (localizedCoulombCoeff_le hf _ _).trans (guard_bounds rho).2.2.1
  have he := CoulombPairEvaluation.approximation_error rho p hrho a b
  have ht : |(ComputableHopping.approximate ((1,p),0):ℝ)-T| ≤ ε := by
    simpa only [Prod.fst,Prod.snd,Rat.cast_zero,T,ε] using
      ComputableHopping.approximation_error ((1,p),0) (by norm_num)
  have hden : |(denominator rho p:ℝ)-C*T| ≤ C*ε := by
    have hm : |C*(ComputableHopping.approximate ((1,p),0):ℝ)-C*T| ≤ C*ε := by
      rw [← mul_sub,abs_mul,abs_of_pos hCp]
      exact mul_le_mul_of_nonneg_left ht hCp.le
    simpa only [denominator,Rat.cast_max,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast,C,T]
      using MoserVelocityNumerics.clamp_error hCT hm
  have hden1 : (1:ℝ) ≤ denominator rho p := by
    exact_mod_cast le_max_left (1:ℚ) ((guard rho:ℚ)*ComputableHopping.approximate ((1,p),0))
  have hnum : |-(C*(CoulombPairEvaluation.approximate rho p a b:ℝ))- -(C*A)| ≤ C*ε := by
    rw [show -(C*(CoulombPairEvaluation.approximate rho p a b:ℝ))- -(C*A) =
      -(C*((CoulombPairEvaluation.approximate rho p a b:ℝ)-A)) by ring,
      abs_neg,abs_mul,abs_of_pos hCp]
    exact mul_le_mul_of_nonneg_left he hCp.le
  have hAb : |-(C*A)| ≤ C^2 := by
    rw [abs_neg,abs_mul,abs_of_pos hCp]
    exact (mul_le_mul_of_nonneg_left hA hCp.le).trans_eq (by ring)
  have h := MoserVelocityNumerics.quotient_error hCT hden1 hAb hnum hden
  have hid : C*A/(C*T) = A/T := by field_simp
  simp only [neg_neg,hid] at h
  have hsmall : C*ε+C^2*(C*ε) ≤ 2*C^3*ε := by
    have heps : 0 ≤ ε := by dsimp [ε]; positivity
    have hc3 : C ≤ C^3 := le_self_pow₀ hC (by decide)
    have hm := mul_le_mul_of_nonneg_right hc3 heps
    nlinarith only [hm]
  exact (show |(entry rho p a b:ℝ)-A/T| ≤ C*ε+C^2*(C*ε) by
    simpa only [entry,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,C] using h).trans hsmall

theorem squaredDistance_eq_zero (a b : ℚ×ℚ) :
    CoulombPairEvaluation.squaredDistance a b = 0 ↔ a=b := by
  constructor
  · intro h
    unfold CoulombPairEvaluation.squaredDistance at h
    have h1 : (a.1-b.1)^2 = 0 := by nlinarith [sq_nonneg (a.2-b.2)]
    have h2 : (a.2-b.2)^2 = 0 := by nlinarith [sq_nonneg (a.1-b.1)]
    apply Prod.ext <;> nlinarith
  · rintro rfl
    simp [CoulombPairEvaluation.squaredDistance]

def offsite (rho p : ℕ) (a b : ℚ×ℚ) : ℚ :=
  if CoulombPairEvaluation.squaredDistance a b = 0 then 0 else entry rho p a b

def row (rho p : ℕ) (a : ℚ×ℚ) (sites : List (ℚ×ℚ)) : ℚ :=
  (sites.map (offsite rho p a)).sum

theorem row_ofFn (rho p : ℕ) {m : ℕ} (u : Fin m → ℚ×ℚ) (i : Fin m) :
    row rho p (u i) (List.ofFn u) = ∑ j, offsite rho p (u i) (u j) := by
  simp only [row,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem row_error (rho p : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → ℚ×ℚ) (hu : Function.Injective u) (i : Fin m) :
    |(row rho p (u i) (List.ofFn u):ℝ)-
      localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i| ≤
      (m:ℝ)*2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  rw [row_ofFn]
  simp only [Rat.cast_sum,localizedCounterterm,localizedOffsiteSum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j : Fin m, 2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i=j
      · subst j
        simp only [offsite,squaredDistance_eq_zero,ite_true,Rat.cast_zero,zero_div,sub_self,abs_zero]
        positivity
      · have huij : u i ≠ u j := fun hij => h (hu hij)
        simpa only [offsite,squaredDistance_eq_zero,ite_eq_right huij,ite_eq_right h]
          using entry_error rho p hrho (u i) (u j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ContinuumCoulomb.CountertermEvaluation

end

end OAI
