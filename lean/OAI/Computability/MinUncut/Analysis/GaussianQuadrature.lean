import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianRounding
import OAI.Computability.MinUncut.Encoding.ArbitraryProductWeights

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace MinUncut.FiniteGaussian
open GaussianBudget
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

lemma conditional_gridStep {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L)
    (F : (ι → Fin L) → ℝ) :
    (∫ x in cube T, gridStep T L F x ∂gaussianLaw ι)/(gaussianLaw ι).real (cube T)=
      (∑ j, (∏ i, gCell T L (j i))*F j)/(gIntegral (-T) T)^(Fintype.card ι) := by
  rw [setIntegral_gridStep hT.le hL,gaussian_cube hT.le]
  simp_rw [gaussian_cubeCell hT hL,mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (ne_of_gt gaussianConstant_pos))

lemma rational_grid_expectation (r : ℕ) (T : ℚ) (L : ℕ) (F : (ι → Fin L) → ℝ) :
    (∑ j, ((∏ i, cellWeight r T L (j i):ℚ):ℝ)*F j)=
      (∑ j, (∏ i, qCell r T L (j i))*F j)/(qIntegral r (-T) T:ℝ)^(Fintype.card ι) := by
  simp only [cellWeight,Rat.cast_prod,Rat.cast_div,Rat.cast_pow,Finset.prod_div_distrib,Finset.prod_const,
    Finset.card_univ,div_mul_eq_mul_div,← Finset.sum_div,qCell]

lemma joint_table_error (v : S → ι → ℝ) (hv : ∀ s, 1 ≤ ‖vector (v s)‖^2)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ s, (∑ i, |v s i|) ≤ A)
    {T : ℚ} (hT : 1 ≤ T) {L : ℕ} (hL : 0 < L) (r : ℕ)
    (F : (S → Bool) → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) :
    |(∫ x, F (thresholdTable v x) ∂gaussianLaw ι)-
      ∑ j : ι → Fin L, ((∏ i, cellWeight r T L (j i):ℚ):ℝ)*
        F (thresholdTable v (gridPoint T L j))| ≤
      (Fintype.card ι:ℝ)/(T:ℝ)^2+2*(Fintype.card S)*A*((T:ℝ)/L)+
        2*(Fintype.card ι)*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT0 : 0 < T := by linarith
  have ht := conditional_tableTest_bound v hv hA0 hA hT0 hL F hF
  rw [conditional_gridStep hT0 hL] at ht
  have hq := grid_product_bound_general hT hL r
    (fun j => F (thresholdTable v (gridPoint T L j)))
    (fun j => hF (thresholdTable v (gridPoint T L j)))
  rw [rational_grid_expectation]
  exact (abs_sub_le _ _ _).trans (add_le_add ht (by simpa only [abs_sub_comm] using hq))

end MinUncut.FiniteGaussian

end
end
section
namespace MinUncut.FiniteGaussian

def qError (r : ℕ) (U : ℚ) : ℚ := U^(2*r+1)/(2*r+1).factorial

lemma qError_cast (r : ℕ) (U : ℚ) : (qError r U:ℝ)=error r U := by
  unfold qError error
  push_cast
  rfl

structure GridData where
  T : ℕ
  L : ℕ
  r : ℕ
  deriving DecidableEq, Encodable

namespace GridData

def Check (d S : ℕ) (A ε : ℚ) (g : GridData) : Prop :=
  1 ≤ g.T ∧ 1 ≤ g.L ∧ (d:ℚ)/(g.T:ℚ)^2 < ε/4 ∧
    2*(S:ℚ)*A*g.T/g.L < ε/4 ∧
    2*(d:ℚ)*g.T*qError g.r ((g.T:ℚ)^2/2) < ε/4

instance (d S : ℕ) (A ε : ℚ) (g : GridData) : Decidable (Check d S A ε g) := by
  unfold Check; infer_instance

lemma exists_check (d S : ℕ) {A ε : ℚ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ g : GridData, g.Check d S A ε := by
  obtain ⟨T,hT⟩ := exists_nat_gt (4*(d:ℚ)/ε+1)
  have hnonnegT : 0 ≤ 4*(d:ℚ)/ε := by positivity
  have hT1 : (1:ℚ)<T := lt_of_le_of_lt (by linarith : 1 ≤ 4*(d:ℚ)/ε+1) hT
  have hTpos : (0:ℚ)<T := by linarith
  have hTnat : 1 ≤ T := by exact_mod_cast hT1.le
  have hT2 : (T:ℚ) ≤ (T:ℚ)^2 := by nlinarith
  have htail : (d:ℚ)/(T:ℚ)^2 < ε/4 := by
    have hh : 4*(d:ℚ) < ε*T := by
      have hh : 4*(d:ℚ)/ε < (T:ℚ) := by linarith
      have := (div_lt_iff₀ hε).mp hh
      nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hTpos)).mpr
    have := mul_le_mul_of_nonneg_left hT2 hε.le
    nlinarith
  obtain ⟨L,hL⟩ := exists_nat_gt (8*(S:ℚ)*A*T/ε+1)
  have hnonnegL : 0 ≤ 8*(S:ℚ)*A*T/ε := by positivity
  have hL1 : (1:ℚ)<L := lt_of_le_of_lt (by linarith : 1 ≤ 8*(S:ℚ)*A*T/ε+1) hL
  have hLpos : (0:ℚ)<L := by linarith
  have hLnat : 1 ≤ L := by exact_mod_cast hL1.le
  have hmesh : 2*(S:ℚ)*A*T/L < ε/4 := by
    have hh : 8*(S:ℚ)*A*T < ε*L := by
      have hh : 8*(S:ℚ)*A*T/ε < (L:ℚ) := by linarith
      have := (div_lt_iff₀ hε).mp hh
      nlinarith
    apply (div_lt_iff₀ hLpos).mpr
    nlinarith
  have hden : 0 < 4*(2*(d:ℚ)*T+1) := by positivity
  obtain ⟨r,hr⟩ := exists_error (U := (((T:ℚ)^2/2:ℚ):ℝ))
    (by exact_mod_cast (div_pos hε hden) : (0:ℝ) < (ε/(4*(2*(d:ℚ)*T+1)):ℚ))
  have hr' : qError r ((T:ℚ)^2/2) < ε/(4*(2*(d:ℚ)*T+1)) := by
    exact_mod_cast (show (qError r ((T:ℚ)^2/2):ℝ) < (ε/(4*(2*(d:ℚ)*T+1)):ℚ) by
      rw [qError_cast]; exact hr)
  have herr : 0 ≤ qError r ((T:ℚ)^2/2) := by unfold qError; positivity
  refine ⟨⟨T,L,r⟩,hTnat,hLnat,htail,hmesh,?_⟩
  change 2*(d:ℚ)*T*qError r ((T:ℚ)^2/2) < ε/4
  have hh := (lt_div_iff₀ hden).mp hr'
  nlinarith

def select (d S : ℕ) (A ε : ℚ) (hA : 0 ≤ A) (hε : 0 < ε) : GridData :=
  Encodable.choose (exists_check d S hA hε)

lemma select_check (d S : ℕ) (A ε : ℚ) (hA : 0 ≤ A) (hε : 0 < ε) :
    (select d S A ε hA hε).Check d S A ε :=
  Encodable.choose_spec (exists_check d S hA hε)

end GridData
end MinUncut.FiniteGaussian

end

end OAI
