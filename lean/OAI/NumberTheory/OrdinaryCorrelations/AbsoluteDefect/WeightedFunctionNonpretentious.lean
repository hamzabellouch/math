import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingParameters
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BilinearPart

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryCorrelations OrdinaryCorrelations.PretentiousEuler
open OrdinaryArchimedeanTwist MeasureTheory

lemma weightedFunction_nonpretentious {f : ℕ → ℂ}
    (hf : OneBounded f) (hNP : UniformlyNonpretentious f)
    (P : Finset ℕ) {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    UniformlyNonpretentious (weightedFunction f P z) := by
  intro q hq χ
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [eventual_all_weighted_distance hf hNP q hq χ R] with N hN
  apply le_csInf
  · refine Set.Nonempty.image _ ?_
    exact ⟨0,neg_nonpos.mpr (Nat.cast_nonneg N),Nat.cast_nonneg N⟩
  · rintro v ⟨t,ht,rfl⟩
    exact hN P z hz t ht

lemma normalized_twist_bound {f : ℕ → ℂ} (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    ‖(N:ℂ)⁻¹*∑n∈Finset.Icc 1 N,twist f t n‖≤1 := by
  by_cases hN : N=0
  · simp [hN]
  have hNr : 0<(N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs : ‖∑n∈Finset.Icc 1 N,twist f t n‖≤(N:ℝ) := by
    calc
      _ ≤ ∑n∈Finset.Icc 1 N,‖twist f t n‖ := norm_sum_le _ _
      _ ≤ ∑n∈Finset.Icc 1 N,(1:ℝ) := Finset.sum_le_sum (fun n _ => by
        simpa only [norm_twist] using hf n)
      _ = (N:ℝ) := by simp
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (N:ℝ)⁻¹*(N:ℝ) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hNr.le)
    _ = 1 := inv_mul_cancel₀ hNr.ne'

theorem cofactor_moving_mean_tendsto_zero {f : ℕ → ℂ}
    (hf : OneBounded f) (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p) :
    Tendsto (fun p : MovingParameters => (p.1.1:ℂ)⁻¹*
      ∑n∈Finset.Icc 1 p.1.1,twist f p.1.2 n/(primeCount P n+1:ℂ))
      movingFilter (nhds 0) := by
  let F := fun (p : MovingParameters) (z : ℝ) => (p.1.1:ℂ)⁻¹*
      ∑n∈Finset.Icc 1 p.1.1,twist (weightedFunction f P z) p.1.2 n
  have hc (p : MovingParameters) : Continuous (F p) := by
    unfold F twist weightedFunction
    fun_prop
  have hb (p : MovingParameters) : ∀ᵐz ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ‖F p z‖≤1 := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro z hz
    exact normalized_twist_bound (weightedFunction_oneBounded hf P hz) p.1.1 p.1.2
  have ht : ∀ᵐz ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Tendsto (fun p => F p z) movingFilter (nhds 0) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro z hz
    exact moving_multiplicative_mean_tendsto_zero (weightedFunction_oneBounded hf P hz)
      (weightedFunction_multiplicative hm hP z) (weightedFunction_nonpretentious hf hNP P hz)
  have : movingFilter.IsCountablyGenerated := by
    unfold movingFilter
    infer_instance
  have hi := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    («μ»:=volume.restrict (Set.Icc (0:ℝ) 1))
    (l:=movingFilter) (F:=F) (f:=fun _ => (0:ℂ)) (fun _ => (1:ℝ))
    (Filter.Eventually.of_forall (fun p => (hc p).aestronglyMeasurable))
    (Filter.Eventually.of_forall hb) (integrableOn_const (measure_Icc_lt_top.ne)) ht
  have he (p : MovingParameters) : (∫z in Set.Icc (0:ℝ) 1,F p z)=
      (p.1.1:ℂ)⁻¹*∑n∈Finset.Icc 1 p.1.1,twist f p.1.2 n/(primeCount P n+1:ℂ) := by
    rw [show F p=(fun z => (p.1.1:ℂ)⁻¹*∑n∈Finset.Icc 1 p.1.1,
      weightedFunction f P z n*Complex.exp (Complex.I*((p.1.2*Real.log n:ℝ):ℂ))) by rfl,
      MeasureTheory.integral_const_mul,MeasureTheory.integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [MeasureTheory.integral_mul_const,cofactor_integral]
      unfold twist
      ring
    · intro n hn
      exact ((continuous_weightedFunction f P n).mul continuous_const).integrableOn_Icc
  simp_rw [he] at hi
  simpa using hi

end SourcePrimeFactor

end

end OAI
