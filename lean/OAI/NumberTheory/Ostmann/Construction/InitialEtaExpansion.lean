import OAI.NumberTheory.Ostmann.Construction.InitialEtaPhysical
import OAI.NumberTheory.Ostmann.Construction.InitialEtaPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

variable (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
  {ι : Type*} [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource)
  (b s : ℕ) (tb td : ℤ)

omit [Fintype ι] [DecidableEq ι] in
theorem tupleLocalTest_norm_le [_fintypeIndex : Fintype ι] [_decidableEqIndex : DecidableEq ι]
    (i : Position b s ι) {q : ℕ} (hq : q.Prime) (z : ZMod q) :
    ‖tupleLocalTest d P i q z‖ ≤ (q:ℝ) := by
  rcases i with ⟨h,i⟩
  rcases i with u | j
  · exact favorableGiantResidueTest_norm_le_prime d P hq z
  · exact residueTest_norm_le_prime d hq z

theorem tuplePhysical_summable {X : ℝ} (hX : 0 < X)
    (x : JointSample giant bulk spectator aux b s) :
    Summable (fun n : ℤ => SchwartzCutoff.psi ((n:ℝ)/X) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.1 : ℝ):ℂ) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.2 : ℝ):ℂ)) := by
  have hpsi : Summable (fun n : ℤ => ‖SchwartzCutoff.psi ((n:ℝ)/X)‖) := by
    simpa only [schwartzScale_apply,div_eq_mul_inv] using
      schwartz_int_norm_summable (schwartzScale SchwartzCutoff.psi X⁻¹ (inv_ne_zero hX.ne'))
  apply (hpsi.mul_right (∏i,(tupleValues x i : ℝ))).of_norm_bounded
  intro n
  rw [mul_assoc,tupleTest_eq,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (tupleBins_nonneg tb td x),norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i : Position b s ι => ‖tupleLocalTest d P i (tupleValues x i) (n:ZMod (tupleValues x i))‖)
      (g := fun i : Position b s ι => (tupleValues x i : ℝ)) (fun _ _ => norm_nonneg _)
      (fun i _ => tupleLocalTest_norm_le d P b s i (tupleValues_prime x i) _))
    (tupleBins_nonneg tb td x)).trans
      (mul_le_of_le_one_left (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
        (tupleBins_le_one tb td x))

theorem jointPrior_tupleTest (n : ℤ) :
    (jointPrior giant bulk spectator aux b s).cmean (fun x =>
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.1 : ℝ):ℂ) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.2 : ℝ):ℂ)) =
    ((halfListTest d P giant bulk spectator aux b s tb td n)^2 : ℝ) := by
  have h := FinitePrior.pair_mean_product
    (halfListPrior giant bulk spectator aux b s) (halfListPrior giant bulk spectator aux b s)
    (halfListTupleTest d P giant bulk spectator aux b s tb td n)
    (halfListTupleTest d P giant bulk spectator aux b s tb td n)
  rw [←halfListTest_eq_tuple_mean] at h
  have hc := congrArg (fun r : ℝ => (r:ℂ)) h
  simpa only [jointPrior,FinitePrior.cmean,FinitePrior.mean,Complex.ofReal_sum,
    Complex.ofReal_mul,pow_two] using hc

theorem statistic_eq_tuple_mean {X : ℝ} (hX : 0 < X) :
    ((smoothedStatistic X (halfListTest d P giant bulk spectator aux b s tb td):ℝ):ℂ) /
      (Real.sqrt X:ℂ) =
    (jointPrior giant bulk spectator aux b s).cmean
      (tuplePhysical d P giant bulk spectator aux b s tb td X) := by
  let μ := jointPrior giant bulk spectator aux b s
  let f := fun (x : JointSample giant bulk spectator aux b s) (n : ℤ) =>
    SchwartzCutoff.psi ((n:ℝ)/X) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.1 : ℝ):ℂ) *
      ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.2 : ℝ):ℂ)
  have hs : ∀x, Summable (f x) := tuplePhysical_summable d P giant bulk spectator aux b s tb td hX
  have he := Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun x n => (μ.mass x:ℂ)*f x n) (fun x _ => (hs x).mul_left _)
  change _ = (∑x,(μ.mass x:ℂ)*((∑' n,f x n)/(Real.sqrt X:ℂ)))
  simp only [←mul_div_assoc,←Finset.sum_div]
  simp only [tsum_mul_left] at he
  rw [←he]
  congr 1
  unfold smoothedStatistic
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  have hpsi : ((SchwartzCutoff.psi ((n:ℝ)/X)).re:ℂ)=SchwartzCutoff.psi ((n:ℝ)/X) := by
    apply Complex.ext <;> simp [SchwartzCutoff.psi_im]
  simp only [Complex.ofReal_mul,hpsi]
  rw [←jointPrior_tupleTest d P giant bulk spectator aux b s tb td n]
  unfold FinitePrior.cmean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [f,μ]
  ring

theorem statistic_eq_distinct_add_repeated {X : ℝ} (hX : 0 < X) :
    ((smoothedStatistic X (halfListTest d P giant bulk spectator aux b s tb td):ℝ):ℂ) /
      (Real.sqrt X:ℂ) =
    distinctContribution d P giant bulk spectator aux b s tb td X +
      repeatedContribution d P giant bulk spectator aux b s tb td X := by
  classical
  rw [statistic_eq_tuple_mean d P giant bulk spectator aux b s tb td hX]
  unfold distinctContribution repeatedContribution FinitePrior.cmean
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  split_ifs <;> ring

end Ostmann.Construction.InitialEta

end

end OAI
