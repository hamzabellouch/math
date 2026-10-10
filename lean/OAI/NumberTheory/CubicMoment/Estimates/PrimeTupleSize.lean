import OAI.NumberTheory.CubicMoment.Estimates.CoordinateWeightedTuple
import OAI.NumberTheory.CubicMoment.Estimates.IdealVonMangoldt

namespace OAI

/-! A polynomial bound for the actual von Mangoldt tuple sum. This coarse
bound is used only against arbitrarily rapid Mellin tails. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma vonMangoldt_coeff_norm_le {Y : ℝ} {n : Eisenstein}
    (hn : n ∈ primaryElementBall (2*Y)) :
    ‖((MvPowerSeries.coeff (idealExponentOf n) idealVonMangoldt:ℝ):ℂ)‖ ≤ 2*Y := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hp := (mem_primaryElementBall.mp hn).1
  have h := idealVonMangoldt_coeff_abs_le_logNorm (idealExponentOf n)
  rw [idealExponentOf_norm (primary_ne_zero hp)] at h
  exact h.trans ((Real.log_le_self (norm_nonneg n)).trans (mem_primaryElementBall.mp hn).2)

lemma vonMangoldt_tuple_core_bound (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (_hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  have hi (i : ι) :
      ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
        (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖ ≤ 2*Y := by
    have htw : ‖mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))‖ ≤ 1 := by
      rw [norm_mul,mellinPhase_norm,mul_one,norm_mul]
      exact (mul_le_mul (norm_mixedCubic_le_one ha hb _) (residueChar_norm_le_one (hq i) (η i) _)
        (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (_root_.norm_nonneg _) htw).trans
      (vonMangoldt_coeff_norm_le ((Fintype.mem_piFinset.mp hn) i))
  unfold primaryTupleCore
  rw [norm_mul,norm_prod]
  have hp : (∏ i, ‖((MvPowerSeries.coeff (idealExponentOf (n i)) idealVonMangoldt:ℝ):ℂ)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*mellinPhase (t i) (norm (n i)))‖) ≤
      (2*Y)^(Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, 2*Y :=
        Finset.prod_le_prod₀ (fun i _ => _root_.norm_nonneg _) (fun i _ => hi i)
      _ = _ := by simp
  exact mul_le_mul hp (hV _) (_root_.norm_nonneg _) (pow_nonneg (by positivity) _)

 theorem vonMangoldt_unsplit_size (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y) :
    ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) a b q η t V Y‖ ≤
      (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) := by
  unfold primaryUnsplitTuple
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        ‖primaryTupleCore (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (2*Y)^(Fintype.card ι)*M :=
      Finset.sum_le_sum (fun n hn => vonMangoldt_tuple_core_bound a b ha hb q η hq t V hM hV hY n hn)
    _ = ((primaryElementBall (2*Y)).card:ℝ)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      simp [Fintype.card_piFinset,Finset.prod_const]
    _ ≤ (36*Y)^(Fintype.card ι)*((2*Y)^(Fintype.card ι)*M) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (mul_nonneg (pow_nonneg (by positivity) _) hM)
      nlinarith [primaryElementBall_card_le (show 0 ≤ 2*Y by positivity)]
    _ = M*((36*Y)*(2*Y))^(Fintype.card ι) := by
      rw [mul_pow (36*Y) (2*Y)]
      ring
    _ = M*(72*Y^2)^(Fintype.card ι) := by congr 1; congr 1; ring
    _ = _ := by rw [mul_pow,pow_mul]; ring

end CubicFirstMoment

end

end OAI
