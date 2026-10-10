import OAI.NumberTheory.CubicMoment.Angular.AngularCoordinateWeightedTuple
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleSize

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma angularTupleCore_norm (ℓ : ℤ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (V : ℝ → ℂ) (Y : ℝ) (n : ι → Eisenstein) (hn : ∀ i, n i ≠ 0) :
    ‖primaryAngularTupleCore ℓ A a b q η t V Y n‖ =
      ‖primaryTupleCore A a b q η t V Y n‖ := by
  have he : primaryAngularTupleCore ℓ A a b q η t V Y n =
      (∏ i, theta ℓ (n i))*primaryTupleCore A a b q η t V Y n := by
    unfold primaryAngularTupleCore primaryTupleCore
    rw [← mul_assoc,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [he,norm_mul,norm_prod]
  simp only [norm_theta (hn _) ℓ,Finset.prod_const_one,one_mul]

lemma angular_vonMangoldt_tuple_core_bound (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y)
    (n : ι → Eisenstein) (hn : n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y))) :
    ‖primaryAngularTupleCore ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ ≤
      (2*Y)^(Fintype.card ι)*M := by
  rw [angularTupleCore_norm ℓ _ _ _ _ _ _ _ _ _ (fun i =>
    primary_ne_zero (mem_primaryElementBall.mp ((Fintype.mem_piFinset.mp hn) i)).1)]
  exact vonMangoldt_tuple_core_bound a b ha hb q η hq t V hM hV hY n hn

 theorem angular_vonMangoldt_unsplit_size (ℓ : ℤ) (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (hq : ∀ i, q i ≠ 0) (t : ι → ℝ) (V : ℝ → ℂ)
    {M Y : ℝ} (hM : 0 ≤ M) (hV : ∀ x, ‖V x‖ ≤ M) (hY : 0 ≤ Y) :
    ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y‖ ≤
      (M*72^(Fintype.card ι))*Y^(2*Fintype.card ι) := by
  unfold primaryAngularUnsplitTuple
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        ‖primaryAngularTupleCore ℓ (fun _ : ι => idealVonMangoldt) a b q η t V Y n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (2*Y)^(Fintype.card ι)*M :=
      Finset.sum_le_sum (fun n hn => angular_vonMangoldt_tuple_core_bound ℓ a b ha hb q η hq t V hM hV hY n hn)
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
