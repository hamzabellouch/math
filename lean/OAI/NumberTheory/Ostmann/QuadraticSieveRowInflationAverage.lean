import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationDilation

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem rowInflation_sum_divisor_weights (P V : Finset ℕ) (f : ℕ → ℝ) (D : ℝ)
    (hf : ∀ v ∈ V, 0 ≤ f v)
    (hcount : ∀ v ∈ V, ((P.filter (fun p => p∣v)).card:ℝ) ≤ D) :
    (∑ p ∈ P, ∑ v ∈ V.filter (fun v => p∣v), f v) ≤ D*∑ v ∈ V, f v := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have he : (∑ p ∈ P, if p∣v then f v else 0) =
      ((P.filter (fun p => p∣v)).card:ℝ)*f v := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_right (hcount v hv) (hf v hv)

theorem quadraticNorm_le_primeDilation_average (P V W S : Finset ℕ)
    (Drow Dcol : ℝ) (hDr : 0 ≤ Drow) (hDc : 0 ≤ Dcol)
    (hP : 0 < P.card) (hprime : ∀ p ∈ P, p.Prime)
    (hV : ∀ v ∈ V, 0 < v)
    (hmap : ∀ p ∈ P, ∀ v ∈ V, ¬p∣v → p*v ∈ W)
    (hrows : ∀ v ∈ V, ((P.filter (fun p => p∣v)).card:ℝ) ≤ Drow)
    (hcols : ∀ n ∈ S, ((P.filter (fun p => p∣n)).card:ℝ) ≤ Dcol)
    (habsorb : 2*(Drow+2*Dcol) ≤ (P.card:ℝ)) :
    quadraticNorm V S ≤ 4*quadraticNorm W S := by
  classical
  have hPr : (0:ℝ) < P.card := by exact_mod_cast hP
  have hQv := quadraticNorm_nonneg V S
  have hQw := quadraticNorm_nonneg W S
  let A : ℝ := (Drow+2*Dcol)/(P.card:ℝ)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA : A ≤ 1/2 := by
    apply (div_le_iff₀ hPr).mpr
    linarith
  have hnorm : quadraticNorm V S ≤ A*quadraticNorm V S+2*quadraticNorm W S := by
    apply quadraticNorm_le_of_bound V S (by positivity)
    intro a
    have hE := coefficientEnergy_nonneg S a
    have hr : (∑ p ∈ P, jacobiEnergy (V.filter (fun v => p∣v)) S a) ≤
        Drow*jacobiEnergy V S a :=
      rowInflation_sum_divisor_weights P V _ Drow (fun _ _ => sq_nonneg _) hrows
    have hc : (∑ p ∈ P, coefficientEnergy (S.filter (fun n => p∣n)) a) ≤
        Dcol*coefficientEnergy S a :=
      rowInflation_sum_divisor_weights P S _ Dcol (fun _ _ => sq_nonneg _) hcols
    have hv := jacobiEnergy_le_quadraticNorm V S a
    have hsum := Finset.sum_le_sum (fun p hp =>
      primeDilation_energy_le (hprime p hp) V W S a hV (hmap p hp))
    have heq : (∑ p ∈ P, (jacobiEnergy (V.filter (fun v => p∣v)) S a +
        2*quadraticNorm W S*coefficientEnergy S a +
        2*quadraticNorm V S*coefficientEnergy (S.filter (fun n => p∣n)) a)) =
        (∑ p ∈ P, jacobiEnergy (V.filter (fun v => p∣v)) S a) +
        (P.card:ℝ)*(2*quadraticNorm W S*coefficientEnergy S a) +
        2*quadraticNorm V S*(∑ p ∈ P, coefficientEnergy (S.filter (fun n => p∣n)) a) := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,
        nsmul_eq_mul,← Finset.mul_sum]
    rw [heq,Finset.sum_const,nsmul_eq_mul] at hsum
    have hh : (P.card:ℝ)*jacobiEnergy V S a ≤
        (Drow+2*Dcol)*quadraticNorm V S*coefficientEnergy S a +
          (P.card:ℝ)*(2*quadraticNorm W S*coefficientEnergy S a) := by
      have hr' := hr.trans (mul_le_mul_of_nonneg_left hv hDr)
      have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*quadraticNorm V S by positivity)
      nlinarith
    have hid : (P.card:ℝ)*((A*quadraticNorm V S+2*quadraticNorm W S)*coefficientEnergy S a) =
        (Drow+2*Dcol)*quadraticNorm V S*coefficientEnergy S a +
          (P.card:ℝ)*(2*quadraticNorm W S*coefficientEnergy S a) := by
      dsimp [A]
      field_simp
    rw [← hid] at hh
    nlinarith only [hh,hPr]
  nlinarith [mul_le_mul_of_nonneg_right hA hQv]

end Ostmann.QuadraticSieve

end

end OAI
