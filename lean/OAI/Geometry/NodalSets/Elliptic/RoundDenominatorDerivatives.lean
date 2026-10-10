import OAI.Geometry.NodalSets.Coefficients.RoundCorrectionDenominator
import OAI.Geometry.NodalSets.Elliptic.FrequencyLeibniz

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma real_partial_iterated_bound (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) (i : Fin 4) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ u y (Pi.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ (r+1) u x‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const (n := r)
    hdf.contDiffAt
    (c := Pi.single i (1:ℝ)) (x := x)
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  simpa [Pi.norm_single,norm_iteratedFDeriv_fderiv] using h

lemma roundDenominator_sum (u : Yau.Jets.Coord → ℝ) (n : ℕ) :
    roundCorrectionDenominator u n = fun x ↦
      (∑ i : Fin 4, roundCoordFactor x *
        (fderiv ℝ u x (Pi.single i 1)*fderiv ℝ u x (Pi.single i 1))) +
      seedEigenvalue n*(u x*u x) := by
  funext x
  rw [roundCorrectionDenominator_formula,sourceEuclideanNorm,
    Real.sq_sqrt (by positivity),Finset.mul_sum]
  simp [pow_two]

theorem round_denominator_derivative_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ‖iteratedFDeriv ℝ r (roundCorrectionDenominator u n) x‖ ≤
        C*(n:ℝ)^(r+8)*H^2 := by
  obtain ⟨B,hB,hq⟩ := compact_real_derivative_bound roundCoordFactor roundCoordFactor_smooth hQ r
  let C : ℝ := 4*((2:ℝ)^r*B*((2:ℝ)^r*A*A))+10*((2:ℝ)^r*A*A)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro u hu n hn x hx H hH hub
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) ≤ n := by positivity
  let p : Fin 4 → Yau.Jets.Coord → ℝ := fun i y ↦ fderiv ℝ u y (Pi.single i 1)
  have hp (i : Fin 4) : ContDiff ℝ ∞ (p i) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hpb (i : Fin 4) (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (p i) x‖ ≤ A*(n:ℝ)^(k+4)*H := by
    exact (real_partial_iterated_bound u hu x i k).trans (by
      simpa [Nat.add_assoc] using hub (k+1) (by omega))
  have hsquare (i : Fin 4) (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (fun y ↦ p i y*p i y) x‖ ≤
        ((2:ℝ)^r*A*A)*(n:ℝ)^(k+8)*(H^2) := by
    have h := frequency_product_derivative (p i) (p i) (hp i) (hp i) x k 4 4
      hN0 hA.le hA.le hH.le hH.le (fun j hj ↦ hpb i j (by omega))
      (fun j hj ↦ hpb i j (by omega))
    simp only [Nat.add_assoc,show 4+4=8 from rfl] at h
    have hh : H*H = H^2 := by ring
    rw [hh] at h
    exact h.trans (by gcongr; norm_num)
  have hqN (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k roundCoordFactor x‖ ≤ B*(n:ℝ)^(k+0)*1 := by
    have hpow : 1 ≤ (n:ℝ)^k := one_le_pow₀ hN
    simpa using (hq k hk x hx).trans (le_mul_of_one_le_right hB.le hpow)
  have hterm (i : Fin 4) :
      ‖iteratedFDeriv ℝ r (fun y ↦ roundCoordFactor y*(p i y*p i y)) x‖ ≤
        ((2:ℝ)^r*B*((2:ℝ)^r*A*A))*(n:ℝ)^(r+8)*H^2 := by
    have h := frequency_product_derivative roundCoordFactor (fun y ↦ p i y*p i y)
      roundCoordFactor_smooth ((hp i).mul (hp i)) x r 0 8
      hN0 hB.le (by positivity) (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg H)
      hqN (hsquare i)
    simpa using h
  have hsum :
      ‖iteratedFDeriv ℝ r (fun y ↦ ∑ i : Fin 4, roundCoordFactor y*(p i y*p i y)) x‖ ≤
        4*((2:ℝ)^r*B*((2:ℝ)^r*A*A))*(n:ℝ)^(r+8)*H^2 := by
    rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
      ((roundCoordFactor_smooth.mul ((hp i).mul (hp i))).of_le
        (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
    have h := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i _ ↦ hterm i))
    simpa [mul_assoc] using h
  have hu2 := frequency_product_derivative u u hu hu x r 3 3
    hN0 hA.le hA.le hH.le hH.le (fun j hj ↦ hub j (by omega))
    (fun j hj ↦ hub j (by omega))
  have hlam : 0 ≤ seedEigenvalue n := by unfold seedEigenvalue; positivity
  have hlam10 : seedEigenvalue n ≤ 10*(n:ℝ)^2 := by
    unfold seedEigenvalue
    have : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    nlinarith
  have heigen : ‖iteratedFDeriv ℝ r (fun y ↦ seedEigenvalue n*(u y*u y)) x‖ ≤
      10*((2:ℝ)^r*A*A)*(n:ℝ)^(r+8)*H^2 := by
    change ‖iteratedFDeriv ℝ r (seedEigenvalue n • (fun y ↦ u y*u y)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((hu.mul hu).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hlam]
    calc
      _ ≤ (10*(n:ℝ)^2)*((2:ℝ)^r*A*A*(n:ℝ)^(r+3+3)*(H*H)) := by gcongr
      _ = _ := by
        rw [show r+8 = 2+(r+3+3) by omega,pow_add]
        ring
  rw [roundDenominator_sum,fun_iteratedFDeriv_add_apply
    ((ContDiff.sum (fun i _ ↦ roundCoordFactor_smooth.mul ((hp i).mul (hp i)))).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((contDiff_const.mul (hu.mul hu)).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  have h := (norm_add_le _ _).trans (add_le_add hsum heigen)
  convert h using 1
  first | rfl | dsimp [C]; ring

end
end Yau.Target

end OAI
