import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevPolynomialBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Uniform second-derivative bounds for the actual Sobolev nonlinearity -/

open Set Metric

namespace DefocusingNLS

private theorem linear_two_jet_bound (L : FourierL2 →L[ℝ] FourierL2)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun g => L g) f‖ ≤ C := by
  refine ⟨(‖L‖ + 1) * (R + 1), by positivity, ?_⟩
  intro f hf n hn
  have hLn := norm_nonneg L
  have hLR : 0 ≤ ‖L‖ * R := mul_nonneg hLn hR
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    have h := L.le_opNorm f
    have h' := mul_le_mul_of_nonneg_left hf hLn
    nlinarith
  · rw [norm_iteratedFDeriv_one, L.fderiv]
    nlinarith
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    have hderiv : fderiv ℝ (fun g => L g) = fun _ => L := funext (fun g => L.fderiv)
    rw [hderiv]
    simp only [fderiv_const_apply, norm_zero]
    positivity

private theorem bilinear_two_jet_bound (B : FourierL2 →L[ℝ] FourierL2 →L[ℝ] FourierL2)
    (F G : FourierL2 → FourierL2) (hF : ContDiff ℝ ⊤ F) (hG : ContDiff ℝ ⊤ G)
    (R A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFb : ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n F f‖ ≤ A)
    (hGb : ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n G f‖ ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun g => B (F g) (G g)) f‖ ≤ C := by
  refine ⟨4 * ‖B‖ * A * D, by positivity, ?_⟩
  intro f hf n hn
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ) ^ n ≤ 4 := by interval_cases n <;> norm_num
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i F f‖ * ‖iteratedFDeriv ℝ (n - i) G f‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear hF hG f (by simp)
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * D := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      gcongr
      · exact hFb f hf i (hi'.trans hn)
      · exact hGb f hf (n - i) ((Nat.sub_le n i).trans hn)
    _ = ‖B‖ * ((2 : ℝ) ^ n * A * D) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ = (‖B‖ * A * D) * (2 : ℝ) ^ n := by ring
    _ ≤ (‖B‖ * A * D) * 4 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 4 * ‖B‖ * A * D := by ring

/-- All derivatives of order at most two are uniformly bounded on a Sobolev ball.
The proof uses the polynomial's actual bounded bilinear operations. -/
theorem exists_sobolevOddPower_two_jet_bound (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (sobolevOddPower k hk m) f‖ ≤ C := by
  obtain ⟨J, hJ, hJb⟩ := linear_two_jet_bound (ContinuousLinearMap.id ℝ FourierL2) R hR
  obtain ⟨D, hD, hDb⟩ := linear_two_jet_bound sobolevConjugation R hR
  induction m with
  | zero =>
      exact ⟨J, hJ, hJb⟩
  | succ m ih =>
      obtain ⟨A, hA, hAb⟩ := ih
      let B := sobolevRealBilinearProduct k hk
      let F : FourierL2 → FourierL2 := fun f =>
        B (sobolevOddPower k hk m f) (sobolevConjugation f)
      have hF : ContDiff ℝ ⊤ F :=
        (B.contDiff.comp (contDiff_sobolevOddPower k hk m)).clm_apply sobolevConjugation.contDiff
      obtain ⟨C, hC, hCb⟩ := bilinear_two_jet_bound B (sobolevOddPower k hk m)
        sobolevConjugation (contDiff_sobolevOddPower k hk m) sobolevConjugation.contDiff
        R A D hA hD hAb hDb
      obtain ⟨C', hC', hC'b⟩ := bilinear_two_jet_bound B F (fun f => f) hF contDiff_id
        R C J hC hJ hCb hJb
      exact ⟨C', hC', hC'b⟩

/-- The real Fréchet derivative of the Sobolev odd-power map is uniformly Lipschitz on balls. -/
theorem exists_sobolevOddPower_derivative_lipschitz (k : ℝ) (hk : 6 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : FourierL2, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖fderiv ℝ (sobolevOddPower k hk m) f - fderiv ℝ (sobolevOddPower k hk m) g‖ ≤
        C * ‖f - g‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_sobolevOddPower_two_jet_bound k hk m R hR
  have hdiff : Differentiable ℝ (fderiv ℝ (sobolevOddPower k hk m)) :=
    (contDiff_infty_iff_fderiv.mp ((contDiff_sobolevOddPower k hk m).of_le
      (by simp))).2.differentiable (by simp)
  refine ⟨C, hC, ?_⟩
  intro f g hf hg
  apply (convex_closedBall (0 : FourierL2) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hdiff x)
  · intro x hx
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hCb x (by simpa using hx) 2 le_rfl
  · simpa using hg
  · simpa using hf

end DefocusingNLS

end OAI
