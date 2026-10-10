import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Scale-uniform derivatives of the actual expanding-torus nonlinearity -/

open Set Metric

namespace DefocusingNLS

private theorem expanding_linear_two_jet_bound (L : FourierL2 →L[ℝ] FourierL2)
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

private theorem expanding_bilinear_two_jet_bound (B : FourierL2 →L[ℝ] FourierL2 →L[ℝ] FourierL2)
    (F G : FourierL2 → FourierL2) (hF : ContDiff ℝ ⊤ F) (hG : ContDiff ℝ ⊤ G)
    (K : ℝ) (hK : 0 ≤ K) (hBK : ‖B‖ ≤ K)
    (R A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFb : ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n F f‖ ≤ A)
    (hGb : ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n G f‖ ≤ D) :
    ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (fun g => B (F g) (G g)) f‖ ≤ 4 * K * A * D := by
  intro f hf n hn
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ) ^ n ≤ 4 := by interval_cases n <;> norm_num
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i F f‖ * ‖iteratedFDeriv ℝ (n - i) G f‖ :=
      B.norm_iteratedFDeriv_le_of_bilinear hF hG f (by simp)
    _ ≤ K * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i F f‖ * ‖iteratedFDeriv ℝ (n - i) G f‖ :=
      mul_le_mul_of_nonneg_right hBK (by positivity)
    _ ≤ K * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * D := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      gcongr
      · exact hFb f hf i (hi'.trans hn)
      · exact hGb f hf (n - i) ((Nat.sub_le n i).trans hn)
    _ = K * ((2 : ℝ) ^ n * A * D) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ = (K * A * D) * (2 : ℝ) ^ n := by ring
    _ ≤ (K * A * D) * 4 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 4 * K * A * D := by ring

/-- Derivatives through order two are bounded uniformly for every `L ≥ 1`. -/
theorem exists_expandingOddPower_two_jet_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2), ‖f‖ ≤ R →
      ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n (expandingOddPower a k L ha ha1 hk hL m) f‖ ≤ C := by
  obtain ⟨J, hJ, hJb⟩ := expanding_linear_two_jet_bound (ContinuousLinearMap.id ℝ FourierL2) R hR
  obtain ⟨D, hD, hDb⟩ := expanding_linear_two_jet_bound sobolevConjugation R hR
  let K := expandingAlgebraBound a k
  have hK : 0 ≤ K := expandingAlgebraBound_nonneg a k
  induction m with
  | zero =>
      exact ⟨J, hJ, fun _ _ => hJb⟩
  | succ m ih =>
      obtain ⟨A, hA, hAb⟩ := ih
      refine ⟨4 * K * (4 * K * A * D) * J, by positivity, ?_⟩
      intro L hL
      let B := expandingRealBilinearProduct a k L ha ha1 hk hL
      let F : FourierL2 → FourierL2 := fun f =>
        B (expandingOddPower a k L ha ha1 hk hL m f) (sobolevConjugation f)
      have hBK : ‖B‖ ≤ K := expandingRealBilinearProduct_norm_le a k L ha ha1 hk hL
      have hF : ContDiff ℝ ⊤ F :=
        (B.contDiff.comp (contDiff_expandingOddPower a k L ha ha1 hk hL m)).clm_apply
          sobolevConjugation.contDiff
      have hFb : ∀ f : FourierL2, ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
          ‖iteratedFDeriv ℝ n F f‖ ≤ 4 * K * A * D :=
        expanding_bilinear_two_jet_bound B (expandingOddPower a k L ha ha1 hk hL m)
          sobolevConjugation (contDiff_expandingOddPower a k L ha ha1 hk hL m)
          sobolevConjugation.contDiff K hK hBK R A D hA hD (hAb L hL) hDb
      exact expanding_bilinear_two_jet_bound B F (fun f => f) hF contDiff_id K hK hBK
        R (4 * K * A * D) J (by positivity) hJ hFb hJb

/-- The derivative is Lipschitz on each ball, uniformly in the torus radius. -/
theorem exists_expandingOddPower_derivative_lipschitz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (f g : FourierL2),
      ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) f -
        fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) g‖ ≤ C * ‖f - g‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_expandingOddPower_two_jet_bound a k ha ha1 hk m R hR
  refine ⟨C, hC, ?_⟩
  intro L hL f g hf hg
  have hdiff : Differentiable ℝ (fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m)) :=
    (contDiff_infty_iff_fderiv.mp ((contDiff_expandingOddPower a k L ha ha1 hk hL m).of_le
      (by simp))).2.differentiable (by simp)
  apply (convex_closedBall (0 : FourierL2) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hdiff x)
  · intro x hx
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hCb L hL x (by simpa using hx) 2 le_rfl
  · simpa using hg
  · simpa using hf

end DefocusingNLS

end OAI
