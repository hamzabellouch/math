import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousNonlinearity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Uniform second-derivative bounds for the actual homogeneous nonlinearity -/

open Set Metric

namespace DefocusingNLS

private theorem homogeneous_linear_two_jet_bound {a k : ℝ} (L : (HomogeneousY a k) →L[ℝ] (HomogeneousY a k))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (HomogeneousY a k), ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
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

private theorem homogeneous_bilinear_two_jet_bound {a k : ℝ} (B : (HomogeneousY a k) →L[ℝ] (HomogeneousY a k) →L[ℝ] (HomogeneousY a k))
    (F G : (HomogeneousY a k) → (HomogeneousY a k)) (hF : ContDiff ℝ ⊤ F) (hG : ContDiff ℝ ⊤ G)
    (R A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFb : ∀ f : (HomogeneousY a k), ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n F f‖ ≤ A)
    (hGb : ∀ f : (HomogeneousY a k), ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 → ‖iteratedFDeriv ℝ n G f‖ ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (HomogeneousY a k), ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
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

/-- All derivatives of order at most two are uniformly bounded on a homogeneous-space ball.
The proof uses the polynomial's actual bounded bilinear operations. -/
theorem exists_homogeneousOddPower_two_jet_bound (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (HomogeneousY a k), ‖f‖ ≤ R → ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (homogeneousOddPower a k ha ha1 hk m) f‖ ≤ C := by
  obtain ⟨J, hJ, hJb⟩ := homogeneous_linear_two_jet_bound (ContinuousLinearMap.id ℝ (HomogeneousY a k)) R hR
  obtain ⟨D, hD, hDb⟩ := homogeneous_linear_two_jet_bound (homogeneousConjugation a k ha ha1 hk) R hR
  induction m with
  | zero =>
      exact ⟨J, hJ, hJb⟩
  | succ m ih =>
      obtain ⟨A, hA, hAb⟩ := ih
      let B := homogeneousRealProduct a k ha ha1 hk
      let F : (HomogeneousY a k) → (HomogeneousY a k) := fun f =>
        B (homogeneousOddPower a k ha ha1 hk m f) ((homogeneousConjugation a k ha ha1 hk) f)
      have hF : ContDiff ℝ ⊤ F :=
        (B.contDiff.comp (contDiff_homogeneousOddPower a k ha ha1 hk m)).clm_apply (homogeneousConjugation a k ha ha1 hk).contDiff
      obtain ⟨C, hC, hCb⟩ := homogeneous_bilinear_two_jet_bound B (homogeneousOddPower a k ha ha1 hk m)
        (homogeneousConjugation a k ha ha1 hk) (contDiff_homogeneousOddPower a k ha ha1 hk m) (homogeneousConjugation a k ha ha1 hk).contDiff
        R A D hA hD hAb hDb
      obtain ⟨C', hC', hC'b⟩ := homogeneous_bilinear_two_jet_bound B F (fun f => f) hF contDiff_id
        R C J hC hJ hCb hJb
      exact ⟨C', hC', hC'b⟩

/-- The real Fréchet derivative of the homogeneous odd-power map is uniformly Lipschitz on balls. -/
theorem exists_homogeneousOddPower_derivative_lipschitz (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : (HomogeneousY a k), ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) f - fderiv ℝ (homogeneousOddPower a k ha ha1 hk m) g‖ ≤
        C * ‖f - g‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_homogeneousOddPower_two_jet_bound a k ha ha1 hk m R hR
  have hdiff : Differentiable ℝ (fderiv ℝ (homogeneousOddPower a k ha ha1 hk m)) :=
    (contDiff_infty_iff_fderiv.mp ((contDiff_homogeneousOddPower a k ha ha1 hk m).of_le
      (by simp))).2.differentiable (by simp)
  refine ⟨C, hC, ?_⟩
  intro f g hf hg
  apply (convex_closedBall (0 : (HomogeneousY a k)) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hdiff x)
  · intro x hx
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hCb x (by simpa using hx) 2 le_rfl
  · simpa using hg
  · simpa using hf

end DefocusingNLS

end OAI
