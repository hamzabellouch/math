import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevConvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDerivatives
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! # Sobolev multiplication agrees with pointwise multiplication on the torus -/

namespace DefocusingNLS

theorem frequencyCoordinates_add (m n : frequencyLattice) (j : Fin 12) :
    frequencyCoordinates (m + n) j = frequencyCoordinates m j + frequencyCoordinates n j := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_add, frequencyCoordinates_coe]
  rfl

theorem torusCharacter_frequency_add (m n : frequencyLattice) (x : SchrodingerTorus) :
    torusCharacter (m + n) x = torusCharacter m x * torusCharacter n x := by
  change (∏ j, fourier (frequencyCoordinates (m + n) j) (x j)) = _
  simp only [frequencyCoordinates_add, fourier_add]
  exact Finset.prod_mul_distrib

/-- The additive shear used to collect terms of a double Fourier series. -/
noncomputable def frequencySumEquiv : frequencyLattice × frequencyLattice ≃
    frequencyLattice × frequencyLattice where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv p := by rcases p with ⟨a,b⟩; ext <;> simp
  right_inv p := by rcases p with ⟨a,b⟩; ext <;> simp

/-- Collect an absolutely convergent double series by the sum of its frequencies. -/
theorem tsum_frequency_convolution (a b : frequencyLattice → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    (∑' n, a n) * (∑' n, b n) = ∑' n, ∑' m, a m * b (n - m) := by
  let D : frequencyLattice × frequencyLattice → ℂ := fun p => a p.1 * b p.2
  let C : frequencyLattice × frequencyLattice → ℂ := fun p => a p.2 * b (p.1 - p.2)
  have heq : D = C ∘ frequencySumEquiv := by
    funext p
    change a p.1 * b p.2 = a p.1 * b (p.1 + p.2 - p.1)
    rw [add_sub_cancel_left]
  have hD : Summable D := summable_mul_of_summable_norm ha hb
  have hC : Summable C := frequencySumEquiv.summable_iff.mp (heq ▸ hD)
  calc
    _ = ∑' p, D p := tsum_mul_tsum_of_summable_norm ha hb
    _ = ∑' p, C p := by rw [heq]; exact frequencySumEquiv.tsum_eq C
    _ = ∑' n, ∑' m, C (n,m) := hC.tsum_prod

/-- The absolutely convergent Fourier Cauchy product on the actual torus. -/
theorem tsum_fourier_product (a b : frequencyLattice → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖))
    (x : SchrodingerTorus) :
    (∑' n, a n * torusCharacter n x) * (∑' n, b n * torusCharacter n x) =
      ∑' n, (∑' m, a m * b (n - m)) * torusCharacter n x := by
  have ha' : Summable (fun n => ‖a n * torusCharacter n x‖) := by simpa using ha
  have hb' : Summable (fun n => ‖b n * torusCharacter n x‖) := by simpa using hb
  rw [tsum_frequency_convolution _ _ ha' hb']
  apply tsum_congr
  intro n
  rw [← tsum_mul_right]
  apply tsum_congr
  intro m
  have hchar : torusCharacter m x * torusCharacter (n - m) x = torusCharacter n x := by
    rw [← torusCharacter_frequency_add, add_sub_cancel]
  calc
    _ = (a m * b (n - m)) * (torusCharacter m x * torusCharacter (n - m) x) := by ring
    _ = _ := by rw [hchar]

lemma sobolevTorusFunction_eq_tsum (k : ℝ) (hk : 6 < k) (f : FourierL2)
    (x : SchrodingerTorus) :
    sobolevTorusFunction k f x =
      ∑' n, sobolevFourierCoefficient k f n * torusCharacter n x := by
  rw [sobolevTorusFunction_apply k hk]
  exact (hasSum_sobolevPointEvaluation k hk x f).tsum_eq.symm

/-- The bounded Sobolev product is exactly the usual product of torus functions. -/
theorem sobolevTorusFunction_product (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    sobolevTorusFunction k (sobolevProduct k hk f g) =
      sobolevTorusFunction k f * sobolevTorusFunction k g := by
  ext x
  simp only [ContinuousMap.mul_apply, sobolevTorusFunction_eq_tsum k hk,
    sobolevProduct_coefficient]
  exact (tsum_fourier_product (sobolevFourierCoefficient k f) (sobolevFourierCoefficient k g)
    (summable_norm_sobolevFourierCoefficient k hk f)
    (summable_norm_sobolevFourierCoefficient k hk g) x).symm

lemma sobolevFourierCoefficient_add (k : ℝ) (f g : FourierL2) (n : frequencyLattice) :
    sobolevFourierCoefficient k (f + g) n =
      sobolevFourierCoefficient k f n + sobolevFourierCoefficient k g n := by
  simp only [sobolevFourierCoefficient, lp.coeFn_add, Pi.add_apply, smul_add]

lemma sobolevFourierCoefficient_smul (k : ℝ) (c : ℂ) (f : FourierL2) (n : frequencyLattice) :
    sobolevFourierCoefficient k (c • f) n = c * sobolevFourierCoefficient k f n := by
  simp only [sobolevFourierCoefficient, lp.coeFn_smul, Pi.smul_apply, Algebra.smul_def]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

lemma summable_sobolevProductTerms (k : ℝ) (hk : 6 < k) (f g : FourierL2)
    (n : frequencyLattice) : Summable (fun m =>
      sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m)) := by
  apply Summable.of_norm
  simpa only [norm_mul] using summable_norm_sobolevProductTerms k hk f g n

theorem sobolevProduct_comm (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    sobolevProduct k hk f g = sobolevProduct k hk g f := by
  ext n
  change (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n =
    (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k g f n
  congr 1
  unfold sobolevProductCoefficient
  rw [← (Equiv.subLeft n).tsum_eq (fun m =>
    sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m))]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, mul_comm]

theorem sobolevProduct_add_left (k : ℝ) (hk : 6 < k) (f g h : FourierL2) :
    sobolevProduct k hk (f + g) h = sobolevProduct k hk f h + sobolevProduct k hk g h := by
  ext n
  change (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k (f + g) h n =
    (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f h n +
      (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k g h n
  unfold sobolevProductCoefficient
  simp only [sobolevFourierCoefficient_add, add_mul]
  rw [(summable_sobolevProductTerms k hk f h n).tsum_add
    (summable_sobolevProductTerms k hk g h n)]
  ring

theorem sobolevProduct_smul_left (k : ℝ) (hk : 6 < k) (c : ℂ) (f g : FourierL2) :
    sobolevProduct k hk (c • f) g = c • sobolevProduct k hk f g := by
  ext n
  change (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k (c • f) g n =
    c * ((sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n)
  unfold sobolevProductCoefficient
  simp only [sobolevFourierCoefficient_smul, mul_assoc, tsum_mul_left]
  ring

theorem sobolevProduct_add_right (k : ℝ) (hk : 6 < k) (f g h : FourierL2) :
    sobolevProduct k hk f (g + h) = sobolevProduct k hk f g + sobolevProduct k hk f h := by
  rw [sobolevProduct_comm k hk f (g + h), sobolevProduct_add_left,
    sobolevProduct_comm k hk g f, sobolevProduct_comm k hk h f]

theorem sobolevProduct_smul_right (k : ℝ) (hk : 6 < k) (c : ℂ) (f g : FourierL2) :
    sobolevProduct k hk f (c • g) = c • sobolevProduct k hk f g := by
  rw [sobolevProduct_comm k hk f (c • g), sobolevProduct_smul_left, sobolevProduct_comm k hk g f]

/-- The usual torus product is a continuous complex-bilinear operation in `H^k`. -/
noncomputable def sobolevBilinearProduct (k : ℝ) (hk : 6 < k) :
    FourierL2 →L[ℂ] FourierL2 →L[ℂ] FourierL2 :=
  (LinearMap.mk₂ ℂ (sobolevProduct k hk)
    (sobolevProduct_add_left k hk) (sobolevProduct_smul_left k hk)
    (sobolevProduct_add_right k hk) (sobolevProduct_smul_right k hk)).mkContinuous₂
      (2 * 4 ^ (k / 2) * ‖sobolevObservationVector k hk‖) (sobolevProduct_norm_le k hk)

@[simp] theorem sobolevBilinearProduct_apply (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    sobolevBilinearProduct k hk f g = sobolevProduct k hk f g := rfl

end DefocusingNLS

end OAI
