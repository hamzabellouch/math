import OAI.Analysis.Cotype.OddPatternBounds
import OAI.Analysis.Cotype.ProjectionCoefficients

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {α : Type*} [Fintype α]

theorem average_mul_left (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := average_const_smul c f

theorem average_mul_right (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := average_smul_const f c

theorem average_add_real (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub_real (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_div_real (f : α → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simp only [div_eq_mul_inv, average_mul_right]

theorem average_const_real [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  simp [average]

theorem abs_average_le_const [Nonempty α] (f : α → ℝ) {M : ℝ}
    (hf : ∀ a, |f a| ≤ M) : |average f| ≤ M := by
  calc
    _ ≤ average (fun a => |f a|) := by simpa only [Real.norm_eq_abs] using norm_average_le f
    _ ≤ average (fun _ : α => M) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hf a)) (by positivity)
    _ = M := average_const_real M

theorem average_coordinate {m : ℕ} (i : Fin m) (F : Bool → ℝ) :
    average (fun ε : Cube m => F (ε i)) = (F false + F true) / 2 := by
  have hn := average_negate (fun ε : Cube m => F (ε i))
  have hs : average (fun ε : Cube m => F (ε i) + F (!(ε i))) = F false + F true := by
    calc
      _ = average (fun _ : Cube m => F false + F true) := by
        congr 1; funext ε; cases ε i <;> simp [add_comm]
      _ = _ := average_const_real _
  rw [average_add_real] at hs
  change average (fun ε : Cube m => F (!(ε i))) = _ at hn
  rw [hn] at hs
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem xorCube_negate_right (a b : ι → Bool) :
    xorCube a (negateCube b) = negateCube (xorCube a b) := by
  funext i; simp [xorCube, negateCube]

omit [Fintype ι] [DecidableEq ι] in
theorem xorCube_negate_left (a b : ι → Bool) :
    xorCube (negateCube a) b = negateCube (xorCube a b) := by
  funext i; simp [xorCube, negateCube]

def vectorTwist {m : ℕ} (φ : Cube m → Cube m → ℝ) (s : Cube m) : ℝ :=
  average (fun ε => φ (xorCube ε s) ε)

def matrixTwist {m : ℕ} (Φ : SignMatrix m → Cube m → Cube m → ℝ) (S : SignMatrix m) : ℝ :=
  average (fun ε => average (fun δ => Φ (dampedSample ε δ S) ε δ))

theorem oddPart_vectorTwist {m : ℕ} (φ : Cube m → Cube m → ℝ) (s : Cube m) :
    oddPart (vectorTwist φ) s = average (fun ε => oddPart (fun s => φ s ε) (xorCube ε s)) := by
  simp only [oddPart, vectorTwist, xorCube_negate_right, average_div_real, average_sub_real]

theorem oddPart_matrixTwist {m : ℕ} (Φ : SignMatrix m → Cube m → Cube m → ℝ) (S : SignMatrix m) :
    oddPart (matrixTwist Φ) S =
      average (fun ε => average (fun δ => oddPart (fun S => Φ S ε δ) (dampedSample ε δ S))) := by
  simp only [oddPart, matrixTwist, dampedSample, xorCube_negate_right,
    average_div_real, average_sub_real]

theorem fourier_average_family (F : α → (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun s => average (fun a => F a s)) p = average (fun a => fourier (F a) p) := by
  simp only [fourier, ← average_mul_right]
  rw [average_comm]

theorem vectorTwist_first_coefficient {m : ℕ} (φ : Cube m → Cube m → ℝ)
    (c : ℝ) (hm : ∀ s i, moment ℝ (φ s) i = c * sign (s i)) (i : Fin m) :
    fourier (oddPart (vectorTwist φ)) (unitIndex i) = c := by
  rw [oddPart_preserves_odd_coefficient _ (by simp [paritySign, unitIndex])]
  unfold vectorTwist
  rw [fourier_average_family]
  have ht (ε : Cube m) : fourier (fun s => φ (xorCube ε s) ε) (unitIndex i) =
      fourier (fun s => φ s ε) (unitIndex i) * sign (ε i) := by
    exact (fourier_translate (fun s => φ s ε) ε (unitIndex i)).trans (by rw [character_unitIndex])
  simp_rw [ht]
  simp only [fourier, character_unitIndex, ← average_mul_right]
  rw [average_comm]
  have he (s : Cube m) : average (fun ε => φ s ε * sign (s i) * sign (ε i)) = c := by
    calc
      _ = sign (s i) * moment ℝ (φ s) i := by
        simp only [moment, smul_eq_mul, ← average_mul_left]
        congr 1; funext ε; ring
      _ = c := by rw [hm, mul_left_comm, sign_sq, mul_one]
  simp_rw [he]
  exact average_const_real c

end Cotype

end

end OAI
