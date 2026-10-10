import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarPrefixCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExtension

namespace OAI

/-! # Exact accumulated lifts of a finite tuple of transitions -/

noncomputable section
namespace PolycyclicRecognition

theorem wordPrefix_succ_left {A : Type*} [Monoid A] (u : ℕ → A) (n : ℕ) :
    wordPrefix u (n + 1) = u 0 * wordPrefix (fun j => u (j + 1)) n := by
  unfold wordPrefix
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem wordPrefix_relative_transitions {G : Type*} [Group G] (y : ℕ → G) (n : ℕ) :
    wordPrefix (fun i => (y i)⁻¹ * y (i + 1)) n = (y 0)⁻¹ * y n := by
  induction n with
  | zero => simp only [wordPrefix_zero, inv_mul_cancel]
  | succ n ih => rw [wordPrefix_succ, ih]; group

theorem wordPrefix_height_bound {D W : Type*} [Group D] [NormedAddCommGroup W]
    (π : D →* Multiplicative W) (u : ℕ → D) (B : ℝ) (h : ℕ)
    (hu : ∀ i < h, ‖(π (u i)).toAdd‖ ≤ B) :
    ‖(π (wordPrefix u h)).toAdd‖ ≤ (h : ℝ) * B := by
  induction h with
  | zero => simp only [wordPrefix_zero, map_one, toAdd_one, norm_zero,
      Nat.cast_zero, zero_mul, le_refl]
  | succ h ih =>
    rw [wordPrefix_succ, map_mul, toAdd_mul]
    calc
      ‖(π (wordPrefix u h)).toAdd + (π (u h)).toAdd‖ ≤
          ‖(π (wordPrefix u h)).toAdd‖ + ‖(π (u h)).toAdd‖ := norm_add_le _ _
      _ ≤ (h : ℝ) * B + B := add_le_add (ih (fun i hi => hu i (Nat.lt_succ_of_lt hi)))
        (hu h (Nat.lt_succ_self h))
      _ = ((h + 1 : ℕ) : ℝ) * B := by rw [Nat.cast_add, Nat.cast_one]; ring

/-- The tuple positions with the identity adjoined at time zero. -/
def basedTuplePosition {G : Type*} [One G] {h : ℕ} (x : Fin h → G) (j : ℕ) : G :=
  if j = 0 then 1 else if hi : j - 1 < h then x ⟨j - 1, hi⟩ else 1

@[simp] theorem basedTuplePosition_zero {G : Type*} [One G] {h : ℕ} (x : Fin h → G) :
    basedTuplePosition x 0 = 1 := by simp [basedTuplePosition]

@[simp] theorem basedTuplePosition_succ {G : Type*} [One G] {h : ℕ}
    (x : Fin h → G) (i : Fin h) : basedTuplePosition x (i.val + 1) = x i := by
  simp [basedTuplePosition, i.isLt]

variable {N D G : Type*} [Group N] [Group D] [Group G]

theorem cartan_word_prefix_identity (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u : ℕ → N) (d : ℕ → D) (m : ℕ) :
    ι (wordPrefix (fun i => φ (wordPrefix d i) (u i)) m) * κ (wordPrefix d m) =
      wordPrefix (fun i => ι (u i) * κ (d i)) m := by
  induction m with
  | zero => simp only [wordPrefix_zero, map_one, mul_one]
  | succ m ih =>
    rw [wordPrefix_succ, wordPrefix_succ d, map_mul, map_mul, hc,
      wordPrefix_succ]
    rw [← ih]
    group

variable [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

theorem prefixCoordinateEquiv_eq_wordPrefix (u : ℕ → N) (h : ℕ) (i : Fin h) :
    prefixCoordinateEquiv h (fun j => u j.val) i = wordPrefix u (i.val + 1) := by
  induction h generalizing u with
  | zero => exact Fin.elim0 i
  | succ h ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [prefixCoordinateEquiv_zero, Fin.val_zero, wordPrefix_succ_left,
        wordPrefix_zero, mul_one]
    · rw [prefixCoordinateEquiv_succ]
      change u 0 * prefixCoordinateEquiv h (fun k => u (k.val + 1)) j = _
      rw [ih (fun k => u (k + 1)) j]
      exact (wordPrefix_succ_left u (j.val + 1)).symm

theorem prefixCoordinateEquiv_symm_wordPrefix (u : ℕ → N) (h : ℕ) :
    (prefixCoordinateEquiv h).symm (fun i => wordPrefix u (i.val + 1)) = fun i => u i.val := by
  apply (prefixCoordinateEquiv h).injective
  rw [MeasurableEquiv.apply_symm_apply]
  funext i
  exact (prefixCoordinateEquiv_eq_wordPrefix u h i).symm

theorem tuple_accumulated_cartan_lifts (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    (u : ℕ → N) (d : ℕ → D) (h : ℕ) :
    ∀ i : Fin h,
      ι (prefixCoordinateEquiv h (fun j => φ (wordPrefix d j.val) (u j.val)) i) *
        κ (wordPrefix d (i.val + 1)) =
          wordPrefix (fun j => ι (u j) * κ (d j)) (i.val + 1) := by
  intro i
  rw [prefixCoordinateEquiv_eq_wordPrefix (fun j => φ (wordPrefix d j) (u j)) h i]
  exact cartan_word_prefix_identity ι κ φ hc u d (i.val + 1)

/-- Individual lifts of the successive relative transitions reproduce the
entire tuple, with the required conjugations by preceding Cartan prefixes. -/
theorem tuple_accumulated_lifts_eq (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N)
    (hc : ∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹)
    {h : ℕ} (x : Fin h → G) (u : ℕ → N) (d : ℕ → D)
    (hprod : ∀ j < h, ι (u j) * κ (d j) =
      (basedTuplePosition x j)⁻¹ * basedTuplePosition x (j + 1)) :
    ∀ i : Fin h,
      ι (prefixCoordinateEquiv h (fun j => φ (wordPrefix d j.val) (u j.val)) i) *
        κ (wordPrefix d (i.val + 1)) = x i := by
  intro i
  rw [tuple_accumulated_cartan_lifts ι κ φ hc u d]
  calc
    wordPrefix (fun j => ι (u j) * κ (d j)) (i.val + 1) =
        wordPrefix (fun j => (basedTuplePosition x j)⁻¹ *
          basedTuplePosition x (j + 1)) (i.val + 1) :=
      wordPrefix_congr _ (fun j hj => hprod j (hj.trans_le i.isLt))
    _ = (basedTuplePosition x 0)⁻¹ * basedTuplePosition x (i.val + 1) :=
      wordPrefix_relative_transitions _ _
    _ = x i := by rw [basedTuplePosition_zero, basedTuplePosition_succ, inv_one, one_mul]

end PolycyclicRecognition

end

end OAI
