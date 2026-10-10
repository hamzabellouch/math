import OAI.Analysis.OInfinity.ZeroCornerRows
import OAI.Analysis.OInfinity.BergRotation

namespace OAI

/-! # Finite stabilization in a coisometric two-generator corner

Splitting one range gives three branches. Folding the first two branches
back into one gives another coisometric pair. This is the algebraic step
behind a bounded rotation contraction of a compressed unitary. The corner
unit stays `q`; no assertion removes its ambient complement.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def cornerThreeBranch (a b : E) : Fin 3 → E := ![a, b * a, b * b]

def cornerPairFold (a b : E) : E := a * star a + (b * a) * star b

variable (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
  (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
  (hsum : a * star a + b * star b = q)

include hqstar hqq haa hbb hab hsum in
lemma cornerThreeBranch_gram (i j : Fin 3) :
    star (cornerThreeBranch a b i) * cornerThreeBranch a b j = if i = j then q else 0 := by
  have hs := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have he : cornerThreeBranch a b = zeroCornerRow q b a 2 := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · change b * b = b * (b * q)
      rw [hs.2.2.2]
  rw [he]
  exact zeroCornerRow_gram q b a hqstar hqq hbb haa hba hs.2.2.1 hs.1 hs.2.1 2 i j

include hqstar hqq haa hbb hab hsum in
lemma cornerThreeBranch_sum :
    a * star a + (b * a) * star (b * a) + (b * b) * star (b * b) = q := by
  have hs := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  calc
    _ = a * star a + b * (a * star a + b * star b) * star b := by
      simp only [star_mul]
      noncomm_ring
    _ = q := by rw [hsum, hs.2.2.2, hsum]

include hqstar hqq haa hbb hab hsum in
lemma cornerPairFold_properties :
    star (cornerPairFold a b) * cornerPairFold a b = q ∧
      star (b * b) * (b * b) = q ∧
      star (cornerPairFold a b) * (b * b) = 0 ∧
      cornerPairFold a b * star (cornerPairFold a b) + (b * b) * star (b * b) = q := by
  have hs := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hf : star (b * a) * (b * a) = q := by
    simpa [cornerThreeBranch] using
      cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 1 1
  have hg : star (b * b) * (b * b) = q := by
    simpa [cornerThreeBranch] using cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 2 2
  have haf : star a * (b * a) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hfa : star (b * a) * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star haf
  have hag : star a * (b * b) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hfg : star (b * a) * (b * b) = 0 := by
    simpa [cornerThreeBranch] using cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 1 2
  have hfq : (b * a) * q = b * a := by rw [mul_assoc, hs.2.1]
  refine ⟨?_, hg, ?_, ?_⟩
  · unfold cornerPairFold
    rw [star_add, star_mul, star_mul, star_star, star_star]
    calc
      _ = a * (star a * a) * star a + a * (star a * (b * a)) * star b +
          b * (star (b * a) * a) * star a + b * (star (b * a) * (b * a)) * star b := by
        simp only [star_mul]
        noncomm_ring
      _ = q := by rw [haa, haf, hfa, hf]; simp only [mul_zero, zero_mul, add_zero,
        hs.2.1, hs.2.2.2]; exact hsum
  · unfold cornerPairFold
    rw [star_add, star_mul, star_mul, star_star, star_star, add_mul]
    calc
      _ = a * (star a * (b * b)) + b * (star (b * a) * (b * b)) := by
        simp only [star_mul]
        noncomm_ring
      _ = 0 := by rw [hag, hfg, mul_zero, mul_zero, add_zero]
  · have hv : cornerPairFold a b * star (cornerPairFold a b) =
        a * star a + (b * a) * star (b * a) := by
      unfold cornerPairFold
      rw [star_add, star_mul, star_mul, star_star, star_star]
      calc
        _ = a * (star a * a) * star a + a * (star a * b) * star (b * a) +
            (b * a) * (star b * a) * star a + (b * a) * (star b * b) * star (b * a) := by
          simp only [star_mul]
          noncomm_ring
        _ = _ := by rw [haa, hab, hba, hbb, hs.2.1, hfq]; simp
    rw [hv]
    exact cornerThreeBranch_sum q a b hqstar hqq haa hbb hab hsum

private lemma corner_sandwich_norm_le (e f x : E) (δ : ℝ) (hδ : 0 ≤ δ)
    (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1) (hx : ‖x‖ ≤ δ) : ‖e * x * star f‖ ≤ δ := by
  calc
    _ ≤ (‖e‖ * ‖x‖) * ‖f‖ := by
      calc
        _ ≤ ‖e * x‖ * ‖star f‖ := norm_mul_le _ _
        _ ≤ (‖e‖ * ‖x‖) * ‖f‖ := by rw [norm_star]; gcongr; exact norm_mul_le _ _
    _ ≤ (1 * δ) * 1 := by gcongr
    _ = δ := by ring

/-- Folding errors are controlled by the two source commutators, independently
of the ambient algebra or the unitary's path length. -/
lemma cornerPairFold_conjugation_error (q a b e f z : E)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (hqz : q * z = z) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (haz : ‖z * a - a * z‖ ≤ δ) (hbz : ‖z * b - b * z‖ ≤ δ) :
    ‖(e * star a + f * star b) * z * star (e * star a + f * star b) -
      (e * z * star e + f * z * star f)‖ ≤ 4 * δ := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  let x := star a * (z * a - a * z)
  let y := star a * (z * b - b * z)
  let u := star b * (z * a - a * z)
  let v := star b * (z * b - b * z)
  have hx : x = star a * z * a - z := by
    dsimp only [x]
    rw [mul_sub, ← mul_assoc, ← mul_assoc, haa, hqz]
  have hy : y = star a * z * b := by
    dsimp only [y]
    rw [mul_sub, ← mul_assoc, ← mul_assoc, hab, zero_mul, sub_zero]
  have hu : u = star b * z * a := by
    dsimp only [u]
    rw [mul_sub, ← mul_assoc, ← mul_assoc, hba, zero_mul, sub_zero]
  have hv : v = star b * z * b - z := by
    dsimp only [v]
    rw [mul_sub, ← mul_assoc, ← mul_assoc, hbb, hqz]
  have hdecomp : (e * star a + f * star b) * z * star (e * star a + f * star b) -
      (e * z * star e + f * z * star f) =
        e * x * star e + e * y * star f + f * u * star e + f * v * star f := by
    rw [hx, hy, hu, hv]
    simp only [star_add, star_mul, star_star]
    noncomm_ring
  have hxn : ‖x‖ ≤ δ := (norm_mul_le _ _).trans (by
    rw [norm_star]
    calc ‖a‖ * ‖z * a - a * z‖ ≤ 1 * δ := by gcongr
         _ = δ := one_mul _)
  have hyn : ‖y‖ ≤ δ := (norm_mul_le _ _).trans (by
    rw [norm_star]
    calc ‖a‖ * ‖z * b - b * z‖ ≤ 1 * δ := by gcongr
         _ = δ := one_mul _)
  have hun : ‖u‖ ≤ δ := (norm_mul_le _ _).trans (by
    rw [norm_star]
    calc ‖b‖ * ‖z * a - a * z‖ ≤ 1 * δ := by gcongr
         _ = δ := one_mul _)
  have hvn : ‖v‖ ≤ δ := (norm_mul_le _ _).trans (by
    rw [norm_star]
    calc ‖b‖ * ‖z * b - b * z‖ ≤ 1 * δ := by gcongr
         _ = δ := one_mul _)
  rw [hdecomp]
  calc
    _ ≤ ‖e * x * star e + e * y * star f + f * u * star e‖ + ‖f * v * star f‖ := norm_add_le _ _
    _ ≤ (‖e * x * star e + e * y * star f‖ + ‖f * u * star e‖) + ‖f * v * star f‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖e * x * star e‖ + ‖e * y * star f‖) + ‖f * u * star e‖) + ‖f * v * star f‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((δ + δ) + δ) + δ := by
      gcongr
      · exact corner_sandwich_norm_le e e x δ hδ he he hxn
      · exact corner_sandwich_norm_le e f y δ hδ he hf hyn
      · exact corner_sandwich_norm_le f e u δ hδ hf he hun
      · exact corner_sandwich_norm_le f f v δ hδ hf hf hvn
    _ = 4 * δ := by ring

end WeakPureInfiniteness

end

end OAI
