import OAI.NumberTheory.Ostmann.Characters.SquareAverage
import OAI.NumberTheory.Ostmann.Characters.BottomPairMellin
import OAI.NumberTheory.Ostmann.Characters.AffineAction

namespace OAI

/-!
# Density of one tree split

Given the parent difference, a split coordinate produces the child ratio
as a fixed unit times its inverse square. Each valid child pair therefore
has multiplicity at most two. Zero weights at zero discard invalid nodes.
-/

namespace Ostmann

open scoped BigOperators

/-- A full-field sum in ratio coordinates is exactly the difference convolution. -/
theorem pair_ratio_sum_eq {p : ℕ} [Fact p.Prime]
    (d : (ZMod p)ˣ) (f g : ZMod p → ℝ) (hf : f 0 = 0) (hg : g 0 = 0) :
    (∑ t : (ZMod p)ˣ, if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) =
      ∑ x : ZMod p, f x * g (x - d) := by
  classical
  let H : ZMod p → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * t / (t - 1)) * g ((d : ZMod p) / (t - 1))
  have hH0 : H 0 = 0 := by simp [H, hf]
  have hunit (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        g ((d : ZMod p) / ((t : ZMod p) - 1))) = H t := by
    have ht : (t : ZMod p) = 1 ↔ t = 1 := by
      constructor
      · intro h; exact Units.ext h
      · intro h; simp [h]
    simp only [H, ht]
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (d : ZMod p) (Units.ne_zero d))
  have he (t : ZMod p) : H t = f (e t) * g (e t - d) := by
    change H t = f ((d : ZMod p) * ratioInvolution t) *
      g ((d : ZMod p) * ratioInvolution t - d)
    by_cases ht : t = 1
    · simp [H, ratioInvolution, ht, hg]
    · have hdif : (d : ZMod p) * t / (t - 1) - d =
          (d : ZMod p) / (t - 1) := by
        have h := pair_coordinate_difference (d : ZMod p) t ht
        linear_combination h
      simp only [H, ht, ite_false, ratioInvolution, ← mul_div_assoc, hdif]
  simp_rw [hunit]
  rw [sum_units_eq_sum_of_zero H hH0]
  simp_rw [he]
  exact e.bijective.sum_comp (fun x => f x * g (x - d))

/-- Counting form of the conditional density bound at one internal node. -/
theorem pair_inverse_square_density {p : ℕ} [Fact p.Prime]
    (d K : (ZMod p)ˣ) (f g : ZMod p → ℝ)
    (hf : f 0 = 0) (hg : g 0 = 0)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∑ m : (ZMod p)ˣ,
      let t := K * (m⁻¹) ^ 2
      if t = 1 then 0 else
        f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
          g ((d : ZMod p) / ((t : ZMod p) - 1))) ≤
      2 * ∑ x : ZMod p, f x * g (x - d) := by
  let H : (ZMod p)ˣ → ℝ := fun t => if t = 1 then 0 else
    f ((d : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
      g ((d : ZMod p) / ((t : ZMod p) - 1))
  have hn (t : (ZMod p)ˣ) : 0 ≤ H t := by
    dsimp [H]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hfn _) (hgn _)
  have h := sum_inverse_square_coset_le_twice K H hn
  rw [show (∑ t : (ZMod p)ˣ, H t) = ∑ x : ZMod p, f x * g (x - d) from
    pair_ratio_sum_eq d f g hf hg] at h
  exact h

end Ostmann

end OAI
