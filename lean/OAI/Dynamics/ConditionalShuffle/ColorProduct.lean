import OAI.Dynamics.ConditionalShuffle.ColorSplit

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp Thorp.Conditional Revealed.Disintegration

theorem conditional_product (d : ℕ) (h : Coloring d) (t : ℕ) (c : History (d+1) t)
    {A C G K : Type} [Fintype G] [Fintype K] [Nonempty G] [Nonempty K]
    (a : A → Position (d+1)) (b : C → Position (d+1))
    (ha : ∀ i, h (a i) = true) (hb : ∀ i, h (b i) = false)
    (f : State (d+1) → G) (g : State (d+1) → K)
    (hf : ∀ P Q, (∀ i, P (a i) = Q (a i)) → f P = f Q)
    (hg : ∀ P Q, (∀ i, P (b i) = Q (b i)) → g P = g Q) (x : G) (y : K) :
    conditional (fairMass (fun ω : History (d+1) t =>
      (occupancy d h t ω,(f (run (d+1) t ω),g (run (d+1) t ω))))) (occupancy d h t c) (x,y) =
    conditional (fairMass (fun ω : History (d+1) t =>
      (occupancy d h t ω,f (run (d+1) t ω)))) (occupancy d h t c) x *
    conditional (fairMass (fun ω : History (d+1) t =>
      (occupancy d h t ω,g (run (d+1) t ω)))) (occupancy d h t c) y := by
  let fa : History (d+1) t → G := fun r => f (run (d+1) t (resampleTwo d h t c r c))
  let gb : History (d+1) t → K := fun r => g (run (d+1) t (resampleTwo d h t c c r))
  have hfa (r s : History (d+1) t) : f (run (d+1) t (resampleTwo d h t c r s)) = fa r := by
    apply hf; intro i
    exact resampleTwo_A d h t c r s c (a i) (ha i)
  have hgb (r s : History (d+1) t) : g (run (d+1) t (resampleTwo d h t c r s)) = gb s := by
    apply hg; intro i
    exact resampleTwo_C d h t c r c s (b i) (hb i)
  have hj := conditional_two_arrays d h t c (fun ω => (f (run (d+1) t ω),g (run (d+1) t ω)))
  simp_rw [hfa, hgb] at hj
  have h₁ : fairMass fa = conditional (fairMass (fun ω : History (d+1) t =>
      (occupancy d h t ω,f (run (d+1) t ω)))) (occupancy d h t c) := by
    rw [← conditional_two_arrays d h t c (fun ω => f (run (d+1) t ω))]
    funext z
    rw [fairMass_eq_mean, fairMass_eq_mean, mean_prod]
    simp_rw [hfa, mean_const]
  have h₂ : fairMass gb = conditional (fairMass (fun ω : History (d+1) t =>
      (occupancy d h t ω,g (run (d+1) t ω)))) (occupancy d h t c) := by
    rw [← conditional_two_arrays d h t c (fun ω => g (run (d+1) t ω))]
    funext z
    rw [fairMass_eq_mean, fairMass_eq_mean, mean_prod]
    simp_rw [hgb, mean_const]
  rw [← hj, ← h₁, ← h₂]
  exact fairMass_prod fa gb x y

end Revealed.Color

end

end OAI
