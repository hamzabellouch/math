import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalCutoffTail

namespace OAI

/-! Uniform H1 graph bounds for actual orbitals and their removed tails. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def positionGraphSquare (f : Position → ℝ) : ℝ :=
  (∫ x, f x^2)+∑ k : Fin 3, ∫ x, (fderiv ℝ f x (EuclideanSpace.single k 1))^2

theorem positionGraphSquare_nonnegative (f : Position → ℝ) : 0 ≤ positionGraphSquare f :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

theorem continuumLocalizedMode_graph_uniform (freq : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u, positionGraphSquare (continuumLocalizedMode freq u) ≤ B := by
  refine ⟨positionGraphSquare (continuumLocalizedMode freq 0)+1,by
    linarith [positionGraphSquare_nonnegative (continuumLocalizedMode freq 0)],?_⟩
  intro u
  have he : positionGraphSquare (continuumLocalizedMode freq u) =
      positionGraphSquare (continuumLocalizedMode freq 0) := by
    unfold positionGraphSquare
    simp_rw [continuumLocalizedMode_translate freq u,continuumLocalizedMode_deriv_translate freq u]
    rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => continuumLocalizedMode freq 0 x^2) (planarCenter u)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_sub_right_eq_self (μ := volume) (fun x : Position => (fderiv ℝ (continuumLocalizedMode freq 0) x (EuclideanSpace.single k 1))^2) (planarCenter u)]
  rw [he]
  linarith

theorem orbitalRemainder_graph_bound {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u,
      positionGraphSquare (orbitalRemainder freq R u) ≤ B/R^24 := by
  obtain ⟨D,_hD,hd⟩ := orbitalRemainder_deriv_tail hfreq
  let M := ∫ x, ‖x‖^24*continuumLocalizedMode freq 0 x^2
  let A (k : Fin 3) := ∫ x, ‖x‖^24*(fderiv ℝ (continuumLocalizedMode freq 0) x
    (EuclideanSpace.single k 1))^2
  let B := 1+M+∑ k : Fin 3, 2*(D^2*M+A k)
  have hM : 0 ≤ M := integral_nonneg (fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hA (k : Fin 3) : 0 ≤ A k := integral_nonneg (fun _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hsum : 0 ≤ ∑ k : Fin 3, 2*(D^2*M+A k) := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (sq_nonneg D) hM) (hA k)))
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro R hR u
  have hR0 : 0 < R := by linarith
  have hm : (∫ x, orbitalRemainder freq R u x^2) ≤ M/R^24 :=
    (orbitalCutoff_value_tail hfreq hR0 u).2
  have hgrad (k : Fin 3) :
      (∫ x, (fderiv ℝ (orbitalRemainder freq R u) x (EuclideanSpace.single k 1))^2) ≤
        2*(D^2*M+A k)/R^24 := by
    simpa only [PiLp.norm_single,norm_one,mul_one,M,A] using
      (hd R hR u (EuclideanSpace.single k 1)).2
  calc
    _ ≤ M/R^24+∑ k : Fin 3, 2*(D^2*M+A k)/R^24 := add_le_add hm (Finset.sum_le_sum (fun k _ => hgrad k))
    _ = (M+∑ k : Fin 3, 2*(D^2*M+A k))/R^24 := by rw [add_div,Finset.sum_div]
    _ ≤ B/R^24 := div_le_div_of_nonneg_right (by dsimp [B]; linarith) (by positivity)

end ContinuumCoulomb

end

end OAI
