import OAI.NumberTheory.TotientAsymptotic.FixedCoordinateMass
import OAI.NumberTheory.TotientAsymptotic.FixedTerminalMass

namespace OAI

/-! Combine coordinate concentration with terminal decay so that the smooth
residuals can still be summed over all terminal strips. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma two_exponential_bounds {R Z A B u v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hu : R ≤ A*Z*Real.exp u) (hv : R ≤ B*Z*Real.exp v) :
    R ≤ (A+B)*Z*Real.exp ((u+v)/2) := by
  by_cases huv : u ≤ v
  · apply hu.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hZ
    · exact Real.exp_le_exp.mpr (by linarith only [huv])
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (add_nonneg hA hB) hZ
  · apply hv.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hZ
    · exact Real.exp_le_exp.mpr (by linarith only [huv])
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (add_nonneg hA hB) hZ

theorem fixed_coordinate_terminal_mass (H : ℕ) :
    ∃ C a c : ℝ,0 < C ∧ 0 < a ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ t : ℝ,0 ≤ t → ∀ Q : Finset (Fin (N+2) → ℕ),
    (∀ p∈Q,(∀ j,(p j).Prime) ∧
      primePrefixCoord p∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (1/100:ℝ) ≤ primePrefixCoord p (Fin.last (N+1)) ∧
      t ≤ primePrefixCoord p (Fin.last (N+1)) ∧
      (primePrefixCoord p i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primePrefixCoord p i)) →
    (∑ p∈Q,reciprocalShiftWeight p) ≤ C*G x (N+2)*
      Real.exp (-a*t-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,a,hA,ha,htail⟩ := fixed_terminal_prime_mass H
  obtain ⟨B,c,hB,hc,hcoord⟩ := fixed_coordinate_prime_mass H
  refine ⟨A+B,a/2,c/2,add_pos hA hB,by positivity,by positivity,?_⟩
  filter_upwards [hcoord] with P hP
  filter_upwards [hP,htail,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx ht hBx
  intro N hN i hi t ht0 Q hQ
  have h1 := ht (N+1) (by omega) t ht0 Q (by
    intro p hp
    exact ⟨(hQ p hp).1,by
      simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using (hQ p hp).2.1,
      (hQ p hp).2.2.1,(hQ p hp).2.2.2.1⟩)
  have h2 := hx N hN i hi Q (by
    intro p hp
    refine ⟨(hQ p hp).1,(hQ p hp).2.1,?_,(hQ p hp).2.2.2.2⟩
    intro j hj
    have he : j=Fin.last (N+1) := by apply Fin.ext; simp only [Fin.val_last]; omega
    simpa only [he] using (hQ p hp).2.2.1)
  have hh := two_exponential_bounds hA.le hB.le (G_pos hBx (N+2)).le h1 h2
  convert hh using 1
  congr 2
  ring

end TotientAsymptotic

end

end OAI
