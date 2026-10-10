import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximationCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusOddCommutator

namespace OAI

/-! # Compactness of the actual odd-power commutator and lower energy -/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable (a Q M : ℝ) (N : ℕ) (ha : 0 < a) (ha1 : a < 1)
  (hN : 8 < ((N + 1 : ℕ) : ℝ)) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
  (hLinf : Tendsto L atTop atTop) (q : ℕ → FourierL2)
  (hq : ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN L hL q) (hqb : ∀ n, ‖q n‖ ≤ Q)
  (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
  (hlocal : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
    ‖expandingTorusFunction a (N + 1 : ℕ) (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))‖ < ε)
  (m : ℕ) (hm : 0 < m)

include ha ha1 hN hL hlocal in
private theorem local_conjugate :
    ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a (N + 1 : ℕ) (L n) (fourierConjugate (f n))
        (euclideanToTorus ((L n)⁻¹ • y))‖ < ε := by
  intro R ε hε
  filter_upwards [hlocal R ε hε] with n hn
  intro y hy
  simpa only [expandingTorusFunction_conjugate a (N + 1 : ℕ) (L n) ha ha1 hN (hL n),
    Complex.norm_conj] using hn y hy

include hLinf hq hqb hf hlocal hm

theorem tendsto_expandingOddFourierCommutator (j : Fin (N + 1) → Fin 12) :
    Tendsto (fun n => expandingOddFourierCommutator a (L n) (N + 1) ha ha1 hN (hL n)
      m (q n) (f n) j) atTop (𝓝 0) := by
  obtain ⟨hc, hd⟩ := expandingOdd_coefficients_compact a (N + 1 : ℕ) Q ha ha1 hN
    L hL hLinf q hq hqb m hm
  have hfirst := tendsto_expandingApproximate_commutator a M N ha ha1 hN L hL hLinf _ hc f hf hlocal j
  have hconj := local_conjugate a N ha ha1 hN L hL f hlocal
  have hsecond := tendsto_expandingApproximate_commutator a M N ha ha1 hN L hL hLinf _ hd
    (fun n => fourierConjugate (f n)) (fun n => by simpa only [fourierConjugate_norm] using hf n) hconj j
  simpa only [expandingOddFourierCommutator_eq, add_zero, smul_zero] using
    (hfirst.add hsecond).const_smul (-Complex.I)

theorem tendsto_expandingLinearized_lowEnergy :
    Tendsto (fun n => expandingLowEnergy a (N + 1 : ℕ) (L n) (hL n)
      (expandingLinearizedPotential a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m (q n) (f n)))
      atTop (𝓝 0) := by
  obtain ⟨hc, hd⟩ := expandingOdd_coefficients_compact a (N + 1 : ℕ) Q ha ha1 hN
    L hL hLinf q hq hqb m hm
  have hfirst := tendsto_expandingApproximate_lowEnergy_product a M (N + 1) ha ha1 hN
    L hL hLinf _ hc f hf hlocal
  have hconj := local_conjugate a N ha ha1 hN L hL f hlocal
  have hsecond := tendsto_expandingApproximate_lowEnergy_product a M (N + 1) ha ha1 hN
    L hL hLinf _ hd (fun n => fourierConjugate (f n))
    (fun n => by simpa only [fourierConjugate_norm] using hf n) hconj
  have he (n : ℕ) : expandingLowEnergy a (N + 1 : ℕ) (L n) (hL n)
      (expandingLinearizedPotential a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m (q n) (f n)) =
      (-Complex.I) • (expandingLowEnergy a (N + 1 : ℕ) (L n) (hL n)
        (expandingProduct a (N + 1 : ℕ) (L n) ha ha1 hN (hL n)
          (expandingCircularCoefficient a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m (q n)) (f n)) +
      expandingLowEnergy a (N + 1 : ℕ) (L n) (hL n)
        (expandingProduct a (N + 1 : ℕ) (L n) ha ha1 hN (hL n)
          (expandingAnticircularCoefficient a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m (q n))
          (fourierConjugate (f n)))) := by
    change expandingLowEnergy _ _ _ _ ((-Complex.I) • fderiv ℝ
      (expandingOddPower a (N + 1 : ℕ) (L n) ha ha1 hN (hL n) m) (q n) (f n)) = _
    rw [expandingOddPower_derivative_algebra, map_smul, map_add]
  simpa only [he, add_zero, smul_zero] using (hfirst.add hsecond).const_smul (-Complex.I)

end DefocusingNLS

end OAI
