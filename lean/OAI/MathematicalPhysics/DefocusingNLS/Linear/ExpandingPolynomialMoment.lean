import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LatticeMomentAlgebra

namespace OAI

/-! # Fourier moments of the actual nonlinear coefficient fields -/

open scoped ComplexConjugate

namespace DefocusingNLS

attribute [local irreducible] expandingProduct expandingFourierCoefficient expandingPower
  expandingConstant fourierConjugate

variable (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (N : ℕ)

theorem expandingProduct_moment (q f : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q)))
    (hf : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L f))) :
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingProduct a k L ha ha1 hk hL q f))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingProduct a k L ha ha1 hk hL q f)) n) ≤
      (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n) *
      ∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L f) n := by
  have he : expandingFourierCoefficient a k L (expandingProduct a k L ha ha1 hk hL q f) =
      fun n => ∑' m, expandingFourierCoefficient a k L q m * expandingFourierCoefficient a k L f (n - m) := by
    funext n
    exact expandingProduct_coefficient a k L ha ha1 hk hL q f n
  rw [he]
  exact latticeMoment_convolution L hL N (expandingFourierCoefficient a k L q)
      (expandingFourierCoefficient a k L f) hq hf

theorem expandingScalar_moment (c : ℂ) (q : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q))) :
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L (c • q))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L (c • q)) n) =
      ‖c‖ * ∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n := by
  have he (n : frequencyLattice) :
      latticeMomentMass L N (expandingFourierCoefficient a k L (c • q)) n =
        ‖c‖ * latticeMomentMass L N (expandingFourierCoefficient a k L q) n := by
    rw [latticeMomentMass, expandingFourierCoefficient_smul, norm_mul]
    unfold latticeMomentMass
    ring
  rw [show latticeMomentMass L N (expandingFourierCoefficient a k L (c • q)) =
    (fun n => ‖c‖ * latticeMomentMass L N (expandingFourierCoefficient a k L q) n) from funext he]
  exact ⟨hq.mul_left _, tsum_mul_left⟩

theorem expandingConjugate_moment (q : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q))) :
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L (fourierConjugate q))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L (fourierConjugate q)) n) =
      ∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n := by
  have he (n : frequencyLattice) :
      latticeMomentMass L N (expandingFourierCoefficient a k L (fourierConjugate q)) n =
        latticeMomentMass L N (expandingFourierCoefficient a k L q) (-n) := by
    simp only [latticeMomentMass, expandingFourierCoefficient_conjugate, Complex.norm_conj,
      latticeMomentWeight, norm_neg]
  rw [show latticeMomentMass L N (expandingFourierCoefficient a k L (fourierConjugate q)) =
    (fun n => latticeMomentMass L N (expandingFourierCoefficient a k L q) (-n)) from funext he]
  exact ⟨(Equiv.neg frequencyLattice).summable_iff.mpr hq,
    (Equiv.neg frequencyLattice).tsum_eq _⟩

include hL in
theorem expandingConstant_moment (c : ℂ) :
    HasSum (latticeMomentMass L N (expandingFourierCoefficient a k L (expandingConstant a k L c))) ‖c‖ := by
  classical
  have he : latticeMomentMass L N (expandingFourierCoefficient a k L (expandingConstant a k L c)) =
      (fun n : frequencyLattice => if n = 0 then ‖c‖ else 0) := by
    funext n
    rw [latticeMomentMass, expandingConstant_coefficient a k L hL]
    by_cases hn : n = 0
    · subst n
      simp [latticeMomentWeight]
    · simp [hn]
  rw [he]
  exact hasSum_ite_eq 0 ‖c‖

theorem expandingPower_moment (q : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q))) (m : ℕ) :
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingPower a k L ha ha1 hk hL q m))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingPower a k L ha ha1 hk hL q m)) n) ≤
      (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n) ^ m := by
  induction m with
  | zero =>
      simp only [expandingPower]
      have h := expandingConstant_moment a k L hL N (1 : ℂ)
      exact ⟨h.summable, by simp only [h.tsum_eq, norm_one, pow_zero, le_refl]⟩
  | succ m ih =>
      simp only [expandingPower]
      obtain ⟨hs, hb⟩ := expandingProduct_moment a k L ha ha1 hk hL N q
        (expandingPower a k L ha ha1 hk hL q m) hq ih.1
      refine ⟨hs, hb.trans ?_⟩
      rw [pow_succ']
      apply mul_le_mul_of_nonneg_left ih.2
      exact tsum_nonneg (fun n => mul_nonneg
        (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _))

end DefocusingNLS

end OAI
