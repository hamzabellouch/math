import OAI.Analysis.Laughlin.ThreeBody.TraceReadout

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem phasedThreeDescendant_quadratic (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    dotProduct (phasedThreeDescendant Q hQ z n) (M *ᵥ phasedThreeDescendant Q hQ z n) =
      dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n)
        (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n) := by
  simp only [phasedThreeDescendant,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have hs : ((-1 : ℝ)^z.val)^2=1 := by rw [← pow_mul,mul_comm z.val 2,pow_mul]; norm_num
  nlinarith only [congrArg (fun s : ℝ => s * dotProduct
    (normalizedCoupledDescendant Q z.val hQ (by omega) n)
    (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n)) hs]

noncomputable def physicalThreeBodyLevel (Q z T t : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) : ℝ :=
  let a := threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z T t entries
  2*((ell : ℝ)/10^7)*physicalCouplingCoefficient (2*Q-2) Q z T t*a+a^2

theorem threeBodyLevelMatrix_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n)
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z n) = 0 := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant_off Q hQ z n t T entries h]
  ring

theorem threeBodyLevelMatrix_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) (ht : t ≤ T) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val))
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z (T-z.val)) =
      physicalThreeBodyLevel Q z.val T t ell entries := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant Q hQ z t T entries hz hT,
    pairOrbitalUnit_dot Q t (T-t) (by omega) (by omega),
    phasedThreeDescendant_at_level Q hQ z T t (T-t) hz hT (by omega)]
  rfl

theorem threeBodyLevelMatrix_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hT : T ≤ Q) (ht : t ≤ T) :
    Matrix.trace (threeSpinProjector Q hQ z * threeBodyLevelMatrix Q t T ell entries) =
      if z.val ≤ T then physicalThreeBodyLevel Q z.val T t ell entries else 0 := by
  classical
  rw [threeSpinProjector_trace]
  simp_rw [← phasedThreeDescendant_quadratic]
  by_cases hz : z.val ≤ T
  · rw [ite_eq_left hz]
    have hn : T-z.val < coupledWeight Q z.val+1 := by unfold coupledWeight; omega
    rw [Finset.sum_eq_single (⟨T-z.val,hn⟩ : Fin (coupledWeight Q z.val+1))]
    · exact threeBodyLevelMatrix_descendant Q hQ z t T ell entries hz hT ht
    · intro n hn' hne
      apply threeBodyLevelMatrix_descendant_off
      intro he
      apply hne
      exact Fin.ext (by dsimp; omega)
    · simp
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro n hn
    exact threeBodyLevelMatrix_descendant_off Q hQ z n.val t T ell entries (by omega)

end Laughlin.Spin

end OAI
