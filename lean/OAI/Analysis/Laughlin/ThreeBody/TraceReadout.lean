import OAI.Analysis.Laughlin.ThreeBody.PhysicalMatrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def phasedThreeDescendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  (-1 : ℝ)^z.val • normalizedCoupledDescendant Q z.val hQ (by omega) n

theorem phasedThreeDescendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z.val+n) :
    phasedThreeDescendant Q hQ z n i = 0 := by
  have hh := genericUnitDescendant_off (2*Q-2) Q z.val n (by omega) (by omega) i hi
  change (-1 : ℝ)^z.val * genericUnitDescendant (2*Q-2) Q z.val (by omega) (by omega) n i = 0
  rw [hh,mul_zero]

theorem phasedThreeDescendant_at_level (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (T p j : ℕ)
    (hz : z.val ≤ T) (hT : T ≤ Q) (hpj : p+j=T) :
    phasedThreeDescendant Q hQ z (T-z.val) (⟨p,by omega⟩,⟨j,by omega⟩) =
      physicalCouplingCoefficient (2*Q-2) Q z.val T p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,by omega,by omega,hT⟩]
  have hj : T-p=j := by omega
  subst j
  rfl

theorem threeBodyLevelVector_dot {Q : ℕ} (v : PairOrbitalIndex Q → ℝ) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) :
    dotProduct v (threeBodyLevelVector Q t T entries) =
      (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
        dotProduct v (pairOrbitalUnit Q e.1 e.2.1) else 0)).sum := by
  induction entries with
  | nil => simp [threeBodyLevelVector]
  | cons e es ih =>
    simp only [threeBodyLevelVector,List.map_cons,List.sum_cons] at ih ⊢
    rw [dotProduct_add,ih]
    by_cases h : e.1+e.2.1=T
    · simp [h,dotProduct_smul,mul_comm]
    · simp [h]

theorem phasedThreeDescendant_unit_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n p j : ℕ)
    (h : p+j ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q p j) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [pairOrbitalUnit]
  split_ifs with he
  · rw [phasedThreeDescendant_off Q hQ z n i (by omega),zero_mul]
  · exact mul_zero _

theorem threeBodyLevelVector_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (threeBodyLevelVector Q t T entries) = 0 := by
  rw [threeBodyLevelVector_dot]
  have he : entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
      dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q e.1 e.2.1) else 0) = entries.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    split_ifs with hT
    · rw [phasedThreeDescendant_unit_off Q hQ z n e.1 e.2.1 (by omega),mul_zero]
    · rfl
  rw [he]
  simp

theorem threeBodyLevelVector_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val)) (threeBodyLevelVector Q t T entries) =
      threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z.val T t entries := by
  rw [threeBodyLevelVector_dot]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  split_ifs with h
  · rw [pairOrbitalUnit_dot Q e.1 e.2.1 (by omega) (by omega),
      phasedThreeDescendant_at_level Q hQ z T e.1 e.2.1 hz hT h]
  · rfl

end Laughlin.Spin

end OAI
