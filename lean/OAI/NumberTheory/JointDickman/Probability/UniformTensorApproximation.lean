import OAI.NumberTheory.JointDickman.Arithmetic.SmoothArithmeticError

namespace OAI

/-! # Uniform tensor approximation with its positive arithmetic error measure -/

namespace JointDickman
open Finset
open scoped Topology

noncomputable def tensorCutoff (x y z : ℝ) : ℝ :=
  tensorBoxBump x*tensorBoxBump y*tensorBoxBump z

def tensorParameterBox : Set (Fin 4 → ℝ) :=
  Set.Icc ![1/4,1/4,1/4,-3] ![17/4,17/4,17/4,3]

theorem tensorCutoff_nonneg (x y z : ℝ) : 0 ≤ tensorCutoff x y z := by
  exact mul_nonneg (mul_nonneg tensorBoxBump.nonneg tensorBoxBump.nonneg)
    tensorBoxBump.nonneg

theorem tensorParameterBox_mem {x y z s : ℝ}
    (hx : x ∈ Set.Icc (1/4 : ℝ) (17/4)) (hy : y ∈ Set.Icc (1/4 : ℝ) (17/4))
    (hz : z ∈ Set.Icc (1/4 : ℝ) (17/4)) (hs : |s| ≤ 3) :
    ![x,y,z,s] ∈ tensorParameterBox := by
  constructor
  · intro i
    fin_cases i
    · exact hx.1
    · exact hy.1
    · exact hz.1
    · exact (abs_le.mp hs).1
  · intro i
    fin_cases i
    · exact hx.2
    · exact hy.2
    · exact hz.2
    · exact (abs_le.mp hs).2

theorem tensorBoxBump_zero_outside {x : ℝ} (hx : x ∉ Set.Icc (1/4 : ℝ) (17/4)) :
    tensorBoxBump x = 0 := by
  apply tensorBoxBump_zero
  by_cases h : x ≤ 1/4
  · exact Or.inl h
  · exact Or.inr (lt_of_not_ge (fun h' => hx ⟨by linarith,h'⟩))

theorem uniform_tensor_approximation (F : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F tensorParameterBox) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ s : ℝ, |s| ≤ 3 → ∀ x y z : ℝ,
      |F ![x,y,z,s]*tensorCutoff x y z-
        MvPolynomial.eval ![x,y,z,s] P*tensorCutoff x y z| ≤ ε*tensorCutoff x y z := by
  let f : C(tensorParameterBox,ℝ) :=
    ⟨fun p => F p,continuousOn_iff_continuous_domRestrict.mp hF⟩
  obtain ⟨P,hP⟩ := compact_support_polynomial_approximation tensorParameterBox isCompact_Icc f hε
  refine ⟨P,?_⟩
  intro s hs x y z
  by_cases hx : x ∈ Set.Icc (1/4 : ℝ) (17/4)
  · by_cases hy : y ∈ Set.Icc (1/4 : ℝ) (17/4)
    · by_cases hz : z ∈ Set.Icc (1/4 : ℝ) (17/4)
      · have hp := (hP ⟨![x,y,z,s],tensorParameterBox_mem hx hy hz hs⟩).le
        change |MvPolynomial.eval ![x,y,z,s] P-F ![x,y,z,s]| ≤ ε at hp
        rw [← sub_mul,abs_mul,abs_of_nonneg (tensorCutoff_nonneg _ _ _),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hp (tensorCutoff_nonneg _ _ _)
      · simp [tensorCutoff,tensorBoxBump_zero_outside hz]
    · simp [tensorCutoff,tensorBoxBump_zero_outside hy]
  · simp [tensorCutoff,tensorBoxBump_zero_outside hx]

theorem smooth_arithmetic_tensor_approximation (F : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F tensorParameterBox) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin 4) ℝ, ∀ (B j : ℕ) (a b l u T t : ℝ) (S : Finset ℤ)
      (s : ℤ → ℝ), (∀ k ∈ S, |s k| ≤ 3) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      |geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => F ![x,y,z,s k]*tensorCutoff x y z) g h-
        geometricSmoothArithmeticSum B j a b l u T t S
          (fun k x y z => MvPolynomial.eval ![x,y,z,s k] P*tensorCutoff x y z) g h| ≤
        ε*geometricSmoothArithmeticSum B j a b l u T t S
          (fun _ x y z => tensorCutoff x y z) (fun _ => 1) (fun _ => 1) := by
  obtain ⟨P,hP⟩ := uniform_tensor_approximation F hF hε
  refine ⟨P,?_⟩
  intro B j a b l u T t S s hs g h hg hh
  rw [← geometricSmoothArithmeticSum_sub,← geometricSmoothArithmeticSum_smul]
  exact geometricSmoothArithmeticSum_abs_le B j a b l u T t S _ _ g h hg hh
    (fun k hk x y z => hP (s k) (hs k hk) x y z)

end JointDickman

end OAI
