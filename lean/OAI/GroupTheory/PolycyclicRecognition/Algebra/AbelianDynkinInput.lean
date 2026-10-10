import OAI.GroupTheory.PolycyclicRecognition.Analysis.OneParameterIntegralCurve
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput

namespace OAI

/-! # Finite BCH for commutative Lie groups -/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem IsGroupExponential.map_add_of_comm
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x y : GroupLieAlgebra (𝓘(ℝ, E)) G) : Exp (x + y) = Exp x * Exp y := by
  let γ : ℝ → G := fun t => Exp (t • x) * Exp (t • y)
  have hzero : γ 0 = 1 := by simp [γ, hExp.map_zero]
  have hmul : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    dsimp [γ]
    rw [hExp.map_add_smul, hExp.map_add_smul]
    ac_rfl
  have hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (x + y)) := by
    have hh := HasMFDerivAt.mul_at_one (hExp.hasMFDerivAt_zero x) (hExp.hasMFDerivAt_zero y)
      (by simp [hExp.map_zero]) (by simp [hExp.map_zero])
    apply hh.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let t : ℝ := r
    change t • x + t • y = t • (x + y)
    exact (smul_add t x y).symm
  have hh := oneParameter_eq_groupExponential hExp hzero hmul (x + y) hd 1
  simpa only [γ, one_smul] using hh.symm

theorem IsGroupExponential.prod_eq_exp_sum_of_comm
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    (List.ofFn (fun i => Exp (X i))).prod = Exp (∑ i, X i) := by
  induction n with
  | zero => simp [hExp.map_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hExp.map_add_of_comm]

/-- Only the degree-one coefficients are nonzero. -/
def abelianDynkinCoefficients (c n : ℕ) : DynkinCoefficients c n :=
  fun d _ => if d.val = 0 then 1 else 0

theorem abelianDynkinCoefficients_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) : |abelianDynkinCoefficients c n d w| ≤ (2 : ℝ) ^ c := by
  dsimp [abelianDynkinCoefficients]
  split_ifs
  · simpa only [abs_one] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ c)
  · simp only [abs_zero]; positivity

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_abelian {c n : ℕ} (hc : 0 < c) (X : Fin n → L) :
    finiteDynkinPolynomial (abelianDynkinCoefficients c n) X = ∑ i, X i := by
  let z : Fin c := ⟨0, hc⟩
  unfold finiteDynkinPolynomial
  rw [Finset.sum_eq_single z]
  · change (∑ w : Fin 1 → Fin n, (1 : ℝ) • X (w 0)) = ∑ i, X i
    simp only [one_smul]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)) _ _ (fun _ => rfl)
  · intro d _ hdz
    have hd : d.val ≠ 0 := fun h => hdz (Fin.ext h)
    simp [abelianDynkinCoefficients, hd]
  · simp

/-- The published BCH input is fully proved for commutative Lie groups. -/
theorem nilpotentDynkinExpansionInput_of_comm [FiniteDimensional ℝ E] :
    NilpotentDynkinExpansionInput E G := by
  intro Exp hExp c hc n
  refine ⟨abelianDynkinCoefficients c n, abelianDynkinCoefficients_bound c n, ?_⟩
  intro X
  by_cases hz : c = 0
  · subst c
    have htop : (⊤ : LieSubmodule ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
        (GroupLieAlgebra (𝓘(ℝ, E)) G)) = ⊥ := by simpa using hc
    have hx (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : x = 0 := by
      have hm : x ∈ (⊥ : LieSubmodule ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
          (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by rw [← htop]; exact LieSubmodule.mem_top x
      exact hm
    have hX : X = 0 := funext fun i => hx (X i)
    rw [hX]
    simp [finiteDynkinPolynomial, hExp.map_zero]
  · rw [finiteDynkinPolynomial_abelian (Nat.pos_of_ne_zero hz)]
    exact hExp.prod_eq_exp_sum_of_comm X

end PolycyclicRecognition

end

end OAI
