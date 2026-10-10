import Mathlib
import OAI.Analysis.Commutator.FiniteWordMaximalPatching
import OAI.Analysis.Commutator.PartialUnitaryCompletion
import OAI.Analysis.Commutator.FiniteTestCompletion

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_full_unitary_finite_tests {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hx : ∀ j,‖x j‖ ≤ 1)
    (hcenter : ∀ j,τ (x j)=0) (hk : ∀ i,k i≠0)
    (N : ℕ) {α : ℝ} (hα : 0<α) :
    ∃ u : unitary M, ((u:M) : H →L[ℂ] H)∈R ∧
      MomentBound τ x k (PartialUnitary.ofUnitary u) N α := by
  classical
  let m := Finset.univ.sup (fun i => (k i).natAbs)
  have hkm (i : K) : (k i).natAbs ≤ m := Finset.le_sup (f := fun i : K => (k i).natAbs) (s:=Finset.univ) (by simp)
  let C : ℝ := ((N+1)*(m+2):ℕ)
  have hC : 0<C := by dsimp [C]; positivity
  have hp (i : K) : ((k i).natAbs:ℝ)+2 ≤ C := by
    have h1 := Nat.add_le_add_right (hkm i) 2
    have h2 : m+2 ≤ (N+1)*(m+2) := by nlinarith
    dsimp [C]
    exact_mod_cast h1.trans h2
  have hw (l : List (Letter J K)) (hl : l.length ≤ N) : (wordCost k l:ℝ) ≤ C := by
    apply Nat.cast_le.mpr
    exact (wordCost_le k hkm l).trans (Nat.mul_le_mul_right (m+2) (hl.trans (Nat.le_succ N)))
  let r : ℝ := min 1 (α/(4*C))
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  have hCr : C*r ≤ α/4 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*C)).mp (min_le_right 1 (α/(4*C)))
    change r*(4*C) ≤ α at hh
    nlinarith
  let η := r^2
  have hη : 0<η := sq_pos_of_pos hr
  have hη1 : η ≤ 1 := by dsimp [η]; nlinarith
  let ε := α/(4*Real.exp (budgetSlope N η*(1-η)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hbudget : momentBudget ε (budgetSlope N η) (1-η)=α/4 := by
    dsimp [momentBudget,ε]
    field_simp
  obtain ⟨v,hvR,hcut,hbound⟩ := exists_almost_full_finite_tests M R τ hτ x k stage hmono
    hRM hnormal hfaith hone hirr hgrow hstage hdiffuse hx hcenter hk N hε hη hη1
  have hfull := momentBound_completed τ hτ x k hone hx v hbound hp hw
  have htotal : momentBudget ε (budgetSlope N η) (1-η)+C*Real.sqrt (1-(τ v.support).re) ≤ α := by
    rw [hbudget,hcut,show 1-(1-η)=η by ring]
    change α/4+C*Real.sqrt (r^2) ≤ α
    rw [Real.sqrt_sq hr.le]
    linarith
  refine ⟨v.completion,v.completed_mem M R hvR,?_⟩
  rw [PartialUnitary.ofUnitary_completion]
  exact momentBound_mono τ x k hfull htotal

end Kadison.FinitePatching

end

end
end

end OAI
