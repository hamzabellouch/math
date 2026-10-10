import Mathlib
import OAI.Analysis.Commutator.FiniteTestPatching
import OAI.Analysis.Commutator.IrreducibleTowerAveraging
import OAI.Analysis.Commutator.MatrixExpectation
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BigOperators

open Filter

namespace Kadison.LocalQuantization

open TracialGNS

section Bridge

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma expectation_eq (x : A) :
    FiniteTest.expectation φ x=MatrixExpectation.expectation φ x := by
  rw [FiniteTest.expectation,MatrixExpectation.expectation_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [FiniteTest.unit]
  congr 1
  change Complex.ofReal ((Fintype.card I : ℝ)⁻¹)=(Fintype.card I : ℂ)⁻¹
  simp

variable [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ)

lemma vector_eq (a : A) : FiniteTest.vector τ a=algebraVector τ a := rfl

end Bridge

section FiniteTests

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hone : τ 1=1)

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] A)

include hτ hone in
theorem exists_small_projection
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (x : J → A)
    (hx : ∀ j, Tendsto (fun n => algebraVector τ (MatrixExpectation.expectation (stage n) (x j)))
      atTop (𝓝 0))
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ (n : ℕ) (q : A), q∈(stage n).range ∧ IsStarProjection q ∧
      0<(τ q).re ∧ (τ q).re<η ∧
      (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re := by
  have hinv : Tendsto (fun n => (Fintype.card (ι n):ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hgrow
  have hsum : Tendsto
      (fun n => ∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2)
      atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by omega : 2≠0),Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => (hx j).norm.pow 2)
  have herr : Tendsto
      (fun n => (∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2) +
        2*(Fintype.card (ι n):ℝ)⁻¹*(∑ j, ‖algebraVector τ (x j)‖^2)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,add_zero] using
      hsum.add ((tendsto_const_nhds.mul hinv).mul_const (∑ j, ‖algebraVector τ (x j)‖^2))
  have hev := (hinv.eventually (gt_mem_nhds hη)).and
    (herr.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  obtain ⟨n,hn,herrn⟩ := hev.exists
  obtain ⟨q,hq,hproj,htrace,hbound⟩ :=
    FiniteTest.exists_rankOne_finite_test τ (stage n) hτ hone (Classical.arbitrary (ι n)) x
  simp only [vector_eq,expectation_eq] at hbound
  have hp : 0<(Fintype.card (ι n):ℝ)⁻¹ := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  refine ⟨n,q,hq,hproj,htrace ▸ hp,htrace ▸ hn,?_⟩
  rw [htrace]
  calc
    _ ≤ (Fintype.card (ι n):ℝ)⁻¹ *
        ((∑ j, ‖algebraVector τ (MatrixExpectation.expectation (stage n) (x j))‖^2) +
          2*(Fintype.card (ι n):ℝ)⁻¹*(∑ j, ‖algebraVector τ (x j)‖^2)) := by
      nlinarith [hbound]
    _ < (Fintype.card (ι n):ℝ)⁻¹*ε^2 := mul_lt_mul_of_pos_left herrn hp
    _ = _ := mul_comm _ _

end FiniteTests

section ActualGeometry

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype J]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_centered_compression
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (x : J → M) (hx : ∀ j, τ (x j)=0)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ (n : ℕ) (q : M), q∈(stage n).range ∧ IsStarProjection q ∧
      0<(τ q).re ∧ (τ q).re<η ∧
      (∑ j, ‖algebraVector τ (q*x j*q)‖^2)<ε^2*(τ q).re := by
  apply exists_small_projection τ hτ hone stage hgrow x _ hε hη
  intro j
  simpa only [hx,zero_smul] using
    IrreducibleTowerAveraging.expectation_tendsto_any M τ hτ stage hmono
      hnormal hfaith hone hirr (x j)

end ActualGeometry

end Kadison.LocalQuantization

end

end
end

end OAI
