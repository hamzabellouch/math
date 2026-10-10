import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledPivotLegs

namespace OAI

/-! # Exact heights on the compact family of actual support legs -/

noncomputable section
namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology

/-- The physical scale version of compact pivot-leg control includes the
pivot itself and retains the exact affine height of every selected point. -/
theorem exists_compact_rescaled_height_legs
    {L G W I J : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Fintype I] [DecidableEq I] [Fintype J] [Nonempty J]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
        ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
      bracketWordExponent (fun _ : I => 1) (β.val i) +
        bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k))
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hs0 : ∀ n, 0 < scale n)
    (pivot : L) (support : J → L) (V : Set W)
    (hV : IsOpen V) (hconv : Convex ℝ V)
    (hpivot : h pivot ∈ V) (hsupport : ∀ j, h (support j) ∈ V) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    ∃ Q : Set (Fin (finrank ℝ L) → ℝ), IsCompact Q ∧
      Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧
      ∀ᶠ n in atTop,
        (br n).equivFun (scale n • pivot) ∈ Q ∧
        ∀ j t, t ∈ Icc (0 : ℝ) 1 → ∃ z ∈ Q,
          Exp ((br n).equivFun.symm z) =
            Exp (scale n • pivot) * Exp ((scale n * t) • (support j - pivot)) ∧
          h (b.equivFun.symm z) = h pivot + t • (h (support j) - h pivot) := by
  classical
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
  obtain ⟨Q, hQ, hQU, hevent⟩ := exists_compact_rescaled_pivot_legs X S β h hh Exp π hπ
    a hm hweight (fun n => Real.log (scale n)) (Real.tendsto_log_atTop.comp hscale)
    pivot support V hV hconv hpivot hsupport
  have hchart (n z) : h ((br n).equivFun.symm z) = scale n • h (b.equivFun.symm z) := by
    simpa only [br, cost, bracketWordExponent_one] using
      word_length_chart_height X S β h hh (hs0 n) z
  refine ⟨Q, hQ, hQU, ?_⟩
  filter_upwards [hevent] with n hn
  have hleg (j : J) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∃ z ∈ Q,
      Exp ((br n).equivFun.symm z) =
        Exp (scale n • pivot) * Exp ((scale n * t) • (support j - pivot)) := by
    simpa only [Real.exp_log (hs0 n)] using hn j t ht
  have hp : (br n).equivFun (scale n • pivot) ∈ Q := by
    obtain ⟨z, hz, he⟩ := hleg (Classical.choice inferInstance) 0 (by constructor <;> norm_num)
    have hcoord : (br n).equivFun.symm z = scale n • pivot := hinj (by
      simpa only [mul_zero, zero_smul, hzero, mul_one] using he)
    have heq : z = (br n).equivFun (scale n • pivot) := by
      rw [← hcoord, LinearEquiv.apply_symm_apply]
    exact heq ▸ hz
  refine ⟨hp, ?_⟩
  intro j t ht
  obtain ⟨z, hz, he⟩ := hleg j t ht
  refine ⟨z, hz, he, ?_⟩
  have hheight := congrArg (fun g => (π g).toAdd) he
  rw [map_mul, toAdd_mul, hπ, hπ, hπ, hchart, map_smul, map_smul, map_sub] at hheight
  apply (smul_right_injective W (hs0 n).ne')
  change scale n • h (b.equivFun.symm z) =
    scale n • (h pivot + t • (h (support j) - h pivot))
  rw [smul_add, smul_smul]
  exact hheight

end PolycyclicRecognition

end

end OAI
