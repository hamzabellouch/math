import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-! The finite convex separation used in path-law fusion. A convex family of
vectors missing the strict upper orthant has a nonnegative normalized separator.
No closedness of the vector family is required. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem finite_nonnegative_separator {I : Type*} [Fintype I] [Nonempty I]
    {V : Set (I → ℝ)} (hV : Convex ℝ V) (hVne : V.Nonempty) (b : ℝ)
    (hmiss : ∀ v ∈ V, ∃ i, v i ≤ b) :
    ∃ w : I → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∀ v ∈ V, ∑ i, w i * v i ≤ b := by
  classical
  let U : Set (I → ℝ) := {v | ∀ i, b < v i}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {v : I → ℝ | b < v i} by ext v; simp [U]]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hUconvex : Convex ℝ U := by
    rw [show U = Set.univ.pi (fun _ : I => Ioi b) by ext v; simp [U]]
    exact convex_pi fun _ _ => convex_Ioi b
  have hdis : Disjoint U V := by
    apply disjoint_left.mpr
    intro v hv hvV
    obtain ⟨i, hi⟩ := hmiss v hvV
    exact (hv i).not_ge hi
  obtain ⟨f, t, hUf, hVf⟩ := geometric_hahn_banach_open hUconvex hUopen hV hdis
  let base : I → ℝ := fun _ => b + 1
  have hbase : base ∈ U := fun _ => by dsimp [base]; linarith
  have hfne : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := hVne
    have h1 := hUf base hbase
    have h2 := hVf v hv
    simp only [hz, zero_apply] at h1 h2
    linarith
  have hexp (v : I → ℝ) : f v = ∑ i, v i * f (Pi.single i 1) := by
    have hv : (∑ i, Pi.single i (v i)) = v := by ext i; simp
    conv_lhs => rw [← hv]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i <;> simp [hji]
    rw [he, map_smul]
    rfl
  have hsign (i : I) : f (Pi.single i 1) ≤ 0 := by
    by_contra h
    have hpos : 0 < f (Pi.single i 1) := lt_of_not_ge h
    obtain ⟨n, hn'⟩ := exists_nat_gt ((t - f base) / f (Pi.single i 1))
    have hn : t - f base < (n : ℝ) * f (Pi.single i 1) :=
      (div_lt_iff₀ hpos).mp hn'
    have hmem : base + (n : ℝ) • Pi.single i 1 ∈ U := by
      intro j
      change b < b + 1 + (n : ℝ) * (Pi.single i (1 : ℝ) : I → ℝ) j
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      by_cases hji : j = i <;> simp [hji]
      linarith
    have hlt := hUf _ hmem
    rw [map_add, map_smul] at hlt
    change f base + (n : ℝ) * f (Pi.single i 1) < t at hlt
    linarith
  let a : I → ℝ := fun i => -f (Pi.single i 1)
  let S : ℝ := ∑ i, a i
  have ha (i : I) : 0 ≤ a i := neg_nonneg.mpr (hsign i)
  have hS : 0 < S := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => ha i
    apply lt_of_le_of_ne hS0
    intro hzero
    have hai : ∀ i, a i = 0 := by
      have hz : ∑ i, a i = 0 := hzero.symm
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hz i
        (Finset.mem_univ i)
    apply hfne
    ext v
    rw [hexp]
    simp only [zero_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : f (Pi.single i 1) = 0 := neg_eq_zero.mp (hai i)
    simp [hi]
  have hbound (v : I → ℝ) (hv : v ∈ V) : ∑ i, a i * v i ≤ b * S := by
    by_contra h
    have hgap : 0 < (∑ i, a i * v i) - b * S := sub_pos.mpr (lt_of_not_ge h)
    let δ := ((∑ i, a i * v i) - b * S) / (2 * S)
    have hδ : 0 < δ := div_pos hgap (by positivity)
    have hu : (fun _ : I => b + δ) ∈ U := fun _ => by dsimp [U]; linarith
    have hlt := lt_of_lt_of_le (hUf _ hu) (hVf v hv)
    rw [hexp, hexp] at hlt
    have he1 : (∑ i, (b + δ) * f (Pi.single i 1)) = -(b + δ) * S := by
      dsimp only [S, a]
      rw [← Finset.mul_sum, Finset.sum_neg_distrib]
      ring
    have he2 : (∑ i, v i * f (Pi.single i 1)) = -(∑ i, a i * v i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [a]
      ring
    rw [he1, he2] at hlt
    have hδeq : δ * (2 * S) = (∑ i, a i * v i) - b * S :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨fun i => a i / S, fun i => div_nonneg (ha i) hS.le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hS.ne'
  · intro v hv
    have he : (∑ i, a i / S * v i) = (∑ i, a i * v i) / S := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact (div_le_iff₀ hS).mpr (hbound v hv)

end CircleDomainRigidity

end

end OAI
