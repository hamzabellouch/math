import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.IdealMasks

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, summand Ψ W X I J * d (I * J ^ 3)

theorem markedCompletedT_one (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun _ => 1) = completedT Ψ W X := by
  simp only [markedCompletedT, mul_one, completedT]

theorem markedCompletedT_congr_nonzero (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A ≠ 0, d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hI : I = 0
  · simp only [hI, summand_zero_left, zero_mul]
  by_cases hJ : J = 0
  · simp only [hJ, summand_zero_right, zero_mul]
  rw [h (I * J ^ 3) (mul_ne_zero hI (pow_ne_zero 3 hJ))]

theorem markedCompletedT_summable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

theorem markedCompletedT_prime_priority {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (L : σ → Finset (Ideal Eis))
    (a : σ → Ideal Eis → ℂ) (H : Ideal Eis) (hH : H ≠ 0)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A))) =
    ∑ J ∈ slots.powerset,
      primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
        markedCompletedT Ψ W X (fun A =>
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A)) := by
  have hmark (A : Ideal Eis) (hA : A ≠ 0) :
      primeMark slots L a (IdealMobiusDivisorSum.primeSupport (H ^ 3 * A)) =
      ∑ J ∈ slots.powerset,
        primeMark J L a (IdealMobiusDivisorSum.primeSupport H) *
          primeMark (slots \ J)
            (fun i => L i \ IdealMobiusDivisorSum.primeSupport H) a
            (IdealMobiusDivisorSum.primeSupport A) := by
    rw [mul_comm (H ^ 3) A, ideal_primeSupport_mul_cube A H hA hH,
      Finset.union_comm, primeMark_priority]
    simp only [primeMark_residual_lists]
  rw [markedCompletedT_congr_nonzero Ψ W X _ _ hmark,
    markedCompletedT_finset_sum slots.powerset Ψ W hW X hX]
  simp only [markedCompletedT_const_mul]

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

theorem markedExpandedTerm_finite_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite := by
  apply (finite_support_expandedTerm Ψ W hW X hX).subset
  intro p hp hz
  apply hp
  simp only [markedExpandedTerm, hz, zero_mul]

theorem markedExpandedTerm_scale (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      (summand Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) I J * d (H ^ 3 * (I * J ^ 3))) =
      markedExpandedTerm Ψ W X d I H J := by
  rw [← mul_assoc, expandedTerm_scale]
  unfold markedExpandedTerm
  congr 2
  ring

theorem weighted_markedCompletedT_reopen (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (H : Ideal Eis) :
    (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) =
      ∑' I : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J := by
  simp only [markedCompletedT, ← tsum_mul_left, markedExpandedTerm_scale]

theorem marked_cube_inner_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    (d : Ideal Eis → ℂ) (I : Ideal Eis) :
    (∑' H : Ideal Eis, ∑' J : Ideal Eis, markedExpandedTerm Ψ W X d I H J) =
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
        Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let f : Ideal Eis → ℂ := fun B =>
    columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm B : ℝ) ^ 3 / X) * d (I * B ^ 3)
  have heq (H J : Ideal Eis) :
      (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) * f (H * J) =
        markedExpandedTerm Ψ W X d I H J := by
    simp only [f, markedExpandedTerm, expandedTerm, map_mul, Nat.cast_mul, mul_pow,
      mul_assoc]
  have hf := markedExpandedTerm_finite_support Ψ W hW X hX d
  have hp : (Function.support (fun p : Ideal Eis × Ideal Eis =>
      markedExpandedTerm Ψ W X d I p.1 p.2)).Finite := by
    change ((fun p : Ideal Eis × Ideal Eis => (I, p)) ⁻¹'
      Function.support (fun p : Ideal Eis × Ideal Eis × Ideal Eis =>
        markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hgeneric := ideal_cube_convolution (cubeWeight Ψ) (cubeWeight_zero Ψ) f
    (by simpa only [heq] using hp)
  simpa only [heq, f, map_one, Nat.cast_one, one_pow, mul_one] using hgeneric

theorem marked_cube_inverse_vstar (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A))) =
    ∑' I : Ideal Eis, (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) / X)) * d I := by
  let F : Ideal Eis × Ideal Eis × Ideal Eis → ℂ :=
    fun p => markedExpandedTerm Ψ W X d p.1 p.2.1 p.2.2
  have hF : Summable F :=
    summable_of_hasFiniteSupport (markedExpandedTerm_finite_support Ψ W hW X hX d)
  let e : (Ideal Eis × Ideal Eis × Ideal Eis) ≃ (Ideal Eis × Ideal Eis × Ideal Eis) := {
    toFun := fun p => (p.2.1, p.1, p.2.2)
    invFun := fun p => (p.2.1, p.1, p.2.2)
    left_inv := by rintro ⟨I, H, J⟩; rfl
    right_inv := by rintro ⟨I, H, J⟩; rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal Eis, ∑' I : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      simp only [weighted_markedCompletedT_reopen]
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal Eis × Ideal Eis × Ideal Eis, F p := e.tsum_eq F
    _ = ∑' I : Ideal Eis, ∑' H : Ideal Eis, ∑' J : Ideal Eis,
        markedExpandedTerm Ψ W X d I H J := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (marked_cube_inner_inverse Ψ W hW X hX d)

theorem marked_cube_inverse (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    (Real.sqrt X : ℂ)⁻¹ *
      (∑' I : Ideal Eis, columnWeight Ψ I * d I * W ((Ideal.absNorm I : ℝ) / X)) =
    ∑' H : Ideal Eis, (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ H *
      markedCompletedT Ψ W (X / (Ideal.absNorm H : ℝ) ^ 3) (fun A => d (H ^ 3 * A)) := by
  rw [marked_cube_inverse_vstar Ψ W hW X hX d, ← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [vstar_source_normalization Ψ W X hX I]
  ring

end

end SevenEighths.InverseMoment

end OAI
