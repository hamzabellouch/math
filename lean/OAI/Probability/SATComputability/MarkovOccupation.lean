import OAI.Probability.DilutedSpin.FiniteLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

noncomputable def finiteKernelStep {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (f : Ω → ℝ) (x : Ω) : ℝ := (K x).expect f

theorem finiteKernelStep_mono {Ω : Type*} [Fintype Ω] (K : Ω → FiniteLaw Ω) :
    Monotone (finiteKernelStep K) := by
  intro f g h x
  exact (K x).expect_mono h

theorem finiteKernelStep_iterate_const {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (c : ℝ) :
    (finiteKernelStep K)^[t] (fun _ => c) = fun _ => c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_const c

theorem finiteKernelStep_iterate_sub {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (f g : Ω → ℝ) :
    (finiteKernelStep K)^[t] (f-g) =
      (finiteKernelStep K)^[t] f - (finiteKernelStep K)^[t] g := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_sub _ _

theorem finiteKernelStep_iterate_mul {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (t : ℕ) (c : ℝ) (f : Ω → ℝ) :
    (finiteKernelStep K)^[t] (fun x => c*f x) =
      fun x => c*((finiteKernelStep K)^[t] f x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply', ih]
    funext x
    exact (K x).expect_mul_left c _

theorem sum_shift_difference_le (u : ℕ → ℝ) (hu0 : ∀ t, 0 ≤ u t)
    (hu1 : ∀ t, u t ≤ 1) (M L : ℕ) :
    (∑ t ∈ Finset.range M, (u t-u (t+L))) ≤ L := by
  have hM := Finset.sum_range_add u M L
  have hL := Finset.sum_range_add u L M
  rw [Nat.add_comm L M] at hL
  have hnonneg : 0 ≤ ∑ t ∈ Finset.range L, u (M+t) :=
    Finset.sum_nonneg (fun t _ => hu0 _)
  have hbound : (∑ t ∈ Finset.range L, u t) ≤ L := by
    calc
      _ ≤ ∑ _t ∈ Finset.range L, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hu1 t)
      _ = _ := by simp
  have he : (∑ t ∈ Finset.range M, u (t+L)) =
      ∑ t ∈ Finset.range M, u (L+t) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_comm t L]
  rw [Finset.sum_sub_distrib, he]
  linarith

theorem finiteKernel_occupation {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (alive bin : Ω → ℝ)
    (ha0 : ∀ x, 0 ≤ alive x) (ha1 : ∀ x, alive x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hblock : ∀ x, δ * bin x ≤ alive x - (finiteKernelStep K)^[L] alive x)
    (M : ℕ) (x : Ω) :
    (∑ t ∈ Finset.range M, (finiteKernelStep K)^[t] bin x) ≤ (L : ℝ)/δ := by
  have hstep (t : ℕ) : δ * (finiteKernelStep K)^[t] bin x ≤
      (finiteKernelStep K)^[t] alive x - (finiteKernelStep K)^[t+L] alive x := by
    have h := (finiteKernelStep_mono K).iterate t hblock x
    rw [finiteKernelStep_iterate_mul] at h
    change δ * (finiteKernelStep K)^[t] bin x ≤
      (finiteKernelStep K)^[t] (alive - (finiteKernelStep K)^[L] alive) x at h
    rw [finiteKernelStep_iterate_sub] at h
    simpa only [Function.iterate_add_apply, Pi.sub_apply] using h
  have hbounds (t : ℕ) : 0 ≤ (finiteKernelStep K)^[t] alive x ∧
      (finiteKernelStep K)^[t] alive x ≤ 1 := by
    have hlo := (finiteKernelStep_mono K).iterate t ha0 x
    have hhi := (finiteKernelStep_mono K).iterate t ha1 x
    rw [finiteKernelStep_iterate_const] at hlo hhi
    exact ⟨hlo, hhi⟩
  apply (le_div_iff₀ hδ).mpr
  rw [mul_comm, Finset.mul_sum]
  apply (Finset.sum_le_sum (fun t _ => hstep t)).trans
  exact sum_shift_difference_le _ (fun t => (hbounds t).1) (fun t => (hbounds t).2) M L

end FixedClauseThreshold.Computability

end OAI
