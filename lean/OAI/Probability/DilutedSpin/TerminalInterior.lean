import OAI.Probability.DilutedSpin.FiniteEncoding

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

lemma exists_weight_pos (P : FiniteLaw Ω) : ∃ a, 0<P.weight a := by
  by_contra! h
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ) => h a)
  rw [P.total] at hh
  simp only [Finset.sum_const_zero] at hh
  linarith

lemma tilt_weight_pos (P : FiniteLaw Ω) (m : ℝ) (f : Ω → ℝ)
    (a : Ω) (ha : 0<P.weight a) : 0<(P.tilt m f).weight a :=
  div_pos (mul_pos ha (Real.exp_pos _)) (P.expMoment_pos _ _)

lemma expect_lt_const (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ a, f a≤c) (hg : ∃ a, 0<P.weight a ∧ f a<c) : P.expect f<c := by
  rw [← P.expect_const c]
  unfold expect
  apply Finset.sum_lt_sum
  · intro a _
    exact mul_le_mul_of_nonneg_left (hf a) (P.nonneg a)
  · obtain ⟨a,ha,hfa⟩ := hg
    exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left hfa ha⟩

lemma spinMean_interior (P : FiniteLaw Ω) (s : Ω → ℝ) (hs : ∀ a, |s a|≤1)
    (hl : ∃ a, 0<P.weight a ∧ s a<1) (hu : ∃ a, 0<P.weight a ∧ -1<s a) :
    P.expect s ∈ Set.Ioo (-1) 1 := by
  refine ⟨?_, P.expect_lt_const s 1 (fun a => (abs_le.mp (hs a)).2) hl⟩
  have hh := P.expect_lt_const (fun a => -s a) 1
    (fun a => by have := (abs_le.mp (hs a)).1; linarith) ?_
  · rw [P.expect_neg] at hh
    linarith
  · obtain ⟨a,ha,hsa⟩ := hu
    exact ⟨a,ha,by linarith⟩

lemma bind_tilt_spinMean_interior {Γ : Type} [Fintype Γ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Γ) (m : ℝ) (f : Ω×Γ → ℝ) (s : Ω → ℝ)
    (hs : ∀ a, |s a|≤1) (hl : ∃ a, 0<P.weight a ∧ s a<1)
    (hu : ∃ a, 0<P.weight a ∧ -1<s a) :
    ((P.bind (fun _ => Q)).tilt m f).expect (fun a => s a.1) ∈ Set.Ioo (-1) 1 := by
  obtain ⟨b,hb⟩ := Q.exists_weight_pos
  apply spinMean_interior ((P.bind (fun _ => Q)).tilt m f) (fun a : Ω×Γ => s a.1) (fun a => hs a.1)
  · obtain ⟨a,ha,hsa⟩ := hl
    exact ⟨(a,b),tilt_weight_pos _ _ _ _ (mul_pos ha hb),hsa⟩
  · obtain ⟨a,ha,hsa⟩ := hu
    exact ⟨(a,b),tilt_weight_pos _ _ _ _ (mul_pos ha hb),hsa⟩

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Finite physical full support survives every old marked factor and every
 sequential tilt, even when the auxiliary priors have zero masses. -/
lemma terminalInterior_tilted (r : ℕ) {k : ℕ} (roots : Fin k → I)
    (P : FiniteLaw Ω) (a : Ω) (Q : (i : I) → Fin (r+1) → FiniteLaw (A i))
    (m : Fin (r+1) → ℝ) (f : FinitePath (Ω×Row roots) (r+1) → ℝ)
    (s : Ω → ℝ) (hs : ∀ x, |s x|≤1)
    (hl : ∃ x, 0<P.weight x ∧ s x<1) (hu : ∃ x, 0<P.weight x ∧ -1<s x) :
    TerminalInterior r (tilt (r+1) (tower roots (r+1) (terminalTower a P r) Q) m f)
      (fun y => s (terminalState r (physical roots (r+1) y))) := by
  induction r with
  | zero =>
    exact FiniteLaw.bind_tilt_spinMean_interior P (FiniteLaw.pi (fun j => Q (roots j) 0))
      (m 0) (fun x => f (x,())) s hs hl hu
  | succ r ih =>
    intro x
    exact ih (fun i j => Q i j.succ) (fun j => m j.succ) (fun y => f (x,y))

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
