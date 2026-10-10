import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-! # Concentration of averages of actual independent finite experiments -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

def sampleSum (g : X → ℝ) (N : ℕ) (xs : Fin N → X) : ℝ := ∑ i,g (xs i)

def sampleAverage (g : X → ℝ) (N : ℕ) (xs : Fin N → X) : ℝ := sampleSum g N xs/N

omit [Fintype X] [Nonempty X] in
lemma sampleSum_cons (g : X → ℝ) (N : ℕ) (x : X) (xs : Fin N → X) :
    sampleSum g (N+1) (Fin.cons x xs)=g x+sampleSum g N xs := by
  simp only [sampleSum,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma centered_mean (g : X → ℝ) :
    uniformAverage (fun x => g x-uniformAverage g)=0 := by
  rw [uniformAverage_sub_const,sub_self]

lemma sampleSum_mean_zero (g : X → ℝ) (hg : uniformAverage g=0) (N : ℕ) :
    uniformAverage (sampleSum g N)=0 := by
  induction N with
  | zero =>
    change uniformAverage (fun xs : Fin 0 → X => sampleSum g 0 xs)=0
    simp [sampleSum,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ]
    have he (x : X) : uniformAverage (fun xs : Fin N → X => sampleSum g (N+1) (Fin.cons x xs))=g x := by
      simp_rw [sampleSum_cons]
      rw [uniformAverage_add,uniformAverage_const,ih,add_zero]
    simp_rw [he]
    exact hg

/-- Mixed terms vanish because each coordinate is an independent uniform
finite experiment, not because of an assumed concentration oracle. -/
theorem sampleSum_secondMoment (g : X → ℝ) (hg : uniformAverage g=0) (N : ℕ) :
    uniformAverage (fun xs : Fin N → X => (sampleSum g N xs)^2)=
      N*uniformAverage (fun x => (g x)^2) := by
  induction N with
  | zero => simp [sampleSum,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ]
    have he (x : X) :
        uniformAverage (fun xs : Fin N → X => (sampleSum g (N+1) (Fin.cons x xs))^2)=
        (g x)^2+N*uniformAverage (fun y => (g y)^2) := by
      have hfun : (fun xs : Fin N → X => (sampleSum g (N+1) (Fin.cons x xs))^2)=
          fun xs => ((g x)^2+(2*g x)*sampleSum g N xs)+(sampleSum g N xs)^2 := by
        funext xs
        rw [sampleSum_cons]
        ring
      rw [hfun,uniformAverage_add,uniformAverage_add,uniformAverage_const,
        uniformAverage_mul_left,sampleSum_mean_zero g hg N,ih]
      ring
    simp_rw [he]
    rw [uniformAverage_add,uniformAverage_const]
    push_cast
    ring

omit [Nonempty X] in
lemma sampleAverage_centered (g : X → ℝ) (N : ℕ) (hN : 0 < N) (xs : Fin N → X) :
    sampleAverage g N xs-uniformAverage g=
      sampleSum (fun x => g x-uniformAverage g) N xs/N := by
  have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  unfold sampleAverage sampleSum
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp [hNR]

theorem sampleAverage_secondMoment (g : X → ℝ) (N : ℕ) (hN : 0 < N) :
    uniformAverage (fun xs : Fin N → X => (sampleAverage g N xs-uniformAverage g)^2)=
      uniformAverage (fun x => (g x-uniformAverage g)^2)/N := by
  have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  simp_rw [sampleAverage_centered g N hN,div_pow,div_eq_mul_inv]
  rw [uniformAverage_mul_const,sampleSum_secondMoment _ (centered_mean g)]
  field_simp [hNR]

/-- A finite Chebyshev bound for the actual independent sample array. -/
theorem sampleAverage_failure (g : X → ℝ) (N : ℕ) (hN : 0 < N)
    (sigma : ℝ) (hsigma : 0 < sigma) (hmean : 0 < uniformAverage g) :
    uniformAverage (fun xs : Fin N → X =>
      if sigma*uniformAverage g < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
      uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*(sigma*uniformAverage g)^2) := by
  have hden : 0 < (sigma*uniformAverage g)^2 := sq_pos_of_pos (mul_pos hsigma hmean)
  have hpoint (xs : Fin N → X) :
      (if sigma*uniformAverage g < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
        (sampleAverage g N xs-uniformAverage g)^2/(sigma*uniformAverage g)^2 := by
    split_ifs with h
    · rw [le_div_iff₀ hden]
      have hh := (sq_le_sq₀ (mul_nonneg hsigma.le hmean.le) (abs_nonneg _)).mpr h.le
      simpa only [one_mul,sq_abs] using hh
    · positivity
  have hh := uniformAverage_mono _ _ hpoint
  have he : uniformAverage (fun xs : Fin N → X =>
      (sampleAverage g N xs-uniformAverage g)^2/(sigma*uniformAverage g)^2)=
      uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*(sigma*uniformAverage g)^2) := by
    simp_rw [div_eq_mul_inv]
    rw [uniformAverage_mul_const,sampleAverage_secondMoment g N hN]
    ring
  exact hh.trans_eq he

lemma mean_bounds (g : X → ℝ) (L U : ℝ) (hg : ∀ x,L ≤ g x ∧ g x ≤ U) :
    L ≤ uniformAverage g ∧ uniformAverage g ≤ U := by
  constructor
  · simpa only [uniformAverage_const] using uniformAverage_mono (fun _ : X => L) g (fun x => (hg x).1)
  · simpa only [uniformAverage_const] using uniformAverage_mono g (fun _ : X => U) (fun x => (hg x).2)

/-- A bounded positive output gives the same explicit relative-variance
bound on every finite experiment, including a Boolean-word sampler. -/
theorem bounded_relative_failure (g : X → ℝ) (L U : ℝ) (hL : 0 < L)
    (hg : ∀ x,L ≤ g x ∧ g x ≤ U) (N : ℕ) (hN : 0 < N) (sigma : ℝ) (hsigma : 0 < sigma) :
    uniformAverage (fun xs : Fin N → X =>
      if sigma*uniformAverage g < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
      U^2/(N*(sigma*L)^2) := by
  have hm := mean_bounds g L U hg
  have hmean : 0 < uniformAverage g := hL.trans_le hm.1
  have hU : 0 ≤ U := hmean.le.trans hm.2
  have hvar : uniformAverage (fun x => (g x-uniformAverage g)^2) ≤ U^2 := by
    have hp (x : X) : (g x-uniformAverage g)^2 ≤ U^2 := by
      have hx := hg x
      have hnon : 0 ≤ g x := hL.le.trans hx.1
      have habs : |g x-uniformAverage g| ≤ U := abs_le.mpr ⟨by linarith,by linarith⟩
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr habs
    simpa only [uniformAverage_const] using uniformAverage_mono _ (fun _ : X => U^2) hp
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hden : 0 < N*(sigma*L)^2 := mul_pos hNR (sq_pos_of_pos (mul_pos hsigma hL))
  have hden' : N*(sigma*L)^2 ≤ N*(sigma*uniformAverage g)^2 := by
    apply mul_le_mul_of_nonneg_left _ hNR.le
    exact (sq_le_sq₀ (mul_nonneg hsigma.le hL.le) (mul_nonneg hsigma.le hmean.le)).mpr
      (mul_le_mul_of_nonneg_left hm.1 hsigma.le)
  exact (sampleAverage_failure g N hN sigma hsigma hmean).trans
    (div_le_div₀ (by positivity) hvar hden hden')

end

end ContingencyTables.FiniteIndependentAverages

end OAI
