import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

/-- Equality of the finite pushforward law, expressed without choosing a
representation of fibers. -/
def Projects (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (π : Ω → Λ) : Prop :=
  ∀ f : Λ → ℝ, P.expect (fun x => f (π x)) = Q.expect f

theorem Projects.logMean {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (m : ℝ) (f : Λ → ℝ) :
    P.logMean m (fun x => f (π x)) = Q.logMean m f := by
  unfold FiniteLaw.logMean FiniteLaw.expMoment
  rw [h (fun y => Real.exp (m*f y))]

theorem Projects.bind {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (R : FiniteLaw Γ) :
    Projects (P.bind (fun _ => R)) (Q.bind (fun _ => R)) (fun z => (π z.1,z.2)) := by
  intro f
  simp only [expect_bind]
  exact h (fun y => R.expect (fun z => f (y,z)))

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

/-- Forgetting the added spin sends the uniform (N+1)-spin prior exactly
to the uniform N-spin prior, including N=0. -/
theorem uniform_spin_projection (N : ℕ) :
    Projects (uniform : FiniteLaw (Fin (N+1) → Spin))
      (uniform : FiniteLaw (Fin N → Spin)) (fun σ i => σ i.succ) := by
  intro f
  rw [uniform_expect,uniform_expect,
    ← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp (fun σ => f (fun i => σ i.succ))]
  simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,Fin.cons_succ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul]
  push_cast
  rw [pow_succ]
  have hcard : (2:ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

def pathMap (π : Ω → Λ) : (n : ℕ) → FinitePath Ω n → FinitePath Λ n
  | 0, _ => ()
  | n+1, y => (π y.1,pathMap π n y.2)

/-- A genuine prior-law projection at every vertex, not a conclusion about
weighted roots. -/
def Projects (π : Ω → Λ) : (n : ℕ) → KernelTower Ω n → KernelTower Λ n → Prop
  | 0, _, _ => True
  | n+1, T, U => FiniteLaw.Projects T.1 U.1 π ∧ ∀ a, Projects π n (T.2 a) (U.2 (π a))

theorem backwardLog_of_projects {π : Ω → Λ} (n : ℕ) {T : KernelTower Ω n} {U : KernelTower Λ n}
    (h : Projects π n T U) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n T m (fun y => f (pathMap π n y)) = backwardLog n U m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.1.logMean (m 0) (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
      (fun y => f (π a,pathMap π n y))) = _
    have heq : (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
        (fun y => f (π a,pathMap π n y))) =
      (fun a => backwardLog n (U.2 (π a)) (fun j => m j.succ) (fun y => f (π a,y))) := by
      funext a
      exact ih (h.2 a) (fun j => m j.succ) (fun y => f (π a,y))
    rw [heq]
    exact h.1.logMean (m 0) (fun b => backwardLog n (U.2 b) (fun j => m j.succ) (fun y => f (b,y)))

theorem terminalTower_projects (π : Ω → Λ) (a : Ω)
    {P : FiniteLaw Ω} {Q : FiniteLaw Λ} (h : P.Projects Q π) (r : ℕ) :
    Projects π (r+1) (terminalTower a P r) (terminalTower (π a) Q r) := by
  induction r with
  | zero => exact ⟨h,fun _ => trivial⟩
  | succ r ih =>
    refine ⟨?_,fun _ => ih⟩
    intro f
    change (FiniteLaw.point a).expect (fun x => f (π x)) = (FiniteLaw.point (π a)).expect f
    simp only [FiniteLaw.expect_point]

omit [Fintype Ω] [Fintype Λ] in
@[simp] theorem terminalState_pathMap (π : Ω → Λ) (r : ℕ) (y : FinitePath Ω (r+1)) :
    terminalState r (pathMap π (r+1) y) = π (terminalState r y) := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih y.2
end KernelTower
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma expect_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (f : Ω → Λ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Successive projection of independent child vectors in a spatial
contraction. This is the actual product law; no decorrelation is assumed. -/
theorem product_contraction {N k : ℕ} {α : Fin k → Type*} [∀ i, Fintype (α i)]
    (P : (i : Fin k) → FiniteLaw (α i)) (X : (i : Fin k) → α i → Fin N → ℝ)
    (hX : ∀ i x v, |X i x v| ≤ 1) (B : Fin N → ℝ) (hB : ∀ v, |B v| ≤ 1) :
    (pi P).l2 (fun x => dot (fun v => (∏ i, X i (x i) v)-
      ∏ i, (P i).expect (fun y => X i y v)) B) ≤
      ∑ i, Real.sqrt (Real.sqrt ((P i).covarianceEnergy (X i))) := by
  classical
  induction k generalizing B with
  | zero => simp [dot,l2]
  | succ k ih =>
    let Q := pi (fun i : Fin k => P i.succ)
    let μ := fun v => (P 0).expect (fun y => X 0 y v)
    let C := fun (x : (i : Fin k) → α i.succ) v => B v * ∏ i, X i.succ (x i) v
    let f := fun (x : (i : Fin (k+1)) → α i) =>
      dot (fun v => X 0 (x 0) v-μ v) (C (fun i => x i.succ))
    let g := fun (x : (i : Fin (k+1)) → α i) =>
      dot (fun v => (∏ i : Fin k, X i.succ (x i.succ) v)-
        ∏ i : Fin k, (P i.succ).expect (fun y => X i.succ y v)) (fun v => B v*μ v)
    have hμ (v : Fin N) : |μ v| ≤ 1 := (P 0).abs_expect_le (fun y => hX 0 y v)
    have hC (x : (i : Fin k) → α i.succ) (v : Fin N) : |C x v| ≤ 1 := by
      dsimp only [C]
      rw [abs_mul,Finset.abs_prod]
      exact (mul_le_mul (hB v) (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        (fun index _ => hX index.succ (x index) v)) (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) zero_le_one).trans_eq (one_mul 1)
    have hBμ (v : Fin N) : |B v*μ v| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (hB v) (hμ v) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have he (x : (i : Fin (k+1)) → α i) :
        dot (fun v => (∏ i, X i (x i) v)-∏ i, (P i).expect (fun y => X i y v)) B = f x+g x := by
      simp only [f,g,C,dot,Fin.prod_univ_succ]
      rw [← add_div,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      dsimp only [μ]
      ring
    have hf : (pi P).l2 f ≤ Real.sqrt (Real.sqrt ((P 0).covarianceEnergy (X 0))) := by
      apply Real.sqrt_le_sqrt
      rw [expect_pi_cons P (fun x => f x^2)]
      change (P 0).expect (fun a => Q.expect (fun x =>
        (dot (fun v => X 0 a v-μ v) (C x))^2)) ≤ _
      rw [expect_comm]
      exact (P 0).independent_contraction_bound Q (X 0) C hC
    have hg : (pi P).l2 g ≤ ∑ i : Fin k,
        Real.sqrt (Real.sqrt ((P i.succ).covarianceEnergy (X i.succ))) := by
      have h := ih (fun i => P i.succ) (fun i => X i.succ)
        (fun i => hX i.succ) (fun v => B v*μ v) hBμ
      have heq : (pi P).l2 g = Q.l2 (fun x => dot
          (fun v => (∏ i : Fin k, X i.succ (x i) v)-
            ∏ i : Fin k, (P i.succ).expect (fun y => X i.succ y v)) (fun v => B v*μ v)) := by
        unfold l2
        rw [expect_pi_cons]
        simp only [g,Fin.cons_succ,expect_const,Q]
      rw [heq]
      exact h
    calc
      _ = (pi P).l2 (fun x => f x+g x) := by unfold l2; rw [FiniteLaw.expect_congr _ (fun x => congrArg (·^2) (he x))]
      _ ≤ (pi P).l2 f+(pi P).l2 g := (pi P).l2_add_le f g
      _ ≤ _ := by rw [Fin.sum_univ_succ]; exact add_le_add hf hg

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
