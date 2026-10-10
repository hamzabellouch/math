import OAI.NumberTheory.JointDickman.Amplification.TwoFormLocalBound

namespace OAI

/-! # The two-form sieve with a Rankin weight and a half weight -/

namespace JointDickman
open Finset Classical

theorem formRootWeight_two_mixed {p : ℕ} (a b x : ZMod p) (t u : ℝ) :
    formRootWeight ![a,b] ![t,u] x = residueWeight t a x*residueWeight u b x := by
  unfold formRootWeight
  rw [prod_filter,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,residueWeight]
  apply congrArg₂ (fun v w : ℝ => v*w)
  · exact @ite_cond_congr ℝ (a = x) (x = a) _ (Classical.propDecidable (x = a)) t 1 (propext eq_comm)
  · exact @ite_cond_congr ℝ (b = x) (x = b) _ (Classical.propDecidable (x = b)) u 1 (propext eq_comm)

theorem mixed_two_root_mean {p : ℕ} [NeZero p] (a b : ZMod p) (hab : a ≠ b) (q : ℝ) :
    (∑ n ∈ range p, residueWeight q a (n : ZMod p)*residueWeight (1/2) b (n : ZMod p))/(p : ℝ) =
      1-(3/2-q)/(p : ℝ) := by
  rw [← real_residue_sum_eq_range (fun x : ZMod p => residueWeight q a x*residueWeight (1/2) b x),sum_two_residueWeights q (1/2) a b hab,ZMod.card]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

/-- Only the two weights needed by the numeric-addition argument are used.
The product is the exact local density for distinct roots. -/
theorem mixed_two_root_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ)
      (a b : (p : P) → ZMod p.val) (q : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) → (∀ p, a p ≠ b p) →
      (∑ n ∈ Ico u v, ∏ p : P,
        residueWeight q (a p) (n : ZMod p.val)*residueWeight (1/2) (b p) (n : ZMod p.val)) ≤
        K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := form_interval_sieve hFord hM (by norm_num : 0 < (2 : ℕ))
  refine ⟨K,hK,?_⟩
  intro P a b q u v Z hq hq1 huv hZ hP hab
  let root : (p : P) → Fin 2 → ZMod p.val := fun p => ![a p,b p]
  let θ : P → Fin 2 → ℝ := fun _ => ![q,1/2]
  have hθ (p : P) (i : Fin 2) : 0 ≤ θ p i ∧ θ p i ≤ 1 := by
    fin_cases i
    · exact ⟨hq,hq1⟩
    · norm_num [θ]
  have hh := hbound P root θ u v Z huv hZ hP hθ
  have hpoint (p : P) (x : ZMod p.val) : formRootWeight (root p) (θ p) x =
      residueWeight q (a p) x*residueWeight (1/2) (b p) x := formRootWeight_two_mixed _ _ _ _ _
  simp_rw [hpoint] at hh
  have hmean (p : P) :
      (∑ n ∈ range p.val, residueWeight q (a p) (n : ZMod p.val)*
        residueWeight (1/2) (b p) (n : ZMod p.val))/(p.val : ℝ) =
      1-(3/2-q)/(p.val : ℝ) := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    exact mixed_two_root_mean (a p) (b p) (hab p) q
  simp_rw [hmean] at hh
  rw [P.prod_coe_sort (fun p : ℕ => 1-(3/2-q)/(p : ℝ))] at hh
  exact hh

end JointDickman

end OAI
