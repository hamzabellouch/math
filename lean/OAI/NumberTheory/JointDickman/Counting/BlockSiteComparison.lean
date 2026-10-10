import OAI.NumberTheory.JointDickman.Arithmetic.BlockPrimeSites

namespace OAI

/-! # Deterministic comparison of all arithmetic sites of a finite block -/

namespace JointDickman
open Finset

noncomputable def blockSiteResidues (M : ℕ) (P : Finset ℕ) (n : ℕ) :
    P → (univ : Finset (Fin M)).powerset :=
  fun p => blockPrimeHit M p.val (n : ZMod p.val)

theorem block_sites_crt_mean (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, M < p)
    (F : (P → (univ : Finset (Fin M)).powerset) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p), F (blockSiteResidues M P n))/
        (∏ p ∈ P, (p : ℝ)) =
      ∑ x, categoricalProductMass univ (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hc := crt_uniform_mean (fun p : P => p.val) hcop
    (fun x => F (fun p => blockPrimeHit M p.val (x p)))
  have hp := finiteProductMass_pushforward_test
    (fun (p : P) (_ : ZMod p.val) => 1/(p.val : ℝ))
    (fun p : P => blockPrimeHit M p.val) (fun x => (F x : ℂ))
  simp only [blockPrimeHit_pushMass M _ (hlarge _ (Subtype.property _))] at hp
  have hp' : (∑ x, categoricalProductMass univ
      (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x) =
      ∑ x, finiteProductMass (fun (p : P) (_ : ZMod p.val) => 1/(p.val : ℝ)) x *
        F (fun p => blockPrimeHit M p.val (x p)) := by
    exact_mod_cast hp
  rw [P.prod_coe_sort (fun p : ℕ => p), P.prod_coe_sort (fun p : ℕ => (p : ℝ))] at hc
  exact hc.trans hp'.symm

theorem block_sites_independent_error (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, M < p)
    (F : (P → (univ : Finset (Fin M)).powerset) → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, |F x| ≤ L) :
    |(∑ n ∈ range (∏ p ∈ P, p), F (blockSiteResidues M P n))/
        (∏ p ∈ P, (p : ℝ)) -
      ∑ x, bernoulliProductMass univ (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x| ≤
        2*L*(M : ℝ)^2*(∑ p ∈ P, 1/(p : ℝ)^2) := by
  have hcard : ∀ p ∈ P, (univ : Finset (Fin M)).card ≤ p := by
    intro p hp
    simpa using (hlarge p hp).le
  have h := categoricalPrimeProduct_test_bound (univ : Finset (Fin M)) P hP hcard
    (fun x => (F x : ℂ)) hL
    (fun x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hF x)
  rw [block_sites_crt_mean M P hP hlarge F]
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, card_univ, Fintype.card_fin] using h

end JointDickman

end OAI
