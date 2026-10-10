import OAI.Probability.UnimodularPercolation.Exploration.TailBounds

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

attribute [local instance] Classical.propDecidable Classical.decEq

theorem seeded_revealment_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (B : ℝ)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B) :
    ∀ i ∈ Q, bernoulliPolynomial (insert x (searchVertices G Q))
      (fun m => (seededEdgeSearch G x Q.card Q m).revealment p i) h ≤ 2 * B := by
  intro i hi
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G i)
  have he' : G i = s(a,b) := he.symm
  have hFa : insert a (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem
      (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have hFb : insert b (searchVertices G Q) ⊆ insert x (searchVertices G Q) :=
    Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_of_mem
      (mem_searchVertices G hi (by rw [he']; simp)),Finset.subset_insert _ _⟩
  have ha := hB a
  have hb := hB b
  rw [←finiteSeedProbability_expectation G Q _ a hFa] at ha
  rw [←finiteSeedProbability_expectation G Q _ b hFb] at hb
  have hr := seededEdgeSearch_mean_revealment_le G x Q
    (insert x (searchVertices G Q)) p h i a b he'
  linarith

theorem covariance_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p h : unitInterval) (B : ℝ)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B)
    (f : Finset E → ℝ) (hf : Monotone f) :
    |finiteCovariance Q p f
      (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h)| ≤
      (2 * B) * ((p : ℝ) * (1 - p)) * deriv (bernoulliPolynomial Q f) p := by
  have hc := EdgeQueryTree.randomized_covariance_le_deriv Q
    (insert x (searchVertices G Q)) p h f hf
    (fun m => seededEdgeSearch G x Q.card Q m)
    (fun _ _ => seededEdgeSearch_valid G x Q.card Q _)
    (2 * B) (seeded_revealment_of_ghost_bound G Q x p h B hB)
  convert hc using 2
  apply finiteCovariance_congr_right
  intro ω hω
  exact finiteSeedProbability_tree G Q _ x h ω hω

theorem tail_derivative_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p h : unitInterval) (B : ℝ)
    (hn : 1 ≤ (h : ℝ) * n) (hB0 : 0 ≤ B) (hsmall : B ≤ 1 / 4)
    (hB : ∀ y, markedConnectionPolynomial G Q y h p ≤ B) :
    finiteClusterTail G Q x n p ≤ 8 * B * deriv (finiteClusterTail G Q x n) p := by
  have hlow := finiteSeed_covariance_lower G Q x n p h hn B (hB x)
  have hupp := covariance_of_ghost_bound G Q x p h B hB
    (finiteClusterTailIndicator G x n) (finiteClusterTailIndicator_mono G x n)
  have hF := finiteClusterTail_nonneg G Q x n p
  have hd := finiteClusterTail_deriv_nonneg G Q x n p
  have hp : (p : ℝ) * (1 - p) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  have hprod := mul_le_mul_of_nonneg_right hp hd
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * B by positivity)
  have ha := le_abs_self (finiteCovariance Q p (finiteClusterTailIndicator G x n)
    (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h))
  have hs := mul_le_mul_of_nonneg_right hsmall hF
  change |_| ≤ _ * deriv (finiteClusterTail G Q x n) p at hupp
  nlinarith

theorem tail_transfer_of_ghost_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p q h : unitInterval) (B : ℝ) (hpq : p ≤ q)
    (hn : 1 ≤ (h : ℝ) * n) (hB0 : 0 < B) (hsmall : B ≤ 1 / 4)
    (hB : ∀ r : unitInterval, p ≤ r → r ≤ q →
      ∀ y, markedConnectionPolynomial G Q y h r ≤ B) :
    finiteClusterTail G Q x n p ≤
      Real.exp (-((q : ℝ) - p) / (8 * B)) * (2 * B) := by
  have hden : 0 < 8 * B := by positivity
  have hder : ∀ t ∈ Set.Icc (p : ℝ) q,
      (1 / (8 * B)) * finiteClusterTail G Q x n t ≤
        deriv (finiteClusterTail G Q x n) t := by
    intro t ht
    let r : unitInterval := ⟨t,⟨p.2.1.trans ht.1,ht.2.trans q.2.2⟩⟩
    have he := tail_derivative_of_ghost_bound G Q x n r h B hn hB0.le hsmall
      (hB r ht.1 ht.2)
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm (deriv (finiteClusterTail G Q x n) t)] using he
  have he := exponential_transfer_of_deriv_lower (finiteClusterTail G Q x n) p q
    (1 / (8 * B)) (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt)
    hpq hder
  have hb := (finiteClusterTail_le_markedConnection G Q x n q h hn).trans
    (mul_le_mul_of_nonneg_left (hB q hpq le_rfl x) (by norm_num : (0 : ℝ) ≤ 2))
  have heq : -(1 / (8 * B)) * ((q : ℝ) - p) = -((q : ℝ) - p) / (8 * B) := by ring
  rw [heq] at he
  exact he.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)

end Percolation.BenjaminiSchramm

end OAI
