import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphPointCap

namespace OAI

/-! # Polynomial graph multiplicity without excluding site squares -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def activeGraphTriples (B L T N : ℕ) (τ C : ℝ) (j : ℤ) (n : ℕ) :
    Finset GraphCoefficientTriple :=
  (arithmeticGraphTriples B T).filter (fun g => graphTripleLag g = j ∧
    n ∈ graphTripleEdges N g ∧ graphTripleWeight B L τ C T g n ≠ 0)

theorem rawArithmeticGraphKernel_active (B L T N : ℕ) (τ C : ℝ) (j : ℤ) (n : ℕ) :
    rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) =
      ∑ g ∈ activeGraphTriples B L T N τ C j n, graphTripleWeight B L τ C T g n/(B : ℝ) := by
  unfold rawArithmeticGraphKernel activeGraphTriples
  rw [sum_div,sum_filter]
  apply sum_congr rfl
  intro g _
  by_cases hc : graphTripleLag g = j ∧ n ∈ graphTripleEdges N g
  · by_cases hw : graphTripleWeight B L τ C T g n = 0
    · simp [hc,hw]
    · simp [hc.1,hc.2,hw]
  · have hn : ¬ (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g ∧
        graphTripleWeight B L τ C T g n ≠ 0) := fun h => hc ⟨h.1,h.2.1⟩
    simp [hc,hn]

theorem activeGraphTriples_card {B L T M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T)
    (hcount : ∀ S R : Finset ℕ, RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
      2^(S ∪ R).card ≤ B)
    {i k : Fin M} (hik : i < k) :
    (activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))).card ≤ B^2 := by
  let G := activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))
  have hg (g : GraphCoefficientTriple) (h : g ∈ G) :
      g ∈ arithmeticGraphTriples B T ∧ graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
      u+(i.val+1) ∈ graphTripleEdges N g ∧ graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0 :=
    mem_filter.mp h
  change G.card ≤ B^2
  by_cases hne : G.Nonempty
  · obtain ⟨g0,hg0⟩ := hne
    obtain ⟨h0,hj0,hn0,hw0⟩ := hg g0 hg0
    have hcounts := graph_regular_endpoint_count hcount hik h0 hj0 hn0 hw0
    let S := (coefficientPrimeSet B (u+(i.val+1))).powerset ×ˢ
      (coefficientPrimeSet B (u+(k.val+1))).powerset
    have hmap : ∀ g ∈ G, (g.2.2,g.2.1) ∈ S := by
      intro g h
      obtain ⟨hgg,hj,hn,_⟩ := hg g h
      have hs := graph_endpoint_prime_subsets hik hgg hj hn
      exact mem_product.mpr ⟨mem_powerset.mpr hs.1,mem_powerset.mpr hs.2⟩
    have hinj : (G : Set GraphCoefficientTriple).InjOn (fun g => (g.2.2,g.2.1)) := by
      intro g h g' h' heq
      obtain ⟨hgg,hj,_,hw⟩ := hg g h
      obtain ⟨hgg',hj',_,hw'⟩ := hg g' h'
      have hr := graphBlockCandidate_roundtrip hik (graphTripleWeight_nonzero_supported hB hT τ C hgg hj hw)
      have hr' := graphBlockCandidate_roundtrip hik (graphTripleWeight_nonzero_supported hB hT τ C hgg' hj' hw')
      have he : graphBlockCandidate i k g = graphBlockCandidate i k g' := Prod.ext rfl heq
      exact hr.symm.trans ((congrArg (candidateGraphTriple B) he).trans hr')
    calc
      G.card ≤ S.card := card_le_card_of_injOn _ hmap hinj
      _ = 2^(coefficientPrimeSet B (u+(i.val+1))).card *
          2^(coefficientPrimeSet B (u+(k.val+1))).card := by simp [S]
      _ ≤ B*B := Nat.mul_le_mul hcounts.1 hcounts.2
      _ = B^2 := by ring
  · simp only [not_nonempty_iff_eq_empty.mp hne,card_empty]
    exact Nat.zero_le _

theorem rawArithmeticGraphKernel_forward_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T M N u : ℕ), 0 < T →
      ∀ (i k : Fin M), i < k →
      rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))/(B : ℝ) ≤
        (B : ℝ)^2 := by
  filter_upwards [regular_endpoint_subset_count hL hτ hτsmall,
    graphTripleWeight_le_one hL hτ hτsmall,eventually_gt_atTop 0] with B hcount hweight hB
  intro C T M N u hT i k hik
  rw [rawArithmeticGraphKernel_active]
  calc
    _ ≤ ∑ _g ∈ activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1)), (1 : ℝ) :=
      sum_le_sum (fun g _ => hweight C T _ g)
    _ = ((activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))).card : ℝ) := by simp
    _ ≤ (B : ℝ)^2 := by exact_mod_cast activeGraphTriples_card hB hT (hcount C) hik

end JointDickman

end OAI
