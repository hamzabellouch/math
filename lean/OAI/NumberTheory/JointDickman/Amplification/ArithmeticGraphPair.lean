import OAI.NumberTheory.JointDickman.Amplification.FirstFormPairs

namespace OAI

/-! # The arithmetic graph weight obtained from the actual quadratic form -/

namespace JointDickman
open Finset

noncomputable def arithmeticGraphPairWeight (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a b c : ℕ) (j : ℤ) (n : ℕ) : ℝ :=
  (u c * regularCoefficientWeight B L τ C c *
    arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n)) *
  (regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C (n/b) * v a c) *
  (regularCoefficientWeight B L τ C b *
    arithmeticResidueWeight B L τ C (((n : ℤ)+j).toNat/a) * v b c)

theorem divisorEdge_new_quotients {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    (a*divisorEdgeInverse a b c n+1)/c = n/b ∧
      (b*divisorEdgeInverse a b c n+1)/c = ((n : ℤ)+j).toNat/a := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  constructor
  · calc
      _ = (b*((a*divisorEdgeInverse a b c n+1)/c))/b :=
        (Nat.mul_div_cancel_left _ hb).symm
      _ = n/b := congrArg (fun t => t/b) hback
  · have hend : (n : ℤ)+j = ((a*((b*divisorEdgeInverse a b c n+1)/c) : ℕ) : ℤ) := by
      have h := natural_divisor_edge_endpoints hc hca hcb he
      rwa [hback] at h
    rw [hend,Int.toNat_natCast,Nat.mul_div_cancel_left _ ha]

theorem firstFormPairWeight_graph {B L : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {D A E : Finset ℕ} {N : ℕ} {j : ℤ}
    (ha : 0 < ∏ p ∈ A, p) (hb : 0 < ∏ p ∈ E, p) (hc : 0 < ∏ p ∈ D, p)
    (he : ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ))
    (hcop : (∏ p ∈ A, p).Coprime j.natAbs) {n : ℕ}
    (hn : n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N j) :
    firstFormPairWeight B L τ C u v D A E
        (divisorEdgeInverse (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) n) =
      arithmeticGraphPairWeight B L τ C u v
        (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) j n := by
  obtain ⟨hqa,hqb⟩ := divisorEdge_new_quotients ha hb hc he hcop hn
  unfold firstFormPairWeight arithmeticGraphPairWeight firstFormWeight
  rw [hqa,hqb]

/-- This is the exact arithmetic graph expression for a fixed coefficient
pair in the original energy. It includes both signs of the additive lag. -/
theorem firstFormPairEnergy_graph {B L : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {D A E : Finset ℕ} {j : ℤ}
    (ha : 0 < ∏ p ∈ A, p) (hb : 0 < ∏ p ∈ E, p) (hc : 0 < ∏ p ∈ D, p)
    (he : ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ))
    (hcop : (∏ p ∈ A, p).Coprime j.natAbs) (N : ℕ) (F : ℕ → ℂ)
    (hFa : ∀ n, F ((∏ p ∈ A, p)*n) = F n)
    (hFb : ∀ n, F ((∏ p ∈ E, p)*n) = F n)
    (hFc : ∀ n, F ((∏ p ∈ D, p)*n) = F n) :
    firstFormPairEnergy B L τ C u v (fun m => F (m+1)) N D A E =
      ∑ n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N j,
        arithmeticGraphPairWeight B L τ C u v
          (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) j n *
          (star (F n) * F ((n : ℤ)+j).toNat).re := by
  rw [firstFormPairEnergy_as_old,
    weighted_divisor_edge_reindex ha hb hc he hcop N
      (firstFormPairWeight B L τ C u v D A E) F hFa hFb hFc]
  apply sum_congr rfl
  intro n hn
  rw [firstFormPairWeight_graph τ C u v ha hb hc he hcop hn]

end JointDickman

end OAI
