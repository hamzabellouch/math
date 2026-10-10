import OAI.Combinatorics.MatchingPSD.CommonSelection

namespace OAI

namespace MatchingSmoothing
open scoped BigOperators

lemma lowProjection_comp (h d : ℕ) (p : Equiv.Perm (Vertices h))
    (f : Pairing (Vertices h) → ℝ) :
    lowProjection h d (fun M => f (Pairing.relabel p M)) =
      fun M => lowProjection h d f (Pairing.relabel p M) := by
  have he := lowProjection_equivariant h d p⁻¹ f
  have hc (f : Pairing (Vertices h) → ℝ) :
      Pairing.act p⁻¹ f = fun M => f (Pairing.relabel p M) := by
    ext M
    simp only [Pairing.act_apply, inv_inv]
  rw [hc, hc] at he
  exact he

lemma simultaneous_table_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (G I T : Type) [Fintype G] [Group G] [Fintype I] [Fintype T]
      (z : I → Vertices h → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing (Vertices h))
      (lift : I → Equiv.Perm (Vertices h) → G)
      (g : I → G → Pairing (Vertices h) → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => N.table (z i) = (M i t).table (z i)) (g i a) -
            P i (fun c => ((M i t).table (z i) (threeEdgeType (crossPair c)) : ℝ)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hsm⟩ := uniform_permutation_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh G I T _ _ _ _ z hz M lift g hcov B hB
  let : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  let err : I → G → ℝ := fun i a => ∑ t : T,
    (predicateAverage (fun N => N.table (z i) = (M i t).table (z i))
      (g i a - lowProjection h d (g i a)))^2
  let b : ℝ := (Fintype.card T : ℝ) * ((2*h : ℝ)^(2*K))⁻¹ * B^2
  have hlocal (i : I) (a : G) : (𝔼 p : Equiv.Perm (Vertices h), err i (a*lift i p)) ≤ b := by
    have hres (p : Equiv.Perm (Vertices h)) :
        g i (a*lift i p) - lowProjection h d (g i (a*lift i p)) =
          fun N => (g i a - lowProjection h d (g i a)) (Pairing.relabel p N) := by
      rw [hcov, lowProjection_comp]
      rfl
    simp only [err, hres]
    rw [Finset.expect_sum_comm]
    have hmean : (𝔼 N : Pairing (Vertices h), (g i a N)^2) ≤ B^2 :=
      Finset.expect_le Finset.univ_nonempty (fun N _ => hB i a N)
    calc
      _ ≤ ∑ _t : T, ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
        apply Finset.sum_le_sum
        intro t _
        exact (hsm h hh (z i) (hz i) (M i t) (g i a)).trans
          (mul_le_mul_of_nonneg_left hmean (by positivity))
      _ = b := by simp [b, mul_assoc]
  obtain ⟨a,ha⟩ := exists_total_le_of_local_means lift err (fun _ => b) hlocal
  have hex (i : I) := table_average_polynomial (z i) d (lowProjection h d (g i a))
    (lowProjection_mem h d (g i a))
  choose P hP he using hex
  refine ⟨a,P,hP,?_⟩
  have ht (i : I) (t : T) := he i ((M i t).table (z i)) ⟨M i t, rfl⟩
  simp only [err, map_sub, ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ha
  simpa only [b, mul_assoc] using ha

end MatchingSmoothing

end OAI
