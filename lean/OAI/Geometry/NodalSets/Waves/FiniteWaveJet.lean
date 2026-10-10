import OAI.Geometry.NodalSets.Elliptic.TransportJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def truncateJet (a : Jet) (d : ℕ) : CPoly := ∑ k ∈ Finset.range (d + 1), a k

def polynomialJet (p : CPoly) : Jet := fun k ↦ homogeneousComponent k p

theorem polynomialJet_truncate (a : Jet) (ha : ∀ k, (a k).IsHomogeneous k) (d k : ℕ) :
    polynomialJet (truncateJet a d) k = if k ≤ d then a k else 0 := by
  unfold polynomialJet truncateJet
  rw [map_sum]
  simp_rw [homogeneousComponent_of_mem (ha _)]
  simp [Finset.mem_range]

lemma polynomialJet_truncate_eq (a : Jet) (ha : ∀ k, (a k).IsHomogeneous k)
    (d k : ℕ) (hk : k ≤ d) : polynomialJet (truncateJet a d) k = a k := by
  simp [polynomialJet_truncate a ha, hk]

lemma eikonalCoefficient_congr (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a b : Jet) (h : ∀ k, k ≤ n + 2 → a k = b k) :
    eikonalCoefficient v g n a = eikonalCoefficient v g n b := by
  rw [eikonalCoefficient_split, eikonalCoefficient_split, h (n + 2) le_rfl,
    eikonalKnown_congr v g n a b (fun k hk ↦ h k (by omega))]

lemma transportCoefficient_congr (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c : Jet) (f f' : Jet) (n : ℕ) (a b : Jet)
    (h : ∀ k, k ≤ n + 1 → a k = b k) (hf : f n = f' n) :
    transportCoefficient w W c f n a = transportCoefficient w W c f' n b := by
  rw [transportCoefficient_split, transportCoefficient_split, h (n + 1) le_rfl]
  rw [transportKnown_congr W c f n a b (fun k hk ↦ h k (by omega))]
  simp only [transportKnown, hf]

theorem finite_eikonal_polynomial (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (initial : Jet)
    (hi : ∀ k, (initial k).IsHomogeneous k)
    (hsecond : eikonalCoefficient v g 0 initial = 0) (steps : ℕ) :
    ∃ p : CPoly,
      (∀ k, k ≤ 2 → polynomialJet p k = initial k) ∧
      (∀ k, steps + 2 < k → polynomialJet p k = 0) ∧
      ∀ n, n ≤ steps → eikonalCoefficient v g n (polynomialJet p) = 0 := by
  obtain ⟨a, ha, hkeep, hsolve⟩ := finite_eikonal_jets v hv g initial hi steps
  refine ⟨truncateJet a (steps + 2), ?_, ?_, ?_⟩
  · intro k hk
    rw [polynomialJet_truncate_eq a ha _ _ (by omega), hkeep k hk]
  · intro k hk
    simp [polynomialJet_truncate a ha, show ¬ k ≤ steps + 2 by omega]
  · intro n hn
    rw [eikonalCoefficient_congr v g n _ a
      (fun k hk ↦ polynomialJet_truncate_eq a ha _ _ (by omega))]
    by_cases hz : n = 0
    · subst n
      rw [eikonalCoefficient_congr v g 0 a initial (by simpa using hkeep)]
      exact hsecond
    · exact hsolve n (by omega) (by omega)

theorem finite_transport_polynomials (w : Fin 4 → ℂ) (hw : w ≠ 0)
    (W : ℕ → Fin 4 → CPoly) (c : Jet)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (b : ℕ → Fin 4 → CPoly) (m J : ℕ) :
    ∃ P : ℕ → CPoly,
      (∀ j, polynomialJet (P j) 0 = if j = 0 then 1 else 0) ∧
      (∀ j k, m + 1 + 2 * (J - j) < k → polynomialJet (P j) k = 0) ∧
      (∀ n, n < m + 1 + 2 * J → transportCoefficient w W c 0 n (polynomialJet (P 0)) = 0) ∧
      ∀ j, j < J → ∀ n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient w W c
          (fun k ↦ -secondOrderCoefficient g b (polynomialJet (P j)) k)
          n (polynomialJet (P (j + 1))) = 0 := by
  obtain ⟨A, hA, hzero, hfirst, hnext⟩ := transport_tower w hw W c g b m J
  let d : ℕ → ℕ := fun j ↦ m + 1 + 2 * (J - j)
  let P : ℕ → CPoly := fun j ↦ truncateJet (A j) (d j)
  have heq (j k : ℕ) (hk : k ≤ d j) : polynomialJet (P j) k = A j k :=
    polynomialJet_truncate_eq (A j) (hA j) _ _ hk
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro j; rw [heq j 0 (Nat.zero_le _), hzero]
  · intro j k hk
    exact (polynomialJet_truncate (A j) (hA j) _ _).trans (ite_eq_right (by dsimp [d]; omega))
  · intro n hn
    rw [transportCoefficient_congr w W c 0 0 n _ (A 0)
      (fun k hk ↦ heq 0 k (by dsimp [d]; omega)) rfl]
    exact hfirst n hn
  · intro j hj n hn
    have hd : d j = d (j + 1) + 2 := (wave_degree_budgets m J j hj).1
    have hforce : -secondOrderCoefficient g b (polynomialJet (P j)) n =
        -secondOrderCoefficient g b (A j) n := by
      rw [secondOrderCoefficient_congr g b _ (A j) n
        (fun k hk ↦ heq j k (by dsimp [d] at *; omega))]
    rw [transportCoefficient_congr w W c _ (fun k ↦ -secondOrderCoefficient g b (A j) k) n _ (A (j + 1))
      (fun k hk ↦ heq (j + 1) k (by dsimp [d]; omega)) hforce]
    exact hnext j n hn

theorem transport_telescope (B L : CPoly →ₗ[ℂ] CPoly) (a : ℕ → CPoly)
    (N : ℂ) (hN : N ≠ 0) (J : ℕ) :
    N • B (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) +
      L (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) =
    N • B (a 0) +
      (∑ j ∈ Finset.range J, (N⁻¹ ^ j) • (B (a (j + 1)) + L (a j))) +
      (N⁻¹ ^ J) • L (a J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ (n := J + 1), map_add, map_add, map_smul, map_smul,
      smul_add]
    conv_rhs => rw [Finset.sum_range_succ]
    have hpow : N * N⁻¹ ^ (J + 1) = N⁻¹ ^ J := by
      rw [pow_succ]
      field_simp
    rw [smul_smul, hpow]
    rw [show N • B (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j) +
      N⁻¹ ^ J • B (a (J + 1)) +
      (L (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j) + N⁻¹ ^ (J + 1) • L (a (J + 1))) =
      (N • B (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j) +
      L (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j)) +
      N⁻¹ ^ J • B (a (J + 1)) + N⁻¹ ^ (J + 1) • L (a (J + 1)) by abel]
    rw [ih, smul_add]
    abel

end
end Yau.Jets

end OAI
