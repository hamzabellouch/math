import OAI.Analysis.Unitarizability.SignMatrix
import OAI.Analysis.Unitarizability.FrameParameters

namespace OAI

/-! The finite union bound chooses one sign matrix that passes every real
net test for every injective subfamily of the prescribed size. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset

theorem embedding_card_le (n p : ℕ) : Fintype.card (Fin p ↪ Fin n) ≤ n^p := by
  have h := Fintype.card_le_of_injective (fun e : Fin p ↪ Fin n => (e : Fin p → Fin n))
    (by intro e f h; apply Function.Embedding.ext; intro i; exact congrFun h i)
  simpa using h

/-- A real sign-matrix realization for all size-p subfamilies. The proof
uses the actual finite sign sample space, cardinality bounds, and net tests. -/
theorem exists_sign_matrix {n k p : ℕ} (hk : 0 < k)
    (hf : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1) :
    ∃ σ : Fin k × Fin n → Bool, ∀ e : Fin p ↪ Fin n, ‖synthesis σ e‖ ≤ 10 := by
  classical
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨s, hs, hsc, hsnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin p))
  obtain ⟨t, ht, htc, htnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin k))
  simp only [finrank_euclideanSpace_fin] at hsc htc
  let Ω := Fin k × Fin n → Bool
  let L := (Fin p ↪ Fin n) × s × t
  let bad : L → Finset Ω := fun l => univ.filter (fun σ =>
    (5 : ℝ) < |inner ℝ (synthesis σ l.1 l.2.1) l.2.2|)
  let B : Finset Ω := univ.biUnion bad
  let N : ℝ := 2 ^ Fintype.card (Fin k × Fin n)
  let q : ℝ := 2 * Real.exp (-25*(k : ℝ)/2)
  have hN : 0 < N := by positivity
  have hq : 0 ≤ q := by positivity
  have hb (l : L) : ((bad l).card : ℝ) ≤ q * N := by
    have h := bilinear_tail l.1 l.2.2 l.2.1 (ht _ l.2.2.2) (hs _ l.2.1.2)
    simp only [Fintype.card_fin] at h
    have he : -(k : ℝ)*25/2 = -25*(k : ℝ)/2 := by ring
    rw [he] at h
    apply (div_le_iff₀ hN).mp
    convert h using 1
    try rfl
    apply congrArg (fun m : ℕ => (m : ℝ) / N)
    apply congrArg Finset.card
    ext σ
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB : (B.card : ℝ) ≤ (Fintype.card L : ℝ) * (q*N) := by
    have hc := Finset.card_biUnion_le (s := (univ : Finset L)) (t := bad)
    calc
      _ ≤ ∑ l : L, ((bad l).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _l : L, q*N := Finset.sum_le_sum (fun l _ => hb l)
      _ = _ := by simp
  have hL : (Fintype.card L : ℝ) ≤ (n : ℝ)^p * 9^p * 9^k := by
    have hc : Fintype.card L = Fintype.card (Fin p ↪ Fin n) * s.card * t.card := by
      simp [L, mul_assoc]
    rw [hc, Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul (by exact_mod_cast embedding_card_le n p) (by exact_mod_cast hsc)
      (by positivity) (by positivity)) (by exact_mod_cast htc) (by positivity) (by positivity)
  have hB' : (B.card : ℝ) < N := by
    have hle := hB.trans (mul_le_mul_of_nonneg_right hL (mul_nonneg hq hN.le))
    have hid : (n : ℝ)^p * 9^p * 9^k * (q*N) =
        (2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2)) * N := by
      dsimp [q]
      rw [pow_add]
      ring
    rw [hid] at hle
    exact hle.trans_lt (by simpa using mul_lt_mul_of_pos_right hf hN)
  have hcard : B.card < (univ : Finset Ω).card := by
    have hNcard : N = (Fintype.card Ω : ℝ) := by simp [N, Ω]
    rw [hNcard] at hB'
    exact_mod_cast hB'
  have hnotall : ∃ σ : Ω, σ ∉ B := by
    by_contra hh
    push Not at hh
    have hle := Finset.card_le_card (show (univ : Finset Ω) ⊆ B from fun σ _ => hh σ)
    omega
  obtain ⟨σ, hnσ⟩ := hnotall
  refine ⟨σ, ?_⟩
  intro e
  apply SphereNet.operator_norm_le_ten (synthesis σ e) s t hs ht hsnet htnet
  intro z hz w hw
  by_contra hnot
  have hbad : σ ∈ bad (e, ⟨z,hz⟩, ⟨w,hw⟩) := by
    exact mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hnot⟩
  exact hnσ (mem_biUnion.mpr ⟨(e, ⟨z,hz⟩, ⟨w,hw⟩), mem_univ _, hbad⟩)

end SignMatrix
end Dixmier

end

end OAI
