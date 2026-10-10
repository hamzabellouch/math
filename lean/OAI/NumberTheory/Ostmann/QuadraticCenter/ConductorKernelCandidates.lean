import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedKernelCharacter

namespace OAI

/-! # Finitely many kernel candidates for one exceptional conductor -/

namespace Ostmann

open scoped Classical

/-- The eight possible quotients of a conductor by its odd kernel part,
with the four possible sign/two factors. -/
def conductorKernelCandidates (q : ℕ) : Finset ℤ :=
  ((Finset.Icc 1 8).product quadraticSigns).image
    (fun z : ℕ × ℤ => z.2 * (q / z.1 : ℕ))

theorem conductorKernelCandidates_card (q : ℕ) :
    (conductorKernelCandidates q).card ≤ 32 := by
  calc
    _ ≤ ((Finset.Icc 1 8).product quadraticSigns).card := Finset.card_image_le
    _ = 32 := by norm_num [quadraticSigns]

/-- The divisibility and size facts proved for the constructed characters
place the signed kernel on the explicit list for its conductor. -/
theorem mem_conductorKernelCandidates (d : ℤ) (q N : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hNq : N ∣ q) (hbound : q ≤ 8 * N)
    (hd : d.natAbs = N ∨ d.natAbs = 2 * N) :
    d ∈ conductorKernelCandidates q := by
  obtain ⟨k, hk⟩ := hNq
  have hkpos : 0 < k := by nlinarith
  have hk8 : k ≤ 8 := by nlinarith
  have hqN : q / k = N := by
    rw [hk, Nat.mul_div_cancel N hkpos]
  have hsign : (d.natAbs : ℤ) = d ∨ -(d.natAbs : ℤ) = d := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 d with hp | hn
    · exact Or.inl (abs_of_nonneg hp)
    · exact Or.inr (by rw [abs_of_nonpos hn, neg_neg])
  have hmem (c : ℤ) (hc : c ∈ quadraticSigns) (hcd : c * (N : ℤ) = d) :
      d ∈ conductorKernelCandidates q := by
    apply Finset.mem_image.mpr
    refine ⟨(k, c), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hkpos, hk8⟩, hc⟩, ?_⟩
    simpa only [hqN] using hcd
  rcases hd with hd | hd <;> rcases hsign with hs | hs
  · exact hmem 1 (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem (-1) (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem 2 (by simp [quadraticSigns]) (by simpa [hd] using hs)
  · exact hmem (-2) (by simp [quadraticSigns]) (by simpa [hd] using hs)

def largeConductorKernelCandidates (q : ℕ) : Finset ℤ :=
  (conductorKernelCandidates q).filter fun d => q ≤ 4 * d.natAbs

theorem largeConductorKernelCandidates_card (q : ℕ) :
    (largeConductorKernelCandidates q).card ≤ 32 :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (conductorKernelCandidates_card q)

theorem mem_largeConductorKernelCandidates (d : ℤ) (q N : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hNq : N ∣ q) (hbound : q ≤ 8 * N)
    (hd : d.natAbs = N ∨ d.natAbs = 2 * N) (hqd : q ≤ 4 * d.natAbs) :
    d ∈ largeConductorKernelCandidates q :=
  Finset.mem_filter.mpr ⟨mem_conductorKernelCandidates d q N hN hq hNq hbound hd, hqd⟩

end Ostmann

end OAI
