import OAI.Probability.InvariantIsing.Cavity.CavityAffineFamily

namespace OAI

/-! Canonical rational multiplicities at every physical dimension. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityResidueOffset {m : ℕ} (hm : 0 < m) (t : ℕ) (a : Fin m) : ℕ :=
  if a=⟨0,hm⟩ then t else 0

lemma cavityResidueOffset_sum {m : ℕ} (hm : 0 < m) (t : ℕ) :
    ∑ a, cavityResidueOffset hm t a=t := by
  classical
  simp [cavityResidueOffset]

def cavityResidueLabel {m n : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (N : ℕ) : Fin N → Fin m :=
  cavityAffineLabel hm s (cavityResidueOffset hm (N%n)) hsum N

lemma cavityResidueSize {m : ℕ} (hm : 0 < m) (n q t r : ℕ) :
    cavityAffineSize n q (cavityResidueOffset hm t) r=(r+q)*n+t := by
  simp only [cavityAffineSize, cavityResidueOffset_sum]

lemma cavityResidueSize_mod {m n : ℕ} (hm : 0 < m) (q t r : ℕ) (ht : t < n) :
    cavityAffineSize n q (cavityResidueOffset hm t) r%n=t := by
  rw [cavityResidueSize]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

lemma cavityResidueLabel_progression {m n : ℕ} (hm : 0 < m)
    (s : Fin m → ℕ) (hsum : ∑ a, s a=n) (q t r : ℕ) (ht : t < n) :
    cavityResidueLabel hm s hsum (cavityAffineSize n q (cavityResidueOffset hm t) r)=
      cavityAffineLabel hm s (cavityResidueOffset hm t) hsum
        (cavityAffineSize n q (cavityResidueOffset hm t) r) := by
  unfold cavityResidueLabel
  rw [cavityResidueSize_mod hm q t r ht]

end InvariantIsing

end

end OAI
