import OAI.NumberTheory.TotientAsymptotic.FordNormalBandLower
import OAI.NumberTheory.TotientAsymptotic.PartitionedBandMass

namespace OAI

/-! A value count with the band restrictions supplied by actual normal preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma descending_nat_chain_le {Y : ℕ → ℕ} {k j : ℕ}
    (hY : ∀ i < k,Y (i+1) ≤ Y i) (hj : j ≤ k) : Y k ≤ Y j := by
  have hseg : ∀ t < k-j,(Y (j+t+1):ℝ) ≤ Y (j+t) := by
    intro t ht
    exact_mod_cast hY (j+t) (by omega)
  have hh := descending_chain_zero (fun t => (Y (j+t):ℝ)) (k-j) (by
    intro t ht
    simpa only [Nat.add_assoc] using hseg t ht)
  simp only [Nat.add_sub_of_le hj,Nat.add_zero] at hh
  exact_mod_cast hh

def normalBandExponent (S : ℕ) (D : ℝ) (k : ℕ) (Y : ℕ → ℕ) : ℝ :=
  ∑ j : Fin k,(((j.val+2:ℕ):ℝ)*(B (Y j.val)-B (Y (j.val+1))+D)-
    ((j.val+2:ℕ):ℝ)*(B (Y j.val)-B (Y (j.val+1))-Real.sqrt (B S*B (Y j.val)))*
      Real.log (j.val+2))

theorem normal_preimage_band_value_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X z k : ℕ) (Y : ℕ → ℕ),2 ≤ S → S ≤ z → Y 0=z → Y k=S →
    (∀ j < k,Y (j+1) ≤ Y j) → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ v ≤ X ∧
      z*partBetween v S z ≤ X ∧ SquarefreeAbove v S ∧ SquarefreeAbove n S ∧
      (∀ p ∈ n.primeFactors,IsNormalPrime S p) ∧
      ∀ j : Fin k,j.val+2 ≤ n.primeFactorsList.length ∧ Y j.val < fordPrime n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X*Real.log S/Real.log z * Real.exp (normalBandExponent S D k Y) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := partitioned_band_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X z k Y hS hSz hY0 hYk hY Q hQ
  let c := fun j : Fin k => ((j.val+2:ℕ):ℝ)
  let R := fun j : Fin k => c j*(B (Y j.val)-B (Y (j.val+1))-Real.sqrt (B S*B (Y j.val)))
  have hlow (j : ℕ) (hj : j ≤ k) : S ≤ Y j := by
    rw [← hYk]
    exact descending_nat_chain_le hY hj
  have hupp (j : ℕ) (hj : j ≤ k) : Y j ≤ z := by
    have hh := descending_chain_zero (fun i => (Y i:ℝ)) j (by
      intro i hi
      exact_mod_cast hY i (by omega))
    rw [hY0] at hh
    exact_mod_cast hh
  have hc (j : Fin k) : 1 ≤ c j := by dsimp [c]; norm_cast; omega
  have hh := hbound S X z k (fun j => (Y j:ℝ)) c R hS hSz
    (by exact_mod_cast hY0) (by exact_mod_cast hYk)
    (fun j hj => by exact_mod_cast hY j hj)
    (fun j hj => by exact_mod_cast hS.trans (hlow (j+1) (by omega))) hc Q (by
      intro v hv
      obtain ⟨n,hn,hφ,hvX,hpart,hsqv,hsqn,hnormal,hprefix⟩ := hQ v hv
      have hv0 : 0 < v := hφ ▸ Nat.totient_pos.mpr hn
      refine ⟨hv0,hvX,hpart,partBetween_squarefree hv0.ne' hsqv,?_⟩
      intro j
      have hsq : SquarefreeAbove n (Y j.val) := by
        intro p hp hpl
        exact hsqn p hp ((show (S:ℝ) ≤ Y j.val by exact_mod_cast hlow j.val (by omega)).trans_lt hpl)
      have hb := ford_normal_part_band_lower hn (by omega : 0 < j.val+2) (hprefix j).1
        (show (S:ℝ) ≤ Y (j.val+1) by exact_mod_cast hlow (j.val+1) (by omega))
        (hY j.val j.isLt) (show (Y j.val:ℝ) ≤ z by exact_mod_cast hupp j.val (by omega))
        (by simpa using (hprefix j).2) hsq hnormal
      rw [hφ] at hb
      exact hb)
  simpa only [normalBandExponent,c,R,Nat.cast_add,Nat.cast_ofNat] using hh

end TotientAsymptotic

end

end OAI
