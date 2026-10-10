import Mathlib
import OAI.Analysis.LaughlinFock.PairOrbit
import OAI.Analysis.LaughlinFock.RelativeTransfer

namespace OAI

/-! Allowance Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology

 

theorem fockAverage_partialHamiltonian {Q P : ℕ} (hQ : 1 ≤ Q) (hP : P ≤ 2*Q-1) :
    fockAverage Q (partialHamiltonian Q P) =
      ((P : ℂ) / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  have h := fockAverage_pair_family hQ (fun p : Fin P => p.val)
    (by intro p; have := p.isLt; omega)
  simpa only [Fintype.card_fin, partialHamiltonian,
    Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) P] using h

 

theorem fockAverage_local_error {Q : ℕ} (hQ : 24 ≤ Q) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (partialHamiltonian Q 24) = (24 : ℂ) • hamiltonian Q := by
  rw [fockAverage_partialHamiltonian (by omega) (by omega), smul_smul]
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  congr 1
  field_simp
  norm_num

 
def fourCopyAllowance (Q : ℕ) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • ∑ D ∈ Finset.Icc 1 23,
    fockAverage Q (∑ r : CopyLabel D,
      (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r)

 

theorem fourCopyAllowance_bound {Q : ℕ} (hQ : 24 ≤ Q) :
    ((1222 : ℂ) • hamiltonian Q - fourCopyAllowance Q).PosSemidef := by
  have hb (D : ℕ) (hD : D ∈ Finset.Icc 1 23) :
      ((Fintype.card (FourHighestShell Q D) : ℂ) • hamiltonian Q -
        ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ r : CopyLabel D,
          (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r)).PosSemidef := by
    have hd : D ≤ Q := by have := (Finset.mem_Icc.mp hD).2; omega
    have he := fockAverage_posSemidef Q _ (highestFourAnnihilator_pair_posSemidef hd)
    rw [map_sub, fockAverage_pair_family (by omega : 1 ≤ Q)
      (fun b : FourHighestShell Q D => b.val.1.val)
      (by intro b; have := b.val.1.isLt; omega)] at he
    have hs := he.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
    have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
    simpa only [smul_sub, smul_smul, mul_div_cancel₀ _ hn] using hs
  have hs := Matrix.posSemidef_sum (Finset.Icc 1 23) hb
  have hc := congrArg (fun n : ℕ => (n : ℂ)) (fourHighestShell_count (by omega : 23 ≤ Q))
  push_cast at hc
  simpa only [Finset.sum_sub_distrib, ← Finset.sum_smul, hc, ← Finset.smul_sum,
    fourCopyAllowance] using hs

 

def averagedFourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q : ℕ) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • ∑ D ∈ Finset.Icc 1 23,
    fockAverage Q (∑ r, ∑ s, fourComparison rows ε Q D r s •
      ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s))

 

theorem averagedFourComparison_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Q, 24 ≤ Q → (averagedFourComparison rows ε Q + e Q • hamiltonian Q).PosSemidef := by
  obtain ⟨ρ, hρpos, hρlim, hρ⟩ := fourComparison_uniform_transfer rows ε hCertificate
  refine ⟨fun Q => 552 * ρ Q, fun Q => mul_nonneg (by norm_num) (hρpos Q), ?_, ?_⟩
  · simpa using hρlim.const_mul 552
  intro Q hQ
  have he (D : ℕ) (hD : D ∈ Finset.Icc 1 23) :
      (((2*Q-1 : ℕ) : ℂ) • fockAverage Q
        (∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
        (24*ρ Q : ℝ) • hamiltonian Q).PosSemidef := by
    have hs := fockAverage_posSemidef Q _
      (hρ D (Finset.mem_Icc.mp hD).1 (Finset.mem_Icc.mp hD).2 Q hQ)
    rw [map_add, (fockAverage Q).map_smul_of_tower] at hs
    have ht := hs.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
    rw [smul_add, smul_comm _ (ρ Q), fockAverage_local_error hQ] at ht
    convert ht using 1
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (ρ Q), smul_smul,
      RCLike.real_smul_eq_coe_smul (K:=ℂ) (24*ρ Q)]
    push_cast
    congr 1
    ring_nf
  have hs := Matrix.posSemidef_sum (Finset.Icc 1 23) he
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const,
    Nat.card_Icc, show 23+1-1=23 by omega] at hs
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have hc : (24*ρ Q : ℝ)*23 = 552*ρ Q := by ring
  simpa only [hc, averagedFourComparison] using hs

end LaughlinFock
end

end OAI
