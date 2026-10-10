import Mathlib
import OAI.Analysis.LaughlinFock.PairLie
import OAI.Analysis.LaughlinFock.RowTraces

namespace OAI

/-! Pair Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem fockAverage_spin_column {Q k n : ℕ}
    (C : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s) * C = C * spinGenerator n s)
    (p : Fin (n+1)) :
    fockAverage Q ((wedgeAnnihilator Q k (fun A => C A p))ᴴ *
      wedgeAnnihilator Q k (fun A => C A p)) =
      (1/(n+1 : ℂ)) • exteriorLift Q k (C*Cᴴ) := by
  rw [← exteriorLift_single_congruence Q k C p p,
    fockAverage_spin_sandwich C hC, Matrix.trace_single_eq_same]

 
theorem pairSpinMatrix_lift {Q : ℕ} (hQ : 1 ≤ Q) :
    exteriorLift Q 2 (pairSpinMatrix Q * (pairSpinMatrix Q)ᴴ) = hamiltonian Q := by
  have h := exteriorLift_congruence Q 2 (pairSpinMatrix Q) 1
  simp only [Matrix.mul_one, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  rw [h]
  simp only [pairSpinMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
  rw [Fin.sum_univ_eq_sum_range (fun p => (pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) (2*Q-2+1)]
  have hd : 2*Q-2+1 = 2*Q-1 := by omega
  rw [hd]
  rfl

 

theorem fockAverage_pair_energy {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    fockAverage Q ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) =
      (1 / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  have h := fockAverage_spin_column (pairSpinMatrix Q) (pairSpinMatrix_intertwines hQ)
    (⟨p,by omega⟩ : Fin (2*Q-2+1))
  simp only [pairSpinMatrix, pairVector,
    wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
    pairSpinMatrix_lift hQ] at h
  have hd : ((2*Q-2 : ℕ) : ℂ) + 1 = ((2*Q-1 : ℕ) : ℂ) := by
    norm_cast
    omega
  simpa only [hd] using h

 
theorem fockAverage_hamiltonian {Q : ℕ} (hQ : 1 ≤ Q) :
    fockAverage Q (hamiltonian Q) = hamiltonian Q := by
  have h := fockAverage_spin_sandwich (pairSpinMatrix Q) (pairSpinMatrix_intertwines hQ) 1
  simp only [Matrix.mul_one, pairSpinMatrix_lift hQ, Matrix.trace_one, Fintype.card_fin] at h
  have hm : ((2*Q-2+1 : ℕ) : ℂ) = ((2*Q-2 : ℕ) : ℂ)+1 := by push_cast; rfl
  have hn : (((2*Q-2 : ℕ) : ℂ)+1) ≠ 0 := by
    rw [← hm]; exact_mod_cast (show 2*Q-2+1 ≠ 0 by omega)
  simpa only [hm, div_self hn, one_smul] using h

 

theorem fockAverage_pair_energy_scaled {Q p : ℕ} (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q ((pairAnnihilator Q p)ᴴ * pairAnnihilator Q p) =
      hamiltonian Q := by
  rw [fockAverage_pair_energy hQ hp, smul_smul]
  have hd : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  rw [one_div, mul_inv_cancel₀ hd, one_smul]

 

theorem fockAverage_pair_family {ι : Type*} [Fintype ι] {Q : ℕ}
    (hQ : 1 ≤ Q) (p : ι → ℕ) (hp : ∀ i, p i ≤ 2*Q-2) :
    fockAverage Q (∑ i, (pairAnnihilator Q (p i))ᴴ * pairAnnihilator Q (p i)) =
      ((Fintype.card ι : ℂ) / ((2*Q-1 : ℕ) : ℂ)) • hamiltonian Q := by
  rw [map_sum]
  simp_rw [fockAverage_pair_energy hQ (hp _)]
  rw [← Finset.sum_smul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

end LaughlinFock
end

end OAI
