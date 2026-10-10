import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicNumber
import OAI.Analysis.CoulombRadii.SpectralTheory.StrictBinding

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma atom_strict_sector_bound (Z:ℕ) (hZ:1≤Z) {n:ℕ} (hn:0<n)
    (h:sectorFormBottom (atom Z hZ) n<sectorFormBottom (atom Z hZ) (n-1)):
    n≤3*Z := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k] at h ⊢
  rw [Nat.add_comm k 1] at h ⊢
  obtain ⟨u,ha,hm,he⟩:=atom_strict_binding_attained Z hZ (by omega : 0<1+k) h
  have H:=atom_minimizer_number_bound Z hZ u ha hm he
  omega
lemma atom_global_sector_minimum (Z:ℕ) (hZ:1≤Z):
    ∃ n:ℕ,0<n ∧ n≤3*Z ∧ ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=unrestrictedFormBottom (atom Z hZ) := by
  let E:ℕ → EReal:=sectorFormBottom (atom Z hZ)
  let A:= (Finset.range (3*Z+1)).filter (fun n => 0<n ∧ E n<E (n-1))
  have h1:E 1<E 0 := by
    dsimp [E]
    rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,
      NeutralAtom.sectorEnergy_vacuum]
    exact NeutralAtom.sectorEnergy_one_neg Z hZ
  have hA:A.Nonempty := by
    refine ⟨1,?_⟩
    rw [Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,by norm_num; exact h1⟩
  let N:=A.max' hA
  have hN:N∈A:=Finset.max'_mem A hA
  have hn:0<N ∧ E N<E (N-1):=(Finset.mem_filter.mp hN).2
  have hNb:N≤3*Z:=by have H: N<3*Z+1:=Finset.mem_range.mp (Finset.mem_filter.mp hN).1; omega
  have hmax:∀ n,0<n → E n<E (n-1) → n≤N := by
    intro n hn hs
    apply Finset.le_max'
    rw [Finset.mem_filter,Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (atom_strict_sector_bound Z hZ hn hs),hn,hs⟩
  have hplateau:∀ d,E (N+d)=E N := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hle:E (N+(d+1))≤E (N+d):=atom_sectorFormBottom_antitone Z hZ (by omega)
      have hnlt:¬E (N+(d+1))<E (N+d) := by
        intro H
        have hh:=hmax (N+(d+1)) (by omega) (by simpa using H)
        omega
      exact (le_antisymm hle (le_of_not_gt hnlt)).trans ih
  have hglobal:E N=unrestrictedFormBottom (atom Z hZ) := by
    apply le_antisymm
    · apply le_iInf
      intro n
      by_cases hn:n≤N
      · exact atom_sectorFormBottom_antitone Z hZ hn
      · obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le (le_of_not_ge hn)
        exact (hplateau d).ge
    · exact iInf_le E N
  obtain ⟨u,ha,hm,he⟩:=atom_strict_binding_attained Z hZ hn.1 hn.2
  exact ⟨N,hn.1,hNb,u,ha,hm,he.trans hglobal⟩
end Coulomb
end

end

end OAI
