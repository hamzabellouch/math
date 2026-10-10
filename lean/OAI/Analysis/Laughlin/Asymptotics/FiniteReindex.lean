import OAI.Analysis.Laughlin.Asymptotics.Convergence

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem deltaFormula_eq_odd_finite_sum (Q : ℕ) :
    deltaFormula Q = ∑ z ∈ (Finset.range (Q+1)).filter (fun z => 17 ≤ z ∧ Odd z), tailWeight Q z := by
  rw [deltaFormula_eq_finite_sum]
  simp only [deltaTerm]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun z hz => (z-17)/2)
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_range] at hz ⊢
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    omega
  · intro z hz w hw he
    simp only [Finset.mem_filter,Finset.mem_range] at hz hw
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    obtain ⟨n,hn⟩ := (odd_tail_index_iff w).mp hw.2
    omega
  · intro m hm
    simp only [Finset.mem_filter,Finset.mem_range] at hm
    refine ⟨17+2*m,?_,by omega⟩
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,(odd_tail_index_iff _).mpr ⟨m,rfl⟩⟩
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_range] at hz
    obtain ⟨m,hm⟩ := (odd_tail_index_iff z).mp hz.2
    congr 1
    omega

end Laughlin

end OAI
