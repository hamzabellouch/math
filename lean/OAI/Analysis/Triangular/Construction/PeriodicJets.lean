import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma P_periodic : Function.Periodic P 36 := by
  intro s
  unfold P
  apply Finset.prod_congr rfl
  intro a _
  unfold sineFactor
  have hh : (kappa:ℂ)*(s+36-(residue a:ℂ)) = (kappa:ℂ)*(s-(residue a:ℂ))+(Real.pi:ℂ) := by
    unfold kappa
    push_cast
    ring
  rw [hh,Complex.sin_add_pi]
  ring
lemma waveDerivative_periodic (k : ℕ) : Function.Periodic (waveDerivative k) 36 := by
  have he : (fun s : ℂ => P (s+36)) = P := funext P_periodic
  have hh := iteratedDeriv_comp_add_const k P 36
  rw [he] at hh
  rw [waveDerivative_eq_iterated]
  intro s
  exact (congrFun hh s).symm
lemma waveDerivative_emod (k : ℕ) (n : ℤ) : waveDerivative k n = waveDerivative k ((n%36:ℤ):ℂ) := by
  have hh := (waveDerivative_periodic k).int_mul (n/36) ((n%36:ℤ):ℂ)
  have hn : (((n%36:ℤ):ℂ)+(n/36:ℤ)*36) = (n:ℂ) := by
    exact_mod_cast (by simpa [mul_comm] using Int.emod_add_mul_ediv n 36)
  rw [hn] at hh
  exact hh
lemma Q_emod (n : ℤ) : Q n = Q (n%36) := by simp only [Q,waveDerivative_emod 2 n]
lemma D_emod (n : ℤ) : D n = D (n%36) := by simp only [D,waveDerivative_emod 3 n,Q_emod n]
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction
lemma Q_node_bounds (n : ℤ) (hn : n%36 ∈ residues) : (157/1000:ℝ)<Q n ∧ Q n<40 := by
  rw [Q_emod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h]
  all_goals first
    | exact Q_0_bounds | exact Q_1_bounds | exact Q_3_bounds | exact Q_4_bounds
    | exact Q_7_bounds | exact Q_9_bounds | exact Q_12_bounds | exact Q_13_bounds
    | exact Q_16_bounds | exact Q_19_bounds | exact Q_21_bounds | exact Q_25_bounds
    | exact Q_27_bounds | exact Q_28_bounds | exact Q_31_bounds
lemma D_node_bound (n : ℤ) (hn : n%36 ∈ residues) : |D n|<(283/100:ℝ) := by
  rw [D_emod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h]
  all_goals first
    | exact D_0_bound | exact D_1_bound | exact D_3_bound | exact D_4_bound
    | exact D_7_bound | exact D_9_bound | exact D_12_bound | exact D_13_bound
    | exact D_16_bound | exact D_19_bound | exact D_21_bound | exact D_25_bound
    | exact D_27_bound | exact D_28_bound | exact D_31_bound
end AtomicTriangular.FiniteCertificate
end

end OAI
