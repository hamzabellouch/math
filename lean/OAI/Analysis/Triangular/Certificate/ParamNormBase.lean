import OAI.Analysis.Triangular.Certificate.PolytopeInterval

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def rowAbsNumerator (a : Fin 8 → RI) : ℤ :=
  max (-(rowLowerBox a).lo) (-(rowLowerBox (fun i => (a i).neg)).lo)
lemma rowAbs_bound {a : Fin 8 → RI} {v : Fin 8 → ℝ}
    (hv : ∀ j, (a j).Mem (v j)) (e : Fin 8 → ℝ) (he : ParameterPolytope e) :
    |∑ j : Fin 8, v j*e j| ≤ (rowAbsNumerator a : ℝ)/scale := by
  have h1 := (rowLowerBox_mem hv).1
  have h2 := (rowLowerBox_mem (fun j => RI.mem_neg (hv j))).1
  have h3 := rowLower_le v e he
  have h4 := rowLower_le (fun j => -v j) e he
  have heq : (∑ j : Fin 8, -v j*e j) = -(∑ j : Fin 8, v j*e j) := by simp only [neg_mul,Finset.sum_neg_distrib]
  rw [heq] at h4
  have hb1 : (-(rowLowerBox a).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_left (-(rowLowerBox a).lo) _)
  have hb2 : (-(rowLowerBox (fun j => (a j).neg)).lo:ℝ) ≤ (rowAbsNumerator a:ℝ) := by
    exact_mod_cast (le_max_right (-(rowLowerBox a).lo) _)
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h3 scale_pos.le
    nlinarith
  · apply (le_div_iff₀ scale_pos).mpr
    have hg := mul_le_mul_of_nonneg_left h4 scale_pos.le
    nlinarith
end AtomicTriangular.FiniteCertificate
end

end OAI
