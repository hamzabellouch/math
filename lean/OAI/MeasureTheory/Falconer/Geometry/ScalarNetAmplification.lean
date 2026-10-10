import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientClosure

namespace OAI

/-! Quadratic improvement of an interval net using one sum and product.
This is the final amplification step once a power-scale net is available. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_interval_net_amplify {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/8)
    (A : Finset ℝ) (hzero : 0 ∈ A)
    (hnet : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ a ∈ A, |x-a| ≤ η) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ y ∈ A+A*A, |x-y| ≤ 5*η^2 := by
  classical
  obtain ⟨a,ha,haerr⟩ := hnet (4*η) (by positivity) (by linarith)
  have hab : 3*η ≤ a ∧ a ≤ 5*η := by
    rw [abs_le] at haerr
    constructor <;> linarith
  have ha0 : 0 < a := by linarith [hab.1]
  have hlocal (x u : ℝ) (hu : u ∈ A) (hxu : 0 ≤ x-u) (hxua : x-u ≤ a) :
      ∃ y ∈ A+A*A, |x-y| ≤ 5*η^2 := by
    obtain ⟨b,hb,hberr⟩ := hnet ((x-u)/a) (div_nonneg hxu ha0.le)
      ((div_le_one ha0).2 hxua)
    refine ⟨u+a*b,Finset.add_mem_add hu (Finset.mul_mem_mul ha hb),?_⟩
    calc
      |x-(u+a*b)| = |a*((x-u)/a-b)| := by congr 1; field_simp; ring
      _ = a*|(x-u)/a-b| := by rw [abs_mul,abs_of_pos ha0]
      _ ≤ a*η := mul_le_mul_of_nonneg_left hberr ha0.le
      _ ≤ 5*η^2 := by nlinarith [mul_le_mul_of_nonneg_right hab.2 hη.le]
  intro x hx0 hx1
  by_cases hxa : x ≤ a
  · exact hlocal x 0 hzero (by simpa using hx0) (by simpa using hxa)
  · obtain ⟨u,hu,herr⟩ := hnet (x-2*η) (by linarith [hab.1]) (by linarith)
    rw [abs_le] at herr
    exact hlocal x u hu (by linarith) (by linarith [hab.1])

end Falconer

end OAI
