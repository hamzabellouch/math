import OAI.Analysis.Laughlin.Asymptotics.ScalarBudget
import OAI.Analysis.Laughlin.ThreeBody.PhysicalTrace

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def threeBodyDimensionRatio (Q z : ℕ) : ℝ :=
  (3*(Q : ℝ)-1-2*z)/(2*(Q : ℝ)-1)

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q => threeBodyDimensionRatio Q z) atTop (𝓝 (3/2 : ℝ)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  convert h using 1
  ext Q
  unfold threeBodyDimensionRatio
  congr 1 <;> ring

theorem source_threeBody_trace_strict_eventually (z : ℕ)
    (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    ∀ᶠ Q : ℕ in atTop, physicalThreeBodyTraceFormula Q z <
      threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z := by
  have h := ((threeBodyDimensionRatio_tendsto z).mul (gramEigenvalueFormula_tendsto z)).sub
    (source_physical_threeBody_trace_formula_tendsto z)
  have hl : 0 < (3/2 : ℝ)*((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)-(Certificate.e z : ℝ) := by
    have hh := three_body_real z hz
    nlinarith only [hh]
  exact ((tendsto_order.mp h).1 0 hl).mono (fun Q hQ => by linarith)

theorem eventually_list_all {I : Type*} (l : List I) (P : ℕ → I → Prop)
    (h : ∀ i ∈ l, ∀ᶠ Q in atTop, P Q i) : ∀ᶠ Q in atTop, ∀ i ∈ l, P Q i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    filter_upwards [h a (by simp),ih (fun i hi => h i (by simp [hi]))] with Q ha hl
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ha
    · exact hl i hi

theorem source_threeBody_physical_traces_strict_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ z : Fin (Q+1),
      z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] →
      Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) <
        threeBodyDimensionRatio Q z.val * gramEigenvalueFormula Q z.val := by
  have hall := eventually_list_all [2,4,5,6,7,8,9,10,11,12,13,14,15]
    (fun Q z => physicalThreeBodyTraceFormula Q z < threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z)
    source_threeBody_trace_strict_eventually
  filter_upwards [eventually_ge_atTop 15,hall] with Q hQ h
  refine ⟨hQ,?_⟩
  intro z hz
  rw [source_physical_threeBody_trace_identity Q hQ]
  exact h z.val hz

end Laughlin.Spin

end OAI
