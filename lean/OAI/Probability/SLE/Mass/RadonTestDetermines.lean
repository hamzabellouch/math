import OAI.Probability.SLE.Mass.RadonTestLimit

namespace OAI

/-! The constructed countable local family determines a regular measure. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem LocalTestFamily.measure_eq_of_test_integrals (D : LocalTestFamily X)
    (μ ν : Measure X) [μ.Regular] [ν.Regular]
    (h : ∀ j, (∫ x, D.test j x ∂μ) = ∫ x, D.test j x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let M (n : ℕ) := if n % 2 = 0 then μ else ν
  let (n : ℕ) : IsFiniteMeasureOnCompacts (M n) := by
    dsimp only [M]
    split_ifs <;> infer_instance
  have hc : CauchySeq (fun n => ∫ x, f x ∂M n) := D.integrals_cauchy M (fun j => by
    refine ⟨∫ x, D.test j x ∂ν,?_⟩
    have he : (fun n => ∫ x, D.test j x ∂M n) = fun _ => ∫ x, D.test j x ∂ν := by
      funext n
      dsimp only [M]
      split_ifs
      · exact h j
      · rfl
    rw [he]
    exact tendsto_const_nhds) f
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  have hh := hN (2*N) (by omega) (2*N+1) (by omega)
  have hm0 : (2*N)%2=0 := by omega
  have hm1 : (2*N+1)%2≠0 := by omega
  simpa only [M,hm0,hm1,ite_true,ite_false,zero_add] using hh.le

end SLEExactGauge

end

end OAI
