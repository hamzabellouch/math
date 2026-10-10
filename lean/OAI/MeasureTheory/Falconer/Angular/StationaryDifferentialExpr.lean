import OAI.MeasureTheory.Falconer.Angular.AngularDifferentialExpr
import OAI.MeasureTheory.Falconer.Angular.StationaryJetOperators

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def angularFiniteSum {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) : AngularDifferentialExpr :=
  AngularDifferentialExpr.sum (s.toList.map p)

theorem angularFiniteSum_apply {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (angularFiniteSum s p).apply f x = ∑ a ∈ s, (p a).apply f x := by
  simp [angularFiniteSum, AngularDifferentialExpr.sum_apply, List.map_map,
    Finset.sum_map_toList, Function.comp_def]

theorem angularFiniteSum_order {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (n : ℕ) (h : ∀ a ∈ s, (p a).order ≤ n) :
    (angularFiniteSum s p).order ≤ n := by
  apply AngularDifferentialExpr.sum_order_le
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact h a (Finset.mem_toList.mp ha)

noncomputable def stationaryLeadingConstant : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I)

theorem stationaryLeadingConstant_ne_zero : stationaryLeadingConstant ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  · exact Complex.exp_ne_zero _

noncomputable def stationaryJetExpr (n : ℕ) : AngularDifferentialExpr :=
  angularFiniteSum (Finset.range (n+1)) (fun k =>
    angularFiniteSum Finset.univ (fun c : OrderedFinpartition (n-k) =>
      .term ((n.choose k:ℂ) * iteratedDeriv k (fun u => (stationaryWeight u:ℂ)) 0 *
        ((∏ j, iteratedDeriv (c.partSize j) extendedStationaryInverse 0:ℝ):ℂ)) c.length))

theorem stationaryJetExpr_order (n : ℕ) : (stationaryJetExpr n).order ≤ n := by
  apply angularFiniteSum_order
  intro k hk
  apply angularFiniteSum_order
  intro c _
  exact stationaryJet_order hk c

theorem stationaryJetExpr_apply (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (stationaryJetExpr n).apply f x = stationaryJet n (fun u => f (u+x)) := by
  simp only [stationaryJetExpr, angularFiniteSum_apply, AngularDifferentialExpr.apply,
    stationaryJet, iteratedDeriv_comp_add_const, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

noncomputable def directStationaryExpr (j : ℕ) : AngularDifferentialExpr :=
  .comp (.term (stationaryLeadingConstant * (((j.factorial:ℝ)⁻¹:ℝ):ℂ) *
    (-Complex.I/2)^j) 0) (stationaryJetExpr (2*j))

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

theorem directStationaryExpr_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (directStationaryExpr j).apply f x = directStationaryOperator j f x := by
  simp [directStationaryExpr, AngularDifferentialExpr.apply, stationaryJetExpr_apply,
    directStationaryOperator, stationaryLeadingConstant]

end PlanarFalconer

end OAI
