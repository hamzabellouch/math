import OAI.Combinatorics.BalancedRyser.Selection.SelectionCylinder
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailCylinder
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailNumerics

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]

@[simp] theorem cylinderMass_failureLaw (G : Input I V) (J : Finset I) (a : I → V) :
    cylinderMass (failureLaw G) J a = 0 := by
  simp [cylinderMass, failureLaw]

section Nonempty
variable [Nonempty V]

theorem cylinderMass_terminalLaw_le_potential (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (J : Finset I) (a : I → V) (c : ℝ) (hc : 0 ≤ c)
    (hproduct : Real.exp (((J ∩ S.remaining).card : ℝ) / 2) *
      (∏ i ∈ J ∩ S.remaining, ((domain G S i).card : ℝ)⁻¹) ≤
        c ^ (J ∩ S.remaining).card) :
    cylinderMass (terminalLaw G hno S) J a ≤ cylinderPotential J a c S := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  unfold terminalLaw
  split
  · rename_i h
    by_cases ha : PrescriptionsAgree J a S
    · have hfixed : ∀ i ∈ J, i ∉ S.remaining → recordedAssignment S i = a i := by
        intro i hi hni
        exact Option.some.inj
          ((recordedAssignment_recorded G S h.1 i hni).symm.trans (ha i hi hni))
      rw [Tail.cylinderMass_completion_eq_ambient _ _ _ _ _ _ _ _ _ hfixed]
      rw [cylinderPotential, ite_eq_left ha]
      calc
        _ ≤ Real.exp (((Tail.residualIndices S J).card : ℝ) / 2) *
            (∏ i ∈ Tail.residualIndices S J, ((domain G S i.1).card : ℝ)⁻¹) :=
          Tail.conditionalAmbientCylinder_le_of_tailCheck G S hno h.2 _ _
        _ ≤ _ := by
          rw [Tail.card_residualIndices,
            Tail.prod_residualIndices S J (fun i => ((domain G S i).card : ℝ)⁻¹)]
          exact hproduct
    · have hbad : ¬ ∀ i ∈ J, i ∉ S.remaining → recordedAssignment S i = a i := by
        intro hfixed
        apply ha
        intro i hi hni
        rw [recordedAssignment_recorded G S h.1 i hni, hfixed i hi hni]
      rw [Tail.cylinderMass_completion_eq_zero_of_prefix_mismatch _ _ _ _ _ _ _ _ _ hbad]
      exact cylinderPotential_nonneg J a hc S
  · simpa only [cylinderMass_failureLaw] using cylinderPotential_nonneg J a hc S

theorem cylinderMass_sourceTerminalLaw_le_potential (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (S : State I V) (J : Finset I) (a : I → V)
    (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I))) :
    cylinderMass (sourceTerminalLaw p q G hno S) J a ≤
      cylinderPotential J a (cylinderConstant p / q) S := by
  have hcost : 0 ≤ cylinderConstant p / q :=
    div_nonneg (cylinderConstant_pos p).le (Nat.cast_nonneg q)
  by_cases ht : SourceTailCheck p q G S
  · rw [sourceTerminalLaw, ite_eq_left ht]
    apply cylinderMass_terminalLaw_le_potential G hno S J a _ hcost
    apply tail_product_source_bound p q hc hq (J ∩ S.remaining) (domain G S)
    intro i hi
    calc
      p.smin * p.c * q / 2 ≤
          p.sizeScale q (p.lastMainTime q (Fintype.card I)) * p.c * q / 2 := by
        gcongr
      _ ≤ _ := ht.2 i (Finset.mem_inter.mp hi).2
  · simpa only [sourceTerminalLaw, ite_eq_right ht, cylinderMass_failureLaw] using
      cylinderPotential_nonneg J a hcost S

theorem cylinderMass_sourceTerminalOutcomeLaw_le_potential (p : Parameters) (q : ℕ)
    (G : Input I V) (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (J : Finset I) (a : I → V) (hc : 0 < p.c) (hq : 0 < q)
    (hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I)))
    (out : Option (State I V)) :
    cylinderMass (sourceTerminalOutcomeLaw p q G hno out) J a ≤
      outcomePotential J a (cylinderConstant p / q) out := by
  cases out with
  | none => simp [sourceTerminalOutcomeLaw, outcomePotential]
  | some S =>
      exact cylinderMass_sourceTerminalLaw_le_potential p q G hno S J a hc hq hscale

theorem cylinderMass_finalLaw_source_bound (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (J : Finset I) (a : I → V) :
    cylinderMass (finalLaw p q G hG.2.1) J a ≤
      (cylinderConstant p / q) ^ J.card := by
  have hP : 0 ≤ p.Pstar := by
    unfold Parameters.Pstar
    have hc := hp.1
    have hC := hp.2.1
    positivity
  have hT : p.lastMainTime q (Fintype.card I) ≤ 3 * q := by
    calc
      p.lastMainTime q (Fintype.card I) ≤ Fintype.card I := Nat.sub_le _ _
      _ = 2 * (q + 1) := hG.1
      _ ≤ 3 * q := by omega
  have hscale : p.smin ≤ p.sizeScale q (p.lastMainTime q (Fintype.card I)) :=
    (SelectionScales.domain_bounds hP (by omega) hPq hT).1
  rw [cylinderMass_finalLaw]
  apply mainStageWeight_payoff_source_bound p q G J a hp hq hPq hG
  exact cylinderMass_sourceTerminalOutcomeLaw_le_potential p q G hG.2.1 J a
    hp.1 (by omega) hscale

end Nonempty

theorem cylinderMass_outputLaw_source_bound (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hq : 2 ≤ q)
    (hPq : 2 * p.Pstar ≤ q) (hG : GraphBounds G q p.c p.C)
    (J : Finset I) (a : I → V) :
    cylinderMass (outputLaw p q G hG.2.1) J a ≤
      (cylinderConstant p / q) ^ J.card := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact cylinderMass_finalLaw_source_bound p q G hp hq hPq hG J a

end
end Balanced.Selection.Process

end OAI
