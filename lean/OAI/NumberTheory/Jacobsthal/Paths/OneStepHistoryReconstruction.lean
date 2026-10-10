import OAI.NumberTheory.Jacobsthal.Renewal.CompletedCycleFirstArrival

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures

def appendRawState (a : ℕ) (past : RawHistory a) (s : CostState) : RawHistory (a+1) :=
  fun i => if hi : i.1 ≤ a then past ⟨i.1,Finset.mem_Iic.mpr hi⟩ else s

lemma appendRawState_measurable (a : ℕ) (past : RawHistory a) : Measurable (appendRawState a past) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i.1 ≤ a
  · simp only [appendRawState,dite_eq_left hi]
    exact measurable_const
  · simp only [appendRawState,dite_eq_right hi]
    exact measurable_id

lemma appendRawState_reconstruct (a : ℕ) (past : RawHistory a) (h : RawHistory (a+1))
    (hp : rawPrefix (show a ≤ a+1 by omega) h=past) : appendRawState a past (rawLast (a+1) h)=h := by
  funext i
  by_cases hi : i.1 ≤ a
  · rw [appendRawState,dite_eq_left hi]
    exact (congrFun hp (⟨i.1,Finset.mem_Iic.mpr hi⟩ : Finset.Iic a)).symm
  · rw [appendRawState,dite_eq_right hi]
    have hin : i.1=a+1 := by have := Finset.mem_Iic.mp i.2; omega
    have he : i=⟨a+1,by simp⟩ := Subtype.ext hin
    rw [he]
    rfl

theorem oneStep_measure_reconstruct (a : ℕ) (past : RawHistory a) (μ : Measure (RawHistory (a+1)))
    (hp : ∀ᵐ h ∂μ, rawPrefix (show a ≤ a+1 by omega) h=past) :
    μ=(μ.map (rawLast (a+1))).map (appendRawState a past) := by
  rw [Measure.map_map (appendRawState_measurable a past) (rawLast_measurable (a+1))]
  have he : appendRawState a past ∘ rawLast (a+1) =ᵐ[μ] id := by
    filter_upwards [hp] with h hh
    exact appendRawState_reconstruct a past h hh
  rw [Measure.map_congr he,Measure.map_id]

lemma oneStep_measure_eq_of_last (a : ℕ) (past : RawHistory a)
    (μ ν : Measure (RawHistory (a+1)))
    (hμ : ∀ᵐ h ∂μ, rawPrefix (show a ≤ a+1 by omega) h=past)
    (hν : ∀ᵐ h ∂ν, rawPrefix (show a ≤ a+1 by omega) h=past)
    (he : μ.map (rawLast (a+1))=ν.map (rawLast (a+1))) : μ=ν := by
  rw [oneStep_measure_reconstruct a past μ hμ,oneStep_measure_reconstruct a past ν hν,he]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
