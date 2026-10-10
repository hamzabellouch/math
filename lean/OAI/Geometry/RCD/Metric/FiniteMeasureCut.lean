import OAI.Geometry.RCD.Sobolev.FiniteDirectedCut

namespace OAI

/-! # Quantitative separation of a measure on a finite product -/

open Set Filter MeasureTheory Finset Classical
noncomputable section
namespace RegularPointCoordinates
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finite_pair_measure_sum (σ : Measure (ι×ι)) [IsFiniteMeasure σ] (S : Set (ι×ι)) :
    σ.real S=∑ i, ∑ j, if (i,j)∈S then σ.real {(i,j)} else 0 := by
  classical
  symm
  rw [←Fintype.sum_prod_type (fun z : ι×ι => if z∈S then σ.real {z} else 0),
    ←Finset.sum_filter]
  rw [sum_measureReal_singleton]
  congr 1
  ext z
  simp

theorem finite_measure_cut_ge_quarter (σ : Measure (ι×ι)) [IsFiniteMeasure σ] :
    ∃ b : ι → Bool, σ.real {z : ι×ι | z.1≠z.2}/4 ≤
      σ.real {z : ι×ι | b z.1=true ∧ b z.2=false} := by
  classical
  let w : ι → ι → ℝ := fun i j => if i=j then 0 else σ.real {(i,j)}
  obtain ⟨b,hb⟩ := exists_directedCutWeight_ge_quarter w (by intro i; simp [w])
  refine ⟨b,?_⟩
  have htotal : (∑ i, ∑ j, w i j)=σ.real {z : ι×ι | z.1≠z.2} := by
    rw [finite_pair_measure_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i=j <;> simp [w,hij]
  have hcut : directedCutWeight w b=σ.real {z : ι×ι | b z.1=true ∧ b z.2=false} := by
    rw [finite_pair_measure_sum]
    unfold directedCutWeight
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i=j
    · subst j
      cases b i <;> simp [w]
    · simp [w,hij]
  rwa [htotal,hcut] at hb

end RegularPointCoordinates

end

end OAI
