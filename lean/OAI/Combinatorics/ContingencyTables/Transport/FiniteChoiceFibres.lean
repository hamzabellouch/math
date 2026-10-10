import OAI.Combinatorics.ContingencyTables.Transport.FinitePartitionVariance

namespace OAI

/-! # Finite fibre sums with their literal subtype enumeration -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

lemma double_fibreWeight_mul {X C D : Type*} (w H : X → ℝ)
    (π : X → C) (ρ : X → D) (c : C) (d : D) (x : X) :
    fibreWeight (fibreWeight (fun a => w a*H a) π c) ρ d x=
      fibreWeight (fibreWeight w π c) ρ d x*H x := by
  rw [fibreWeight_pair,fibreWeight_mul,← fibreWeight_pair]

theorem double_fibre_sum {X C D : Type*} [Fintype X]
    (w : X → ℝ) (π : X → C) (ρ : X → D) (c : C) (d : D)
    [Fintype {x : X // π x=c ∧ ρ x=d}] :
    (∑ x,fibreWeight (fibreWeight w π c) ρ d x)=
      ∑ x : {x : X // π x=c ∧ ρ x=d},w x.val := by
  have he (x : X) : fibreWeight (fibreWeight w π c) ρ d x=
      if π x=c ∧ ρ x=d then w x else 0 := by
    unfold fibreWeight
    by_cases hp : π x=c <;> by_cases hρ : ρ x=d <;>
      simp only [hp,hρ,↓reduceIte,and_self,false_and,and_false]
  calc
    _ = ∑ x,if π x=c ∧ ρ x=d then w x else 0 := Finset.sum_congr rfl (fun x _ => he x)
    _ = ∑ x ∈ Finset.univ.filter (fun x => π x=c ∧ ρ x=d),w x := (Finset.sum_filter _ _).symm
    _ = _ := Finset.sum_subtype _ (by simp) w

end ContingencyTables.FiniteExposureVariance

end OAI
