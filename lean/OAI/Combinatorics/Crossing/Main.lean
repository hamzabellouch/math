import OAI.Combinatorics.Crossing.BalancedAxisCrossingCount

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem mainTarget_proof : MainTarget := by
  intro m n hm hn
  obtain ⟨R⟩ := nonempty_balancedAxisRealization m n
  exact ⟨⟨R.drawing,R.crossingCount_eq⟩,crossing_lower_bound m n⟩

theorem ordinary_crossing_number_eq (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ordinaryCrossingNumber m n=axisPairs m*axisPairs n := by
  obtain ⟨D,hD⟩ := (mainTarget_proof m n hm hn).1
  apply Nat.le_antisymm
  · calc
      ordinaryCrossingNumber m n ≤ crossingCount D := ordinaryCrossingNumber_le_count D
      _ = _ := hD
  · obtain ⟨A,hA⟩ := crossingCount_attainment D
    rw [← hA]
    exact crossing_lower_bound m n A

theorem ordinary_crossing_number_attained (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ D : AdmissibleDrawing m n, crossingCount D=ordinaryCrossingNumber m n ∧
      crossingCount D=axisPairs m*axisPairs n := by
  obtain ⟨D,hD⟩ := (mainTarget_proof m n hm hn).1
  exact ⟨D,by rw [ordinary_crossing_number_eq m n hm hn,hD],hD⟩

end Zarankiewicz

end

end OAI
