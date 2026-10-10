import OAI.Combinatorics.Crossing.FiniteConePoint
import OAI.Combinatorics.Crossing.ConeIntersection

namespace OAI

noncomputable section
namespace Zarankiewicz

def PolygonLinePosition (v w : ℕ → Plane) (n m : ℕ) : Prop :=
  (∀ i : Fin n, ∀ j : Fin m, det2 (v (i.val+1)-v i.val) (w (j.val+1)-w j.val) ≠ 0) ∧
  (∀ i : Fin (n+1), ∀ j : Fin m, orient2 (w j.val) (w (j.val+1)) (v i.val) ≠ 0) ∧
  (∀ i : Fin n, ∀ j : Fin (m+1), orient2 (v i.val) (v (i.val+1)) (w j.val) ≠ 0)

theorem polygon_intersection_zero_in_line_position (v w : ℕ → Plane) (n m : ℕ)
    (hc : v n = v 0) (hd : w m = w 0)
    (hv : ∀ i : Fin n, v (i.val+1) ≠ v i.val)
    (hw : ∀ j : Fin m, w (j.val+1) ≠ w j.val)
    (hvw : ∀ i : Fin (n+1), ∀ j : Fin (m+1), w j.val ≠ v i.val)
    (hp : PolygonLinePosition v w n m) : polygonIntersection v w n m = 0 := by
  obtain ⟨o,ha,hb,hpar,hcorn⟩ := exists_polygon_cone_point v w n m hv hw hvw
  apply polygon_intersection_zero_of_cone v w n m hc hd o
  · intro i hi
    exact ha ⟨i,Finset.mem_range.mp hi⟩
  · intro i hi j hj
    have hin := Finset.mem_range.mp hi
    have hjm := Finset.mem_range.mp hj
    let ii : Fin n := ⟨i,Finset.mem_range.mp hi⟩
    let jj : Fin m := ⟨j,Finset.mem_range.mp hj⟩
    let i₀ : Fin (n+1) := ⟨i,by omega⟩
    let i₁ : Fin (n+1) := ⟨i+1,by omega⟩
    let j₀ : Fin (m+1) := ⟨j,by omega⟩
    let j₁ : Fin (m+1) := ⟨j+1,by omega⟩
    refine ⟨?_,?_,?_⟩
    · intro k
      fin_cases k
      · exact hpar i₀ jj
      · exact hp.1 ii jj
      · change det2 (o-v (i+1)) (w (j+1)-w j) ≠ 0
        rw [det2_reverse_edge o (v (i+1)) (w j) (w (j+1))]
        exact neg_ne_zero.mpr (hpar i₁ jj)
    · intro k
      fin_cases k
      · exact hb jj
      · exact hp.2.1 i₀ jj
      · exact hp.2.1 i₁ jj
    · intro k
      fin_cases k
      · exact ⟨hcorn i₀ j₀,hcorn i₀ j₁⟩
      · exact ⟨hp.2.2 ii j₀,hp.2.2 ii j₁⟩
      · change orient2 (v (i+1)) o (w j) ≠ 0 ∧ orient2 (v (i+1)) o (w (j+1)) ≠ 0
        rw [orient2_reverse_edge o _ _,orient2_reverse_edge o _ _]
        exact ⟨neg_ne_zero.mpr (hcorn i₁ j₀),neg_ne_zero.mpr (hcorn i₁ j₁)⟩

end Zarankiewicz

end

end OAI
