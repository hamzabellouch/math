import OAI.MeasureTheory.Falconer.Recursion.RetainedProfileBounds
import OAI.MeasureTheory.Falconer.Geometry.HalfSlopeGrid
import OAI.MeasureTheory.Falconer.Estimates.PlanarQuarter

namespace OAI

/-! A fixed quarter chart closes under the actual local cell map. Its
contraction does not accumulate with the number of selected intervals. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

noncomputable def quarterEndpointPoint (Q : DyadicCube 2) (a : ℕ)
    (p₀ r : CellPath 2) : Space 2 :=
  localPacketPoint (4/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
    (Q.descendant r).center

noncomputable def quarterEndpointSet (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) : Finset (Space 2) :=
  (prefixChildren C a b p₀).image (quarterEndpointPoint Q a p₀)

theorem quarterEndpointPoint_eq (Q : DyadicCube 2) (a : ℕ) (p₀ r : CellPath 2) :
    quarterEndpointPoint Q a p₀ r = planarQuarter
      (localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
        (Q.descendant r).center) := by
  ext i
  rw [planarQuarter_apply]
  fin_cases i <;> dsimp [quarterEndpointPoint,localPacketPoint] <;> ring

theorem quarterEndpointSet_eq (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) :
    quarterEndpointSet Q C a b p₀ = (blockEndpointSet Q C a b p₀).image planarQuarter := by
  simp only [quarterEndpointSet,blockEndpointSet,Finset.image_image,Function.comp_def]
  congr 1
  funext r
  exact quarterEndpointPoint_eq Q a p₀ r

theorem quarterEndpointPoint_dist (Q : DyadicCube 2) (a : ℕ) (p₀ r t : CellPath 2) :
    dist (quarterEndpointPoint Q a p₀ r) (quarterEndpointPoint Q a p₀ t) =
      dist (Q.descendant r).center (Q.descendant t).center/(4/(2:ℝ)^a) := by
  exact localPacketPoint_dist (by positivity) _ _ _ _

theorem quarterEndpointPoint_injOn {N : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (a : ℕ) (p₀ : CellPath 2) : Set.InjOn (quarterEndpointPoint Q a p₀) (cubePaths 2 N) := by
  intro r hr t ht he
  have hh := localPacketPoint_injective (by positivity : 0 < 4/(2:ℝ)^a)
    ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1) he
  exact Q.center_injective_at_depth hQ ((mem_cubePaths _ _ _).mp hr)
    ((mem_cubePaths _ _ _).mp ht) hh

theorem quarterEndpointSet_geometry {N a b : ℕ} (Q : DyadicCube 2) (hQ : Q.side = 1)
    (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    (quarterEndpointSet Q C a b p₀).card = (prefixChildren C a b p₀).card ∧
    (∀ x ∈ quarterEndpointSet Q C a b p₀, |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4) ∧
    FiniteSeparatedAt (1/(2:ℝ)^(b-a+2)) (quarterEndpointSet Q C a b p₀) := by
  obtain ⟨hcard,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ C hC hab hbN p₀
  rw [quarterEndpointSet_eq]
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ planarQuarter_injective]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := hchart z hz
    constructor
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.1]
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.2]
  · have he : (1/(2:ℝ)^(b-a))/4 = 1/(2:ℝ)^(b-a+2) := by
      rw [pow_add]
      norm_num
      ring
    rw [← he]
    exact planarQuarter_separated _ hsep

theorem quarterEndpointPoint_local {a b : ℕ} (hab : a ≤ b) (Q : DyadicCube 2)
    (p₀ q r : CellPath 2) :
    localPacketPoint (4*(1/(2:ℝ)^(b-a+2)))
      (quarterEndpointPoint Q a p₀ q 0) (quarterEndpointPoint Q a p₀ q 1)
      (quarterEndpointPoint Q a p₀ r) = quarterEndpointPoint Q b q r := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  ext i
  fin_cases i <;> dsimp [quarterEndpointPoint,localPacketPoint] <;>
    rw [hp,pow_add] <;> norm_num <;> field_simp <;> ring

theorem quarterEndpointPoint_near {b c : ℕ} (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (a : ℕ) (p₀ r : CellPath 2)
    (hr : r ∈ cubePaths 2 b) :
    dist (quarterEndpointPoint Q a p₀ r) (quarterEndpointPoint Q a p₀ (r.take c)) ≤
      (1/(2:ℝ)^c)/(4/(2:ℝ)^a) := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant (r.take c)).side = 1/(2:ℝ)^c := by
    rw [Q.descendant_side,List.length_take,(mem_cubePaths _ _ _).mp hr,Nat.min_eq_left hcb,hQ]
  have hh := (Q.descendant (r.take c)).center_distance_bound
    (Q.descendant_side_pos hQpos _).le (Q.center_mem_ancestor hQpos r c)
  rw [hside] at hh
  rw [quarterEndpointPoint_dist]
  exact div_le_div_of_nonneg_right hh (by positivity)

end Falconer

end OAI
