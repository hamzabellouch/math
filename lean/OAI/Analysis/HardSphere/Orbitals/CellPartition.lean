import Mathlib
import OAI.Analysis.HardSphere.Orbitals.CenteredCell
import OAI.Analysis.HardSphere.Geometry.SelectedUnitCellPenalty

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace HardSphere.CellOrbital

def gridHome {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (x : Torus L) : Fin 3→Fin K :=
  fun j ↦ unitIndex hL (x j+(1/2:ℝ))

lemma gridHome_measurable {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) : Measurable (gridHome hL) := by
  exact Measurable.of_eval (fun j ↦ (measurable_unitIndex hL).comp ((measurable_pi_apply j).add_const _))

lemma gridHome_mem {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K) (x : Torus L) :
    x∈centeredCell L (gridCenter L (gridHome hL x)) := by
  apply (centeredCell_image (by rw [hL]; exact_mod_cast hK) _ _).mpr
  intro j
  let z := (AddCircle.equivIco L.val 0) (x j+(1/2:ℝ))
  have hz0 : 0≤z.val := z.property.1
  let n : ℕ := ⌊z.val⌋₊
  refine ⟨z.val-(n:ℝ)-1/2,⟨?_,?_⟩,?_⟩
  · linarith [Nat.floor_le hz0]
  · have hh := Nat.lt_floor_add_one z.val
    dsimp [n]
    linarith
  · have he : (z.val : AddCircle L.val)=x j+((1/2:ℝ):AddCircle L.val) := AddCircle.coe_equivIco
    change ((z.val-(n:ℝ)-1/2:ℝ):AddCircle L.val)=x j-((n:ℝ):AddCircle L.val)
    simp only [QuotientAddGroup.mk_sub]
    rw [he]
    abel

lemma centeredCell_disjoint {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {v w : Fin 3→Fin K} (hvw : v≠w) : Disjoint (centeredCell L (gridCenter L v)) (centeredCell L (gridCenter L w)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj⟩ : ∃j,v j≠w j := by
    by_contra h
    push Not at h
    exact hvw (funext h)
  have h1 : 1≤L.val := by rw [hL]; exact_mod_cast hK
  obtain ⟨s,hs,hes⟩ := (centeredCell_image h1 _ _).mp hx j
  obtain ⟨t,ht,het⟩ := (centeredCell_image h1 _ _).mp hy j
  have he : gridCenter L v j-gridCenter L w j=((t-s:ℝ):AddCircle L.val) := by
    rw [QuotientAddGroup.mk_sub,het,hes]
    abel
  have ha : |t-s|<1 := by rw [abs_lt]; constructor <;> linarith [ht.1,ht.2,hs.1,hs.2]
  have hd : dist (gridCenter L v j) (gridCenter L w j)<1 := by
    rw [dist_eq_norm,he]
    exact lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm (m:=t-s)) (by simpa only [Real.norm_eq_abs] using ha)
  exact (not_lt_of_ge (fin_circle_dist hL hj)) hd

lemma gridHome_eq_iff {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (x : Torus L) (v : Fin 3→Fin K) : gridHome hL x=v ↔ x∈centeredCell L (gridCenter L v) := by
  constructor
  · intro h; exact h ▸ gridHome_mem hL hK x
  · intro hx
    by_contra h
    exact Set.disjoint_left.mp (centeredCell_disjoint hL hK h) (gridHome_mem hL hK x) hx

end HardSphere.CellOrbital

end
end

end

end OAI
