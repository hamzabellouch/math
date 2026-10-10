import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmallComponent
import OAI.Analysis.HardSphere.Geometry.GridCorner
import OAI.Analysis.HardSphere.Thermodynamics.FiniteScaledBox

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma not_small_has_exit {B : Set Vertex} {C : Finset Vertex} {z : Vertex} {h : ℝ}
    (hh : 0 < h) (hC : IsBadComponent B C) (hz : z ∈ C) (hlarge : ¬ SmallComponent h C) :
    ∃ w, withinReach starStep B z w ∧ ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
  classical
  have hex : ∃ w ∈ C, ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
    by_contra hn
    push Not at hn
    apply hlarge
    intro u hu v hv i
    have hu' := hn u hu i
    have hv' := hn v hv i
    have ht := abs_sub_le (u i : ℝ) (z i) (v i)
    rw [abs_sub_comm (z i : ℝ) (v i)] at ht
    have hm := mul_le_mul_of_nonneg_left ht hh.le
    nlinarith
  obtain ⟨w,hw,i,hi⟩ := hex
  exact ⟨w,withinReach_mono hC.subset (hC.connected z hz w hw),i,hi⟩

theorem large_component_witnesses {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhr : h ≤ r) (hrh : r ≤ 2*h) (hr : r ≤ 1/4096)
    (hperiod : L.val = h * J) (hL : 10 < L.val)
    (Y : Configuration n L) {z : Vertex} (hz : z ∈ bad h r Y)
    (hlarge : ¬ (liftedBadComponent (bad h r Y) z).Finite ∨
      ∃ C, IsBadComponent (bad h r Y) C ∧ z ∈ C ∧ ¬ SmallComponent h C) :
    ∃ A : Finset (Fin n),
      (1:ℝ)/1372 ≤ r * A.card ∧
      (∀ i ∈ A, torusDistance L (Y i) (gridCorner L h z) ≤ 1) ∧
      (∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) := by
  have hex : ∃ w, withinReach starStep (bad h r Y) z w ∧
      ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
    rcases hlarge with hinf | ⟨C,hC,hzC,hClarge⟩
    · exact infinite_component_has_exit hh hinf
    · exact not_small_has_exit hh hC hzC hClarge
  obtain ⟨w,hp,hw⟩ := hex
  exact first_exit_witnesses hh hhr hrh hr hperiod hL Y hz hp hw

def microPeriod (r : ℝ) : ℕ := ⌈1/r⌉₊
def microMesh (r : ℝ) : ℝ := 1/(microPeriod r : ℝ)

lemma microPeriod_pos {r : ℝ} (hr : 0 < r) : 0 < microPeriod r := by
  exact Nat.ceil_pos.mpr (by positivity)

lemma microMesh_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < microMesh r ∧ microMesh r ≤ r ∧ r ≤ 2*microMesh r := by
  have hq : (0:ℝ) < microPeriod r := by exact_mod_cast microPeriod_pos hr
  have hceil : 1/r ≤ (microPeriod r : ℝ) := Nat.le_ceil _
  have hceil' : (microPeriod r : ℝ) < 1/r + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hcr := (div_le_iff₀ hr).mp hceil
  have hcr' := (lt_div_iff₀ hr).mp (show (microPeriod r : ℝ)-1 < 1/r by linarith)
  refine ⟨one_div_pos.mpr hq,?_,?_⟩
  · exact (div_le_iff₀ hq).mpr (by nlinarith)
  · change r ≤ 2*(1/(microPeriod r : ℝ))
    rw [← div_eq_mul_one_div]
    exact (le_div_iff₀ hq).mpr (by nlinarith)

end HardSphere.BathSlice

end

end OAI
