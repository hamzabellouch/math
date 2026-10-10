import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MeshRatioLabels

open Set MeasureTheory

noncomputable def binCount (S h : ℝ) : ℕ := ⌊S/h⌋₊
abbrev Label (S h : ℝ) := Fin (binCount S h+2)

noncomputable def cemeteryLabel (S h : ℝ) : Label S h := ⟨binCount S h+1,by omega⟩

noncomputable def ratioLabel (S h t : ℝ) : Label S h :=
  if t ≤ S then Fin.ofNat (binCount S h+2) ⌊t/h⌋₊ else cemeteryLabel S h

theorem ratioLabel_measurable (S h : ℝ) : Measurable (ratioLabel S h) := by
  have hm : Measurable (fun n : ℕ => Fin.ofNat (binCount S h+2) n) := measurable_of_countable _
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (hm.comp (Nat.measurable_floor.comp (measurable_id.div_const h))) measurable_const

theorem ratioLabel_val {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    (ratioLabel S h t).val = ⌊t/h⌋₊ := by
  rw [ratioLabel,ite_eq_left ht,Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_ne_cemetery {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    ratioLabel S h t ≠ cemeteryLabel S h := by
  intro heq
  have he := congrArg Fin.val heq
  rw [ratioLabel_val hh ht] at he
  change ⌊t/h⌋₊ = binCount S h+1 at he
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_eq_iff {S h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (htS : t ≤ S) (j : Label S h) :
    ratioLabel S h t = j ↔ (j.val : ℝ)*h ≤ t ∧ t < ((j.val : ℝ)+1)*h := by
  rw [Fin.ext_iff,ratioLabel_val hh htS,Nat.floor_eq_iff (div_nonneg ht0 hh.le),le_div_iff₀ hh,div_lt_iff₀ hh]

theorem matching_ratios_close {S h u v : ℝ} (hh : 0 < h) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huS : u ≤ S) (hvS : v ≤ S) (heq : ratioLabel S h u = ratioLabel S h v) : |u-v| < h := by
  have hu := (ratioLabel_eq_iff hh hu0 huS (ratioLabel S h v)).mp heq
  have hv := (ratioLabel_eq_iff hh hv0 hvS (ratioLabel S h v)).mp rfl
  rw [abs_lt]
  constructor <;> nlinarith [hu.1,hu.2,hv.1,hv.2]

theorem label_card_le {S h : ℝ} (hS : 0 ≤ S) (hh : 0 < h) :
    (Fintype.card (Label S h) : ℝ) ≤ S/h+2 := by
  have hc : Fintype.card (Label S h) = binCount S h+2 :=
    (Nat.card_eq_fintype_card (α := Label S h)).symm.trans (Nat.card_fin _)
  rw [hc]
  simp only [Nat.cast_add,Nat.cast_ofNat,binCount]
  linarith [Nat.floor_le (div_nonneg hS hh.le)]

end NumberTheoryLean.MeshRatioLabels

end

section

namespace NumberTheoryLean.MeshBoundaryGeometry

open Set MeshRatioLabels

noncomputable def lowerEdge {S mesh : ℝ} (j : Label S mesh) : ℝ := (j.val:ℝ)*mesh
noncomputable def upperEdge {S mesh : ℝ} (j : Label S mesh) : ℝ := ((j.val:ℝ)+1)*mesh

def fullCell {S mesh : ℝ} (Ld Lc Ud Uc : ℝ) (j : Label S mesh) : Prop :=
  max Ld Lc < lowerEdge j ∧ upperEdge j ≤ min Ud Uc

noncomputable def lowerPacket (mesh Ld Lc : ℝ) : Set ℝ := Icc (min Ld Lc) (max Ld Lc+mesh)
noncomputable def upperPacket (mesh Ud Uc : ℝ) : Set ℝ := Icc (min Ud Uc-mesh) (max Ud Uc)

theorem noninterior_in_packets {S mesh t Ld Lc Ud Uc : ℝ} (hm : 0 < mesh)
    (ht0 : 0 ≤ t) (htS : t ≤ S)
    (hvalid : (Ld ≤ t ∧ t ≤ Ud) ∨ (Lc ≤ t ∧ t ≤ Uc))
    (hbad : ¬fullCell Ld Lc Ud Uc (ratioLabel S mesh t)) :
    t ∈ lowerPacket mesh Ld Lc ∪ upperPacket mesh Ud Uc := by
  have hj := (ratioLabel_eq_iff hm ht0 htS (ratioLabel S mesh t)).mp rfl
  have hlo : min Ld Lc ≤ t := hvalid.elim (fun h => (min_le_left _ _).trans h.1)
    (fun h => (min_le_right _ _).trans h.1)
  have hup : t ≤ max Ud Uc := hvalid.elim (fun h => h.2.trans (le_max_left _ _))
    (fun h => h.2.trans (le_max_right _ _))
  have hwidth : upperEdge (ratioLabel S mesh t) = lowerEdge (ratioLabel S mesh t)+mesh := by
    unfold upperEdge lowerEdge
    ring
  change lowerEdge (ratioLabel S mesh t) ≤ t ∧ t < upperEdge (ratioLabel S mesh t) at hj
  by_cases hl : max Ld Lc < lowerEdge (ratioLabel S mesh t)
  · have hu : min Ud Uc < upperEdge (ratioLabel S mesh t) := by
      exact lt_of_not_ge (fun h => hbad ⟨hl,h⟩)
    exact Or.inr ⟨by linarith,hup⟩
  · exact Or.inl ⟨hlo,by linarith⟩

theorem lowerPacket_width (mesh Ld Lc : ℝ) :
    (max Ld Lc+mesh)-min Ld Lc = |Ld-Lc|+mesh := by
  rw [show max Ld Lc+mesh-min Ld Lc = max Ld Lc-min Ld Lc+mesh by ring,
    max_sub_min_eq_abs,abs_sub_comm]

theorem upperPacket_width (mesh Ud Uc : ℝ) :
    max Ud Uc-(min Ud Uc-mesh) = |Ud-Uc|+mesh := by
  rw [show max Ud Uc-(min Ud Uc-mesh) = max Ud Uc-min Ud Uc+mesh by ring,
    max_sub_min_eq_abs,abs_sub_comm]

theorem clipPacket {a b t : ℝ} (hab : a ≤ b) (ht : (1/2:ℝ) ≤ t) (hm : t ∈ Icc a b) :
    t ∈ Icc (max (1/2) a) (max (1/2) b) ∧
      max (1/2) b-max (1/2) a ≤ b-a := by
  refine ⟨⟨max_le ht hm.1,hm.2.trans (le_max_right _ _)⟩,?_⟩
  have h := abs_max_sub_max_le_abs b a (1/2:ℝ)
  rw [max_comm b (1/2),max_comm a (1/2),abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (max_le_max_left _ hab))] at h
  exact h

theorem clipped_packet_width {a b mesh d : ℝ} (hab : a ≤ b) (hwidth : b-a ≤ d+mesh) :
    0 < max (1/2:ℝ) a ∧ max (1/2:ℝ) a ≤ max (1/2:ℝ) b ∧
      max (1/2:ℝ) b-max (1/2:ℝ) a ≤ d+mesh := by
  refine ⟨lt_of_lt_of_le (by norm_num) (le_max_left _ _),max_le_max_left _ hab,?_⟩
  have h := abs_max_sub_max_le_abs b a (1/2:ℝ)
  rw [max_comm b (1/2),max_comm a (1/2),abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (sub_nonneg.mpr (max_le_max_left _ hab))] at h
  exact h.trans hwidth

end NumberTheoryLean.MeshBoundaryGeometry

end

end Erdos970

end OAI
