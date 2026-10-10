import OAI.Combinatorics.PolynomialVacuum.Cylinder.BridgeMass
import OAI.Combinatorics.PolynomialVacuum.Bridge.HalfPlaneArchMass

namespace OAI

namespace PolynomialVacuumBridge.Corridor
open Filter
open scoped Topology
open PolynomialVacuumCylinder

 

theorem summable_height_tail_tendsto {α : Type*} (height : α → ℕ) (f : α → ℝ)
    (hf : Summable f) (hpos : ∀ a,0≤f a) :
    Tendsto (fun H : ℕ => ∑' a,if H≤height a then f a else 0) atTop (nhds 0) := by
  classical
  have hp : ∀ a, Tendsto (fun H : ℕ => if H≤height a then f a else 0) atTop (nhds 0) := by
    intro a
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (height a)] with H hH
    simp [not_le.mpr hH]
  have hdom : ∀ᶠ H in atTop,∀ a,‖(if H≤height a then f a else 0)‖≤f a := by
    apply Eventually.of_forall
    intro H a
    split_ifs <;> simp [Real.norm_eq_abs,abs_of_nonneg (hpos a),hpos a]
  simpa using tendsto_tsum_of_dominated_convergence hf hp hdom

namespace BridgeWord
noncomputable def cylinderHeightTail (M H : ℕ) : ℝ :=
  ∑' A : CylinderBridge M,if H≤A.val.height then mass A.val else 0
noncomputable def cylinderHeightMass (M H : ℕ) : ℝ :=
  ∑' A : CylinderBridge M,if H=A.val.height then mass A.val else 0

theorem cylinder_height_tail_tendsto (M : ℕ) (hM : 0<M) :
    Tendsto (cylinderHeightTail M) atTop (nhds 0) :=
  summable_height_tail_tendsto (fun A : CylinderBridge M => A.val.height) _
    (cylinder_bridge_mass_summable M hM) (fun A => (mass_pos A.val).le)

theorem cylinder_height_mass_tendsto (M : ℕ) (hM : 0<M) :
    Tendsto (cylinderHeightMass M) atTop (nhds 0) := by
  apply squeeze_zero (fun H => tsum_nonneg (fun A => by split_ifs <;> first | exact (mass_pos A.val).le | rfl))
    (fun H => ?_) (cylinder_height_tail_tendsto M hM)
  dsimp only [cylinderHeightMass,cylinderHeightTail]
  apply Summable.tsum_le_tsum
  · intro A
    split_ifs with he hle hle <;> first | rfl | exact (mass_pos A.val).le | omega
  · apply (cylinder_bridge_mass_summable M hM).of_nonneg_of_le
    · intro A; split_ifs <;> first | exact (mass_pos A.val).le | rfl
    · intro A; split_ifs <;> first | rfl | exact (mass_pos A.val).le
  · apply (cylinder_bridge_mass_summable M hM).of_nonneg_of_le
    · intro A; split_ifs <;> first | exact (mass_pos A.val).le | rfl
    · intro A; split_ifs <;> first | rfl | exact (mass_pos A.val).le
end BridgeWord

namespace ArchWord
noncomputable def height (A : ArchWord) : ℕ :=
  (traced bottomSource A.word).toFinset.sup (fun v => (boxIndex v 0).toNat)+1

theorem layer_lt_height (A : ArchWord) (v : PolynomialVacuumBridge.Corridor.Vertex)
    (hv : v∈traced bottomSource A.word) : boxIndex v 0 < A.height := by
  have hh := Finset.le_sup (f := fun v => (boxIndex v 0).toNat) (List.mem_toFinset.mpr hv)
  have hn := A.inHalfPlane v hv
  unfold height
  omega

def CylinderSafe (M : ℕ) (A : ArchWord) : Prop :=
  ((traced bottomSource A.word).map (projectVertex M)).Nodup
abbrev CylinderArch (M : ℕ) := {A : ArchWord // CylinderSafe M A}

theorem cylinder_arch_mass_summable (M : ℕ) :
    Summable (fun A : CylinderArch M => mass A.val) := mass_summable.subtype _

noncomputable def cylinderHeightTail (M H : ℕ) : ℝ :=
  ∑' A : CylinderArch M,if H≤A.val.height then mass A.val else 0

theorem cylinder_height_tail_tendsto (M : ℕ) : Tendsto (cylinderHeightTail M) atTop (nhds 0) :=
  summable_height_tail_tendsto (fun A : CylinderArch M => A.val.height) _
    (cylinder_arch_mass_summable M) (fun A => (mass_pos A.val).le)

end ArchWord
end PolynomialVacuumBridge.Corridor

end OAI
