import Mathlib

namespace OAI

section


/-! Explicit prism retraction proving the cubical homotopy extension geometry.
All maps use the actual interval and product/subspace topologies. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.CubicalHomotopyExtension
attribute [local instance] Classical.propDecidable
variable {N : Type*} [Fintype N]

def radius (x : N → I) : ℝ := 2 * ‖fun i => (x i : ℝ) - 1 / 2‖

lemma radius_continuous : Continuous (radius (N := N)) := by
  unfold radius
  fun_prop

lemma radius_nonneg (x : N → I) : 0 ≤ radius x := by
  unfold radius; positivity

lemma radius_le_one (x : N → I) : radius x ≤ 1 := by
  have hn : ‖fun i => (x i : ℝ) - 1 / 2‖ ≤ (1 / 2 : ℝ) := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [(x i).property.1,(x i).property.2]
  unfold radius
  linarith

lemma coord_le_radius (x : N → I) (i : N) : |(x i : ℝ) - 1/2| ≤ radius x / 2 := by
  have := norm_le_pi_norm (fun j => (x j : ℝ) - 1/2) i
  simpa [Real.norm_eq_abs,radius] using this

lemma radius_eq_one_iff (x : N → I) : radius x = 1 ↔ x ∈ Cube.boundary N := by
  constructor
  · intro h
    by_contra hx
    have hi : ∀ i, (0 : ℝ) < x i ∧ (x i : ℝ) < 1 := by
      intro i
      have h0 : x i ≠ 0 := fun h0 => hx ⟨i,Or.inl h0⟩
      have h1 : x i ≠ 1 := fun h1 => hx ⟨i,Or.inr h1⟩
      exact ⟨lt_of_le_of_ne (x i).property.1 (fun he => h0 (Subtype.ext he.symm)),
        lt_of_le_of_ne (x i).property.2 (fun he => h1 (Subtype.ext he))⟩
    have hn : ‖fun i => (x i : ℝ) - 1/2‖ < (1/2 : ℝ) := by
      rw [pi_norm_lt_iff (by norm_num)]
      intro i
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> linarith [(hi i).1,(hi i).2]
    unfold radius at h
    linarith
  · rintro ⟨i,hi|hi⟩
    · have hc := coord_le_radius x i
      rw [hi] at hc
      norm_num at hc
      exact le_antisymm (radius_le_one x) (by linarith)
    · have hc := coord_le_radius x i
      rw [hi] at hc
      norm_num at hc
      exact le_antisymm (radius_le_one x) (by linarith)

def denominator (tx : I × (N → I)) : ℝ := max (1 - (tx.1 : ℝ) / 2) (radius tx.2)

lemma denominator_ge_half (tx : I × (N → I)) : (1/2 : ℝ) ≤ denominator tx := by
  have := le_max_left (1 - (tx.1 : ℝ) / 2) (radius tx.2)
  unfold denominator
  linarith [tx.1.property.2]

lemma denominator_pos (tx : I × (N → I)) : 0 < denominator tx :=
  (by norm_num : (0 : ℝ) < 1/2).trans_le (denominator_ge_half tx)

lemma denominator_le_one (tx : I × (N → I)) : denominator tx ≤ 1 := by
  apply max_le
  · linarith [tx.1.property.1]
  · exact radius_le_one tx.2

lemma denominator_continuous : Continuous (denominator (N := N)) := by
  unfold denominator
  exact (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (radius_continuous.comp continuous_snd)

def retractTime (tx : I × (N → I)) : I :=
  ⟨2 - (2 - (tx.1 : ℝ)) / denominator tx, by
    have hp := denominator_pos tx
    have hl := le_max_left (1 - (tx.1 : ℝ) / 2) (radius tx.2)
    have hu := denominator_le_one tx
    have hdiv0 : (2 - (tx.1 : ℝ)) / denominator tx ≤ 2 :=
      (div_le_iff₀ hp).mpr (by dsimp [denominator]; linarith)
    have hdiv1 : 1 ≤ (2 - (tx.1 : ℝ)) / denominator tx :=
      (le_div_iff₀ hp).mpr (by linarith [tx.1.property.2])
    constructor <;> linarith⟩

def retractCube (tx : I × (N → I)) : N → I := fun i =>
  ⟨1/2 + ((tx.2 i : ℝ) - 1/2) / denominator tx, by
    have hp := denominator_pos tx
    have hc := coord_le_radius tx.2 i
    have hd : radius tx.2 ≤ denominator tx := le_max_right _ _
    have hi := abs_le.mp hc
    have hdiv0 : -(1/2 : ℝ) ≤ ((tx.2 i : ℝ) - 1/2) / denominator tx :=
      (le_div_iff₀ hp).mpr (by linarith [hi.1])
    have hdiv1 : ((tx.2 i : ℝ) - 1/2) / denominator tx ≤ (1/2 : ℝ) :=
      (div_le_iff₀ hp).mpr (by linarith [hi.2])
    constructor <;> linarith⟩

lemma retractTime_continuous : Continuous (retractTime (N := N)) := by
  apply Continuous.subtype_mk
  exact continuous_const.sub ((continuous_const.sub
    (continuous_subtype_val.comp continuous_fst)).div denominator_continuous
    (fun tx => (denominator_pos tx).ne'))

lemma retractCube_continuous : Continuous (retractCube (N := N)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_snd)).sub continuous_const).div denominator_continuous
    (fun tx => (denominator_pos tx).ne'))

lemma radius_retractCube (tx : I × (N → I)) :
    radius (retractCube tx) = radius tx.2 / denominator tx := by
  have he : (fun i => (retractCube tx i : ℝ) - 1/2) =
      (denominator tx)⁻¹ • (fun i => (tx.2 i : ℝ) - 1/2) := by
    funext i
    dsimp [retractCube]
    ring
  rw [radius,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denominator_pos tx))]
  unfold radius
  ring

/-- The bottom of the prism together with all its vertical sides. -/
def bottomSides : Set (I × (N → I)) := {tx | tx.1 = 0 ∨ tx.2 ∈ Cube.boundary N}

lemma retraction_mem (tx : I × (N → I)) : (retractTime tx,retractCube tx) ∈ bottomSides := by
  by_cases h : radius tx.2 ≤ 1 - (tx.1 : ℝ) / 2
  · left
    apply Subtype.ext
    change 2 - (2 - (tx.1 : ℝ)) / denominator tx = 0
    have hd : denominator tx = 1 - (tx.1 : ℝ) / 2 := max_eq_left h
    have hn : denominator tx ≠ 0 := (denominator_pos tx).ne'
    field_simp
    rw [hd]
    ring
  · right
    apply (radius_eq_one_iff _).mp
    rw [radius_retractCube]
    have hd : denominator tx = radius tx.2 := max_eq_right (le_of_not_ge h)
    rw [←hd]
    exact div_self (denominator_pos tx).ne'

/-- Literal continuous retraction of the prism to bottom and sides. -/
def retraction : C(I × (N → I),bottomSides (N := N)) where
  toFun tx := ⟨(retractTime tx,retractCube tx),retraction_mem tx⟩
  continuous_toFun := (retractTime_continuous.prodMk retractCube_continuous).subtype_mk _

lemma denominator_eq_one {tx : I × (N → I)} (h : tx ∈ bottomSides) : denominator tx = 1 := by
  rcases h with h|h
  · unfold denominator
    rw [h]
    simpa using max_eq_left (radius_le_one tx.2)
  · unfold denominator
    rw [(radius_eq_one_iff _).mpr h]
    apply max_eq_right
    linarith [tx.1.property.1]

lemma retraction_fixed {tx : I × (N → I)} (h : tx ∈ bottomSides) : (retraction tx).val = tx := by
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (tx.1 : ℝ)) / denominator tx = (tx.1 : ℝ)
    rw [denominator_eq_one h]
    ring
  · funext i
    apply Subtype.ext
    change 1/2 + ((tx.2 i : ℝ) - 1/2) / denominator tx = (tx.2 i : ℝ)
    rw [denominator_eq_one h]
    ring

variable {X : Type*} [TopologicalSpace X]

lemma boundary_isClosed : IsClosed (Cube.boundary N) := by
  have he : Cube.boundary N = radius ⁻¹' ({1} : Set ℝ) := by
    ext x
    exact (radius_eq_one_iff x).symm
  rw [he]
  exact isClosed_singleton.preimage radius_continuous

/-- Glue the prescribed initial map and boundary homotopy on the closed
bottom-and-sides subspace. -/
def sideGlueRaw (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (tx : I × (N → I)) : X :=
  if hx : tx.2 ∈ Cube.boundary N then H (tx.1,⟨tx.2,hx⟩) else f tx.2

omit [Fintype N] in
lemma sideGlueRaw_bottom (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (x : N → I) :
    sideGlueRaw f H (0,x) = f x := by
  classical
  unfold sideGlueRaw
  split_ifs with hx
  · exact hH ⟨x,hx⟩
  · rfl

omit [Fintype N] in
lemma sideGlueRaw_side (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (t : I) (x : Cube.boundary N) : sideGlueRaw f H (t,x) = H (t,x) := by
  classical
  simp [sideGlueRaw,x.property]

lemma sideGlueRaw_continuousOn (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) :
    ContinuousOn (sideGlueRaw f H) (bottomSides (N := N)) := by
  classical
  have hb : ContinuousOn (sideGlueRaw f H) {tx | tx.1 = (0 : I)} := by
    apply (f.continuous.comp continuous_snd).continuousOn.congr
    intro tx htx
    rcases tx with ⟨t,x⟩
    change t = 0 at htx
    subst t
    exact sideGlueRaw_bottom f H hH x
  have hs : ContinuousOn (sideGlueRaw f H) {tx | tx.2 ∈ Cube.boundary N} := by
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {tx : I × (N → I) | tx.2 ∈ Cube.boundary N} → I × Cube.boundary N :=
      fun tx => (tx.val.1,⟨tx.val.2,tx.property⟩)
    have hg : Continuous g :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    apply (H.continuous.comp hg).congr
    intro tx
    exact (sideGlueRaw_side f H tx.val.1 ⟨tx.val.2,tx.property⟩).symm
  exact hb.union_of_isClosed hs
    (isClosed_singleton.preimage continuous_fst)
    (boundary_isClosed.preimage continuous_snd)

def sideGlue (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) : C(bottomSides (N := N),X) :=
  ⟨(bottomSides (N := N)).domRestrict (sideGlueRaw f H),
    continuousOn_iff_continuous_domRestrict.mp (sideGlueRaw_continuousOn f H hH)⟩

/-- Genuine cubical homotopy extension, constructed by the explicit prism
retraction. No extension or cellular-approximation premise is used. -/
def extend (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) : C(I × (N → I),X) :=
  (sideGlue f H hH).comp retraction

lemma extend_bottom (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (x : N → I) :
    extend f H hH (0,x) = f x := by
  change sideGlueRaw f H (retraction (0,x)).val = f x
  rw [retraction_fixed (Or.inl rfl)]
  exact sideGlueRaw_bottom f H hH x

lemma extend_side (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (t : I) (x : Cube.boundary N) :
    extend f H hH (t,x) = H (t,x) := by
  change sideGlueRaw f H (retraction (t,x)).val = H (t,x)
  rw [retraction_fixed (Or.inr x.property)]
  exact sideGlueRaw_side f H t x

end HyperbolicObstruction.CubicalHomotopyExtension
end
end

section

end

end OAI
