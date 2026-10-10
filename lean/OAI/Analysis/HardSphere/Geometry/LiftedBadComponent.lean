import Mathlib
import OAI.Analysis.HardSphere.Model
import OAI.Analysis.HardSphere.Geometry.RoundBox

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

def liftedBadComponent (B : Set Vertex) (z : Vertex) : Set Vertex :=
  {w | z ∈ B ∧ w ∈ B ∧ withinReach starStep B z w}

def FiniteBadComponents (B : Set Vertex) : Prop :=
  ∀ z ∈ B, (liftedBadComponent B z).Finite

lemma liftedBadComponent_self {B : Set Vertex} {z : Vertex} (hz : z ∈ B) :
    z ∈ liftedBadComponent B z := ⟨hz, hz, .refl⟩

lemma liftedBadComponent_subset (B : Set Vertex) (z : Vertex) : liftedBadComponent B z ⊆ B :=
  fun _ h ↦ h.2.1

lemma liftedBadComponent_closed {B : Set Vertex} {z c x : Vertex}
    (hc : c ∈ liftedBadComponent B z) (hx : x ∈ B) (hcx : starStep c x) :
    x ∈ liftedBadComponent B z :=
  ⟨hc.1, hx, hc.2.2.tail ⟨hc.2.1, hx, hcx⟩⟩

lemma liftedBadComponent_connected (B : Set Vertex) (z : Vertex) :
    starConnected (liftedBadComponent B z) := by
  intro c hc x hx
  have hcx := (withinReach_symm (fun _ _ ↦ starStep_symm) hc.2.2).trans hx.2.2
  exact withinReach_invariant (fun _ hu _ hv huv ↦ liftedBadComponent_closed hu hv huv) hc hcx

def IsBadComponent (B : Set Vertex) (C : Finset Vertex) : Prop :=
  ∃ z ∈ B, (↑C : Set Vertex) = liftedBadComponent B z

lemma IsBadComponent.connected {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) : starConnected (↑C) := by
  obtain ⟨z, _, hz⟩ := hC
  rw [hz]
  exact liftedBadComponent_connected B z

lemma IsBadComponent.subset {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) : (↑C : Set Vertex) ⊆ B := by
  obtain ⟨z, _, hz⟩ := hC
  rw [hz]
  exact liftedBadComponent_subset B z

lemma IsBadComponent.closed {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) {c x : Vertex}
    (hc : c ∈ C) (hx : x ∈ B) (hcx : starStep c x) : x ∈ C := by
  obtain ⟨z, _, hz⟩ := hC
  change x ∈ (↑C : Set Vertex)
  rw [hz]
  exact liftedBadComponent_closed (by simpa only [← hz, Finset.mem_coe] using hc) hx hcx

lemma intervalBox_finite (x y : Vertex) : (intervalBox x y).Finite := by
  have he : intervalBox x y = Set.Icc (x ⊓ y) (x ⊔ y) := by
    ext z
    simp only [intervalBox, Set.mem_ofPred, Set.mem_Icc, Pi.le_def,
      Pi.inf_apply, Pi.sup_apply]
    exact forall_and
  rw [he]
  exact Set.finite_Icc _ _

theorem exterior_all_liftedBadComponents_reach (B : Set Vertex)
    (hfin : FiniteBadComponents B) {v w : Vertex}
    (hv : ∀ C, IsBadComponent B C → v ∈ exterior C)
    (hw : ∀ C, IsBadComponent B C → w ∈ exterior C) :
    withinReach nearestStep Bᶜ v w := by
  classical
  let Γ := intervalBox v w
  let f : {z : Vertex // z ∈ B} → Finset Vertex := fun z ↦ (hfin z z.2).toFinset
  let roots : Finset {z : Vertex // z ∈ B} :=
    ((intervalBox_finite v w).inter_of_left B).toFinset.attach.image
      (fun z ↦ ⟨z.1, (Set.Finite.mem_toFinset _).mp z.2 |>.2⟩)
  let Cs := roots.image f
  have hf (z : {z : Vertex // z ∈ B}) : IsBadComponent B (f z) :=
    ⟨z, z.2, (hfin z z.2).coe_toFinset⟩
  have hCs : ∀ C ∈ Cs, IsBadComponent B C := by
    intro C hC
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hC
    exact hf z
  have hcover : ∀ z ∈ Γ, z ∈ B → ∃ C ∈ Cs, z ∈ C := by
    intro z hzΓ hzB
    have hz : z ∈ ((intervalBox_finite v w).inter_of_left B).toFinset := by
      exact ((intervalBox_finite v w).inter_of_left B).mem_toFinset.mpr ⟨hzΓ, hzB⟩
    have hzroot : (⟨z, hzB⟩ : {z : Vertex // z ∈ B}) ∈ roots := by
      apply Finset.mem_image.mpr
      exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨f ⟨z, hzB⟩, Finset.mem_image.mpr ⟨⟨z, hzB⟩, hzroot, rfl⟩, ?_⟩
    exact (hfin z hzB).mem_toFinset.mpr (liftedBadComponent_self hzB)
  have hvΓ : v ∈ Γ := by intro i; exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hwΓ : w ∈ Γ := by intro i; exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hd := good_detour_reach Γ B Cs
    (fun _ h ↦ (hCs _ h).connected) (fun _ h ↦ (hCs _ h).subset)
    (fun _ h _ hc _ hx hcx ↦ (hCs _ h).closed hc hx hcx) hcover hvΓ hwΓ
    (fun _ h ↦ hv _ (hCs _ h)) (fun _ h ↦ hw _ (hCs _ h)) (intervalBox_reach v w)
  exact withinReach_mono (fun _ h ↦ h.2) hd

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

abbrev Point := Fin 3 → ℝ

def liftPoint (L : Length) (x : Point) : Torus L := fun j ↦ (x j : AddCircle L.val)

def liftedCube (h : ℝ) (z : Vertex) : Set Point :=
  Set.Icc (fun j ↦ h * (z j : ℝ) - 1/2) (fun j ↦ h * ((z j : ℝ) + 1) - 1/2)

def microCube (L : Length) (h : ℝ) (z : Vertex) : Set (Torus L) :=
  liftPoint L '' liftedCube h z

def forbidden {n : ℕ} {L : Length} (r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | ∃ j, torusDistance L x (Y j) ≤ r}

def slice {n : ℕ} {L : Length} (r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  (forbidden r Y)ᶜ

def bad {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set Vertex :=
  {z | ∃ x ∈ microCube L h z, x ∈ forbidden r Y}

def exceptional {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Prop :=
  Y ∉ allowed n L r ∨ ¬ FiniteBadComponents (bad h r Y)

def omitted {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | exceptional h r Y ∨
    ∃ C : Finset Vertex, IsBadComponent (bad h r Y) C ∧
      ∃ z ∈ fill C, x ∈ microCube L h z}

def retained {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  (omitted h r Y)ᶜ

lemma continuous_liftPoint (L : Length) : Continuous (liftPoint L) := by
  exact continuous_pi fun j ↦ continuous_quotient_mk'.comp (continuous_apply j)

lemma isCompact_microCube (L : Length) (h : ℝ) (z : Vertex) :
    IsCompact (microCube L h z) :=
  isCompact_Icc.image (continuous_liftPoint L)

lemma microCube_pathConnected (L : Length) {h : ℝ} (hh : 0 ≤ h) (z : Vertex) :
    IsPathConnected (microCube L h z) := by
  apply ((convex_Icc (𝕜 := ℝ) _ _).isPathConnected ?_).image (continuous_liftPoint L)
  refine ⟨fun j ↦ h * (z j : ℝ) - 1/2, le_rfl, ?_⟩
  intro j
  dsimp
  nlinarith

lemma goodCube_subset_slice {n : ℕ} {L : Length} {h r : ℝ} {Y : Configuration n L}
    {z : Vertex} (hz : z ∉ bad h r Y) : microCube L h z ⊆ slice r Y := by
  intro x hx hxf
  exact hz ⟨x, hx, hxf⟩

lemma retained_finiteComponents {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} {x : Torus L} (hx : x ∈ retained h r Y) :
    FiniteBadComponents (bad h r Y) := by
  by_contra hn
  exact hx (Or.inl (Or.inr hn))

lemma retained_mem_exterior {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} {x : Torus L} (hx : x ∈ retained h r Y)
    {z : Vertex} (hxz : x ∈ microCube L h z) (C : Finset Vertex)
    (hC : IsBadComponent (bad h r Y) C) : z ∈ exterior C := by
  by_contra hn
  exact hx (Or.inr ⟨C, hC, z, hn, hxz⟩)

end HardSphere.BathSlice

end

end OAI
