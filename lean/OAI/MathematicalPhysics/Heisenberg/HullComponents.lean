import OAI.MathematicalPhysics.Heisenberg.LatticeHulls

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.LatticeCut
open Heisenberg.Geometry
open Heisenberg.LatticePotential (shift)

def Boundary {d : ℕ} (H : Set (Site d)) : Set (Site d) :=
  {v | v ∉ H ∧ ∃ u ∈ H, Step u v}

def outer {d : ℕ} (H : Set (Site d)) (e : Edge d) : Site d :=
  if e.1 ∈ H then shift e.1 e.2 else e.1

lemma step_to_shift {d : ℕ} (x : Site d) (i : Fin d) : Step x (shift x i) := by
  refine ⟨i,Or.inl ?_,?_⟩
  · simp [shift]
  · intro k hk; simp [shift,hk]

lemma cut_mem_iff {d : ℕ} (H : Set (Site d)) (e : Edge d) :
    Cut H e ↔ (e.1 ∈ H ∧ shift e.1 e.2 ∉ H) ∨ (e.1 ∉ H ∧ shift e.1 e.2 ∈ H) := by
  by_cases h : e.1 ∈ H <;> by_cases h' : shift e.1 e.2 ∈ H <;> simp [Cut,color,h,h']

lemma outer_boundary {d : ℕ} (H : Set (Site d)) (e : Edge d) (he : Cut H e) :
    outer H e ∈ Boundary H := by
  rcases (cut_mem_iff H e).mp he with ⟨h,h'⟩ | ⟨h,h'⟩
  · rw [outer,ite_eq_left h]
    exact ⟨h',e.1,h,step_to_shift e.1 e.2⟩
  · rw [outer,ite_eq_right h]
    exact ⟨h,shift e.1 e.2,h',step_symm (step_to_shift e.1 e.2)⟩

lemma boundary_has_cut {d : ℕ} (H : Set (Site d)) (v : Site d) (hv : v ∈ Boundary H) :
    ∃ e, Cut H e ∧ outer H e = v := by
  obtain ⟨hv,u,hu,huv⟩ := hv
  rcases step_shift huv with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(u,i),(cut_mem_iff ..).mpr (Or.inl ⟨hu,hv⟩),by simp [outer,hu]⟩
  · exact ⟨(v,i),(cut_mem_iff ..).mpr (Or.inr ⟨hv,hu⟩),by simp [outer,hv]⟩

lemma square_outer_bounds {d : ℕ} (H : Set (Site d)) {x : Site d} {i j : Fin d}
    (hij : i ≠ j) {e : Edge d} (he : e ∈ square x i j) (k : Fin d) :
    x k ≤ outer H e k ∧ outer H e k ≤ x k+1 := by
  simp only [square,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    unfold outer
    split_ifs
    all_goals
      by_cases hki : k = i
      · subst k; simp [shift,hij,Ne.symm hij]
      · by_cases hkj : k = j
        · subst k; simp [shift,hij,Ne.symm hij]
        · simp [shift,hki,hkj]

lemma linked_outer_near {d : ℕ} (H : Set (Site d)) {e f : Edge d}
    (h : Linked H e f) : outer H f ∈ Ball 1 (outer H e) := by
  obtain ⟨_,_,x,i,j,hij,he,hf⟩ := h
  intro k
  have he' := square_outer_bounds H hij he k
  have hf' := square_outer_bounds H hij hf k
  rw [abs_le]
  omega

theorem boundary_connected {d : ℕ} (H : Set (Site d)) (hH : Connected H) (hU : Connected Hᶜ)
    (x y : Site d) (hx : x ∈ Boundary H) (hy : y ∈ Boundary H) :
    Relation.ReflTransGen (fun a b => b ∈ Ball 1 a ∧ a ∈ Boundary H ∧ b ∈ Boundary H) x y := by
  obtain ⟨e,he,rfl⟩ := boundary_has_cut H x hx
  obtain ⟨f,hf,rfl⟩ := boundary_has_cut H y hy
  have hr := cut_connected H hH hU e f he hf
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail g f hrg hgf ih =>
    exact (ih hgf.1 (outer_boundary H g hgf.1)).tail
      ⟨linked_outer_near H hgf,outer_boundary H g hgf.1,outer_boundary H f hgf.2.1⟩

end Heisenberg.LatticeCut

namespace Heisenberg.Geometry

lemma ball_symm {d : ℕ} {r : ℤ} {x y : Site d} (h : y ∈ Ball r x) : x ∈ Ball r y := by
  intro j
  simpa only [abs_sub_comm] using h j

lemma ball_triangle {d : ℕ} {r s : ℤ} {x y z : Site d}
    (hxy : y ∈ Ball r x) (hyz : z ∈ Ball s y) : z ∈ Ball (r+s) x := by
  intro j
  have h : z j-x j = (z j-y j)+(y j-x j) := by omega
  rw [h]
  exact (abs_add_le ..).trans (by have := hxy j; have := hyz j; omega)

lemma ball_mono {d : ℕ} {r s : ℤ} (h : r ≤ s) (x : Site d) : Ball r x ⊆ Ball s x :=
  fun _ hz j => (hz j).trans h

lemma ball_self {d : ℕ} {r : ℤ} (hr : 0 ≤ r) (x : Site d) : x ∈ Ball r x := by
  intro j; simpa using hr

lemma ball_connected {d : ℕ} (r : ℤ) (x : Site d) : Heisenberg.LatticeCut.Connected (Ball r x) := by
  intro y hy z hz
  apply reach_rectangle
  intro w hw j
  have hyj := abs_le.mp (hy j)
  have hzj := abs_le.mp (hz j)
  have hwj := hw j
  rw [abs_le]
  constructor <;> omega

lemma step_ball_one {d : ℕ} {x y : Site d} (h : Step x y) : y ∈ Ball 1 x := by
  obtain ⟨j,hj,hother⟩ := h
  intro k
  by_cases hk : k = j
  · subst k; rw [abs_le]; rcases hj with hj | hj <;> omega
  · rw [hother k hk,sub_self,abs_zero]; omega

lemma interpolate_near {d : ℕ} {U : Set (Site d)} {x y : Site d}
    (hxy : y ∈ Ball 1 x) (hU : Ball 1 x ⊆ U) : Reach U x y :=
  reach_mono hU (ball_connected 1 x x (ball_self (by omega) x) y hxy)

end Heisenberg.Geometry

namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry

def Component {d : ℕ} (Z : Set (Site d)) (x : Site d) : Set (Site d) :=
  {y | y ∈ Z ∧ Relation.ReflTransGen (fun a b => b ∈ Ball 8 a ∧ a ∈ Z ∧ b ∈ Z) x y}

def Thick {d : ℕ} (r : ℤ) (C : Set (Site d)) : Set (Site d) :=
  {z | ∃ x ∈ C, z ∈ Ball r x}

lemma thick_mono {d : ℕ} {r s : ℤ} (hrs : r ≤ s) (C : Set (Site d)) : Thick r C ⊆ Thick s C := by
  intro x hx
  obtain ⟨y,hy,hxy⟩ := hx
  exact ⟨y,hy,ball_mono hrs y hxy⟩

lemma self_mem_component {d : ℕ} (Z : Set (Site d)) {x : Site d} (hx : x ∈ Z) : x ∈ Component Z x :=
  ⟨hx,Relation.ReflTransGen.refl⟩

lemma component_closed {d : ℕ} (Z : Set (Site d)) (x : Site d) {y z : Site d}
    (hy : y ∈ Component Z x) (hz : z ∈ Z) (hyz : z ∈ Ball 8 y) : z ∈ Component Z x :=
  ⟨hz,hy.2.tail ⟨hyz,hy.1,hz⟩⟩

lemma component_symmetric {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Component Z x) : x ∈ Component Z y := by
  refine ⟨hx,?_⟩
  have hr := hy.2
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail z w _ hzw ih =>
    exact (Relation.ReflTransGen.single ⟨ball_symm hzw.1,hzw.2.2,hzw.2.1⟩).trans (ih ⟨hzw.2.1,by assumption⟩)

lemma component_eq_of_mem {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Component Z x) : Component Z y = Component Z x := by
  have hyx := component_symmetric Z hx hy
  ext z
  exact ⟨fun hz => ⟨hz.1,hy.2.trans hz.2⟩,fun hz => ⟨hz.1,hyx.2.trans hz.2⟩⟩

lemma components_disjoint {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Z) (hne : Component Z x ≠ Component Z y) :
    Disjoint (Component Z x) (Component Z y) := by
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  exact hne ((component_eq_of_mem Z hx hzx).symm.trans (component_eq_of_mem Z hy hzy))

lemma thickenings_disjoint {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Z) (hne : Component Z x ≠ Component Z y) :
    Disjoint (Thick 4 (Component Z x)) (Thick 4 (Component Z y)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,hu,hzu⟩ ⟨v,hv,hzv⟩
  have huv : v ∈ Ball 8 u := by
    simpa using ball_triangle hzu (ball_symm hzv)
  have hvx := component_closed Z x hu hv.1 huv
  exact Set.disjoint_left.mp (components_disjoint Z hx hy hne) hvx hv

lemma overlapping_balls {d : ℕ} {x y : Site d} (hxy : y ∈ Ball 8 x) :
    ∃ z, z ∈ Ball 4 x ∧ z ∈ Ball 4 y := by
  refine ⟨fun j => max (x j-4) (y j-4),?_,?_⟩
  all_goals
    intro j
    have h := abs_le.mp (hxy j)
    dsimp only
    rw [abs_le]
    constructor <;> omega

lemma thick_component_connected {d : ℕ} (Z : Set (Site d)) {x : Site d} (_hx : x ∈ Z) :
    Heisenberg.LatticeCut.Connected (Thick 4 (Component Z x)) := by
  let A := Thick 4 (Component Z x)
  have hball : ∀ y ∈ Component Z x, Ball 4 y ⊆ A := fun y hy z hz => ⟨y,hy,hz⟩
  have hbase : ∀ y ∈ Component Z x, Reach A x y := by
    intro y hy
    have hr := hy.2
    induction hr with
    | refl => exact reach_refl _ _
    | @tail v w hvw hstep ih =>
      have hv : v ∈ Component Z x := ⟨hstep.2.1,hvw⟩
      have hw : w ∈ Component Z x := ⟨hstep.2.2,hvw.tail hstep⟩
      obtain ⟨z,hzv,hzw⟩ := overlapping_balls hstep.1
      exact (ih hv).trans ((reach_mono (hball v hv)
        (ball_connected 4 v v (ball_self (by omega) v) z hzv)).trans
        (reach_mono (hball w hw) (ball_connected 4 w z hzw w (ball_self (by omega) w))))
  have hAll : ∀ y ∈ A, Reach A x y := by
    rintro y ⟨z,hz,hyz⟩
    exact (hbase z hz).trans (reach_mono (hball z hz)
      (ball_connected 4 z z (ball_self (by omega) z) y hyz))
  intro y hy z hz
  exact (reach_symm (hAll y hy)).trans (hAll z hz)

lemma boundary_unit_clear {d : ℕ} (Z : Set (Site d)) {x b v : Site d}
    (hb : b ∉ Thick 4 (Component Z x))
    (hv : v ∈ Heisenberg.LatticeCut.Boundary (Heisenberg.LatticeHull.Hull (Thick 4 (Component Z x)) b)) :
    Ball 1 v ⊆ Zᶜ := by
  obtain ⟨hv,u,hu,huv⟩ := hv
  have huA := Heisenberg.LatticeHull.inner_endpoint_mem _ hb hu hv huv
  obtain ⟨c,hc,huc⟩ := huA
  have hvc : v ∈ Ball 5 c := by simpa using ball_triangle huc (step_ball_one huv)
  intro z hz hzZ
  have hzc : z ∈ Ball 8 c := ball_mono (by omega : (6:ℤ) ≤ 8) c (ball_triangle hvc hz)
  have hzC := component_closed Z x hc hzZ hzc
  have hvA : v ∈ Thick 4 (Component Z x) := ⟨z,hzC,ball_mono (by omega : (1:ℤ) ≤ 4) z (ball_symm hz)⟩
  exact hv (Heisenberg.LatticeHull.subset_hull _ hb hvA)

theorem surviving_boundary_connected {d : ℕ} (Z : Set (Site d)) {x b : Site d}
    (hx : x ∈ Z) (hb : b ∉ Thick 4 (Component Z x))
    (u v : Site d)
    (hu : u ∈ Heisenberg.LatticeCut.Boundary (Heisenberg.LatticeHull.Hull (Thick 4 (Component Z x)) b))
    (hv : v ∈ Heisenberg.LatticeCut.Boundary (Heisenberg.LatticeHull.Hull (Thick 4 (Component Z x)) b)) :
    Reach Zᶜ u v := by
  have hAn : (Thick 4 (Component Z x)).Nonempty :=
    ⟨x,x,self_mem_component Z hx,ball_self (by omega) x⟩
  have hr := Heisenberg.LatticeCut.boundary_connected _
    (Heisenberg.LatticeHull.hull_connected _ (thick_component_connected Z hx) hAn hb)
    (Heisenberg.LatticeHull.complement_connected _ b) u v hu hv
  induction hr with
  | refl => exact reach_refl _ _
  | @tail w z _ hwz ih =>
    exact (ih hwz.2.1).trans (interpolate_near hwz.1 (boundary_unit_clear Z hb hwz.2.1))

end Heisenberg.LatticeComponents

namespace Heisenberg.Geometry

lemma exterior_ball_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (c x y : Site d) (hx : x ∉ Ball r c) (hy : y ∉ Ball r c) :
    Reach (Ball r c)ᶜ x y := by
  have hx' : x-c ∉ Box r := hx
  have hy' : y-c ∉ Box r := hy
  have hxy := exterior_connected hd r hr (x-c) (y-c) hx' hy'
  have h := reach_translate c (Box r)ᶜ (Ball r c)ᶜ (fun z hz hzc =>
    hz ((translate_mem_ball c z r).mp hzc)) hxy
  simpa only [add_sub_cancel] using h

lemma ball_finite {d : ℕ} (r : ℕ) (x : Site d) : (Ball (r : ℤ) x).Finite := by
  have he : Ball (r : ℤ) x = (ballFinset d r x : Set (Site d)) := by
    ext z; exact (mem_ballFinset ..).symm
  rw [he]
  exact Finset.finite_toSet _

lemma ball_enlarge_step {d : ℕ} {c u v : Site d} {r : ℤ}
    (hu : u ∈ Ball r c) (huv : Step u v) : v ∈ Ball (r+1) c :=
  ball_triangle hu (step_ball_one huv)

lemma interpolate_near_confined {d : ℕ} {U : Set (Site d)} {c x y : Site d} {r : ℤ}
    (hx : x ∈ Ball r c) (hy : y ∈ Ball r c)
    (hxy : y ∈ Ball 1 x) (hU : Ball 1 x ⊆ U) : Reach (Ball r c ∩ U) x y := by
  apply reach_rectangle
  intro z hz
  constructor
  · intro j
    have hxj := abs_le.mp (hx j)
    have hyj := abs_le.mp (hy j)
    have hzj := hz j
    rw [abs_le]
    constructor <;> omega
  · apply hU
    intro j
    have hyj := abs_le.mp (hxy j)
    have hzj := hz j
    rw [abs_le]
    constructor <;> omega

end Heisenberg.Geometry
end

end OAI
