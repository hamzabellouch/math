import OAI.MathematicalPhysics.Heisenberg.HullComponents

namespace OAI

noncomputable section
open scoped Classical
namespace Heisenberg.LatticeHull
open Heisenberg.Geometry

lemma hull_subset_ball {d : ℕ} (hd : 2 ≤ d) (A : Set (Site d)) (c : Site d) (r : ℤ) (hr : 0 ≤ r)
    (hAr : A ⊆ Ball r c) {b : Site d} (hb : b ∉ Ball r c) : Hull A b ⊆ Ball r c := by
  intro x hx
  by_contra hxr
  apply hx
  apply reach_mono _ (exterior_ball_connected hd r hr c b x hb hxr)
  intro z hz hzA
  exact hz (hAr hzA)

lemma boundary_subset_ball {d : ℕ} (H : Set (Site d)) (c : Site d) (r : ℤ)
    (hH : H ⊆ Ball r c) : Heisenberg.LatticeCut.Boundary H ⊆ Ball (r+1) c := by
  rintro v ⟨_,u,hu,huv⟩
  exact ball_enlarge_step (hH hu) huv

lemma boundary_nonempty {d : ℕ} (H : Set (Site d)) {x y : Site d} (hx : x ∈ H) (hy : y ∉ H) :
    (Heisenberg.LatticeCut.Boundary H).Nonempty := by
  have hr := ambient_connected x y
  have h : y ∈ H ∨ (Heisenberg.LatticeCut.Boundary H).Nonempty := by
    clear hy
    induction hr with
    | refl => exact Or.inl hx
    | @tail u v _ huv ih =>
      rcases ih with hu | hu
      · by_cases hv : v ∈ H
        · exact Or.inl hv
        · exact Or.inr ⟨v,hv,u,hu,huv.1⟩
      · exact Or.inr hu
  exact h.resolve_left hy

end Heisenberg.LatticeHull
namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry Heisenberg.LatticeHull

lemma thick_finite {d : ℕ} (r : ℕ) (C : Set (Site d)) (hC : C.Finite) : (Thick (r : ℤ) C).Finite := by
  have he : Thick (r : ℤ) C = ⋃ x ∈ C, Ball (r : ℤ) x := by
    ext z; simp [Thick]
  rw [he]
  exact hC.biUnion (fun x _ => ball_finite r x)

lemma component_finite {d : ℕ} (Z : Set (Site d)) (hZ : Z.Finite) (x : Site d) :
    (Component Z x).Finite := hZ.subset (fun _ h => h.1)

lemma thick_nonempty {d : ℕ} (Z : Set (Site d)) {x : Site d} (hx : x ∈ Z) :
    (Thick 4 (Component Z x)).Nonempty := ⟨x,x,self_mem_component Z hx,ball_self (by omega) x⟩

lemma hull_cut_clearance {d : ℕ} (Z : Set (Site d)) {x b u v : Site d}
    (hb : b ∉ Thick 4 (Component Z x))
    (hu : u ∈ Hull (Thick 4 (Component Z x)) b)
    (hv : v ∉ Hull (Thick 4 (Component Z x)) b) (huv : Step u v) :
    (u ∈ Thick 4 (Component Z x) ∧ u ∉ Thick 3 (Component Z x)) ∧
    (v ∈ Thick 5 (Component Z x) ∧ v ∉ Thick 4 (Component Z x)) ∧ u ∉ Z ∧ v ∉ Z := by
  have huA := inner_endpoint_mem _ hb hu hv huv
  have hvA : v ∉ Thick 4 (Component Z x) := fun h => hv (subset_hull _ hb h)
  have hv5 : v ∈ Thick 5 (Component Z x) := by
    obtain ⟨c,hc,huc⟩ := huA
    exact ⟨c,hc,ball_triangle huc (step_ball_one huv)⟩
  have hu3 : u ∉ Thick 3 (Component Z x) := by
    rintro ⟨c,hc,huc⟩
    exact hvA ⟨c,hc,ball_triangle huc (step_ball_one huv)⟩
  have huZ : u ∉ Z := by
    intro huZ
    obtain ⟨c,hc,huc⟩ := huA
    have huC := component_closed Z x hc huZ (ball_mono (by omega : (4:ℤ) ≤ 8) c huc)
    exact hu3 ⟨u,huC,ball_self (by omega) u⟩
  have hvZ : v ∉ Z := boundary_unit_clear Z hb ⟨hv,u,hu,huv⟩ (ball_self (by omega) v)
  exact ⟨⟨huA,hu3⟩,⟨hv5,hvA⟩,huZ,hvZ⟩

theorem surviving_boundary_confined {d : ℕ} (Z : Set (Site d)) {x b c : Site d}
    (hx : x ∈ Z) (hb : b ∉ Thick 4 (Component Z x)) (r : ℤ)
    (hH : Hull (Thick 4 (Component Z x)) b ⊆ Ball r c)
    (u v : Site d)
    (hu : u ∈ Heisenberg.LatticeCut.Boundary (Hull (Thick 4 (Component Z x)) b))
    (hv : v ∈ Heisenberg.LatticeCut.Boundary (Hull (Thick 4 (Component Z x)) b)) :
    Reach (Ball (r+1) c ∩ Zᶜ) u v := by
  have hB := boundary_subset_ball _ c r hH
  have hr := Heisenberg.LatticeCut.boundary_connected _
    (hull_connected _ (thick_component_connected Z hx) (thick_nonempty Z hx) hb)
    (complement_connected _ b) u v hu hv
  induction hr with
  | refl => exact reach_refl _ _
  | @tail w z _ hwz ih =>
    exact (ih hwz.2.1).trans (interpolate_near_confined (hB hwz.2.1) (hB hwz.2.2)
      hwz.1 (boundary_unit_clear Z hb hwz.2.1))

end Heisenberg.LatticeComponents

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents

variable {d : ℕ}

def DisjointFamily (F : Finset (Set (Site d))) : Prop :=
  ∀ H ∈ F, ∀ K ∈ F, H ≠ K → Disjoint H K

lemma member_unique {F : Finset (Set (Site d))} (hF : DisjointFamily F)
    {H K : Set (Site d)} (hH : H ∈ F) (hK : K ∈ F) {x : Site d}
    (hxH : x ∈ H) (hxK : x ∈ K) : H = K := by
  by_contra hne
  exact Set.disjoint_left.mp (hF H hH K hK hne) hxH hxK

def collapse (F : Finset (Set (Site d))) (rep : Set (Site d) → Site d) (x : Site d) : Site d :=
  if h : ∃ H ∈ F, x ∈ H then rep h.choose else x

lemma collapse_of_mem {F : Finset (Set (Site d))} (hF : DisjointFamily F)
    (rep : Set (Site d) → Site d) {H : Set (Site d)} (hH : H ∈ F) {x : Site d} (hx : x ∈ H) :
    collapse F rep x = rep H := by
  have h : ∃ K ∈ F, x ∈ K := ⟨H,hH,hx⟩
  rw [collapse,dite_eq_left h]
  rw [member_unique hF h.choose_spec.1 hH h.choose_spec.2 hx]

lemma collapse_free {F : Finset (Set (Site d))} (rep : Set (Site d) → Site d) {x : Site d}
    (hx : ¬ ∃ H ∈ F, x ∈ H) : collapse F rep x = x := by rw [collapse,dite_eq_right hx]

lemma collapse_survives (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (rep : Set (Site d) → Site d) (hcover : ∀ x ∈ Z, ∃ H ∈ F, x ∈ H)
    (hrep : ∀ H ∈ F, rep H ∉ Z) (x : Site d) : collapse F rep x ∉ Z := by
  unfold collapse
  split_ifs with h
  · exact hrep h.choose h.choose_spec.1
  · exact fun hx => h (hcover x hx)

def RouteRegion (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (E : Set (Site d) → Set (Site d)) (u v : Site d) : Set (Site d) :=
  {z | (z = u ∨ z = v ∨ ∃ H ∈ F, (u ∈ H ∨ v ∈ H) ∧ z ∈ E H) ∧ z ∉ Z}

lemma region_boundary (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (E : Set (Site d) → Set (Site d)) (u v : Site d)
    {H : Set (Site d)} (hH : H ∈ F) (hc : u ∈ H ∨ v ∈ H) :
    E H ∩ Zᶜ ⊆ RouteRegion Z F E u v := by
  exact fun z hz => ⟨Or.inr (Or.inr ⟨H,hH,hc,hz.1⟩),hz.2⟩

theorem route_exists (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (hF : DisjointFamily F) (rep : Set (Site d) → Site d)
    (E : Set (Site d) → Set (Site d))
    (hcover : ∀ x ∈ Z, ∃ H ∈ F, x ∈ H)
    (hroute : ∀ H ∈ F, ∀ v ∈ Boundary H, Reach (E H ∩ Zᶜ) (rep H) v)
    (hclear : ∀ H ∈ F, Boundary H ⊆ Zᶜ)
    {u v : Site d} (huv : Step u v) :
    Reach (RouteRegion Z F E u v) (collapse F rep u) (collapse F rep v) := by
  by_cases hu : ∃ H ∈ F, u ∈ H
  · obtain ⟨H,hH,huH⟩ := hu
    rw [collapse_of_mem hF rep hH huH]
    by_cases hv : ∃ K ∈ F, v ∈ K
    · obtain ⟨K,hK,hvK⟩ := hv
      rw [collapse_of_mem hF rep hK hvK]
      by_cases hHK : H = K
      · subst K; exact reach_refl _ _
      have hvH : v ∉ H := fun hvH => hHK (member_unique hF hH hK hvH hvK)
      have huK : u ∉ K := fun huK => hHK (member_unique hF hH hK huH huK)
      have hvB : v ∈ Boundary H := ⟨hvH,u,huH,huv⟩
      have huB : u ∈ Boundary K := ⟨huK,v,hvK,step_symm huv⟩
      have hru := reach_mono (region_boundary Z F E u v hH (Or.inl huH)) (hroute H hH v hvB)
      have hrv := reach_symm (reach_mono (region_boundary Z F E u v hK (Or.inr hvK))
        (hroute K hK u huB))
      exact hru.trans ((Relation.ReflTransGen.single ⟨step_symm huv,
        ⟨Or.inr (Or.inl rfl),hclear H hH hvB⟩,⟨Or.inl rfl,hclear K hK huB⟩⟩).trans hrv)
    · rw [collapse_free rep hv]
      have hvH : v ∉ H := fun hvH => hv ⟨H,hH,hvH⟩
      exact reach_mono (region_boundary Z F E u v hH (Or.inl huH))
        (hroute H hH v ⟨hvH,u,huH,huv⟩)
  · rw [collapse_free rep hu]
    by_cases hv : ∃ K ∈ F, v ∈ K
    · obtain ⟨K,hK,hvK⟩ := hv
      rw [collapse_of_mem hF rep hK hvK]
      have huK : u ∉ K := fun huK => hu ⟨K,hK,huK⟩
      exact reach_symm (reach_mono (region_boundary Z F E u v hK (Or.inr hvK))
        (hroute K hK u ⟨huK,v,hvK,step_symm huv⟩))
    · rw [collapse_free rep hv]
      exact Relation.ReflTransGen.single ⟨huv,
        ⟨Or.inl rfl,fun huZ => hu (hcover u huZ)⟩,
        ⟨Or.inr (Or.inl rfl),fun hvZ => hv (hcover v hvZ)⟩⟩

def allHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) : Finset (Set (Site d)) :=
  hZ.toFinset.image (fun x => Hull (Thick 4 (Component Z x)) b)

def maxHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) : Finset (Set (Site d)) :=
  (allHulls Z hZ b).filter (fun H => Maximal (· ∈ allHulls Z hZ b) H)

lemma mem_allHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) (H : Set (Site d)) :
    H ∈ allHulls Z hZ b ↔ ∃ x ∈ Z, Hull (Thick 4 (Component Z x)) b = H := by
  simp [allHulls]

lemma mem_maxHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) (H : Set (Site d)) :
    H ∈ maxHulls Z hZ b ↔ Maximal (· ∈ allHulls Z hZ b) H := by
  simp only [maxHulls,Finset.mem_filter]
  exact ⟨And.right,fun h => ⟨h.prop,h⟩⟩

lemma allHulls_laminar (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) {H K : Set (Site d)}
    (hH : H ∈ allHulls Z hZ b) (hK : K ∈ allHulls Z hZ b) :
    H ⊆ K ∨ K ⊆ H ∨ Disjoint H K := by
  obtain ⟨x,hx,rfl⟩ := (mem_allHulls Z hZ b H).mp hH
  obtain ⟨y,hy,rfl⟩ := (mem_allHulls Z hZ b K).mp hK
  by_cases he : Component Z x = Component Z y
  · exact Or.inl (by rw [he])
  have hbC : ∀ a, b ∉ Thick 4 (Component Z a) := by
    rintro a ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  exact hull_laminar _ _ (thick_component_connected Z hx) (thick_component_connected Z hy)
    (thick_nonempty Z hx) (thick_nonempty Z hy) (thickenings_disjoint Z hx hy he) (hbC x) (hbC y)

lemma maxHulls_disjoint (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) : DisjointFamily (maxHulls Z hZ b) := by
  intro H hH K hK hne
  have hHm := (mem_maxHulls Z hZ b H).mp hH
  have hKm := (mem_maxHulls Z hZ b K).mp hK
  rcases allHulls_laminar Z hZ b hb hHm.prop hKm.prop with h | h | h
  · exact (hne (Set.Subset.antisymm h (hHm.le_of_ge hKm.prop h))).elim
  · exact (hne (Set.Subset.antisymm (hKm.le_of_ge hHm.prop h) h)).elim
  · exact h

lemma maxHulls_cover (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) (x : Site d) (hx : x ∈ Z) : ∃ H ∈ maxHulls Z hZ b, x ∈ H := by
  let H := Hull (Thick 4 (Component Z x)) b
  have hH : H ∈ allHulls Z hZ b := (mem_allHulls ..).mpr ⟨x,hx,rfl⟩
  obtain ⟨K,hHK,hK⟩ := (allHulls Z hZ b).exists_le_maximal hH
  refine ⟨K,(mem_maxHulls ..).mpr hK,hHK ?_⟩
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  exact subset_hull _ hbC ⟨x,self_mem_component Z hx,ball_self (by omega) x⟩

lemma allHulls_boundary_nonempty (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) {H : Set (Site d)} (hH : H ∈ allHulls Z hZ b) :
    (Boundary H).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := (mem_allHulls ..).mp hH
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  apply boundary_nonempty _ (subset_hull _ hbC ⟨x,self_mem_component Z hx,ball_self (by omega) x⟩)
  exact fun h => h (reach_refl _ _)

theorem finite_hull_routing (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) :
    ∃ rep : Set (Site d) → Site d,
      (∀ H ∈ maxHulls Z hZ b, rep H ∈ Boundary H) ∧
      (∀ z, collapse (maxHulls Z hZ b) rep z ∉ Z) ∧
      ∀ (c : Set (Site d) → Site d) (r : Set (Site d) → ℤ),
        (∀ H ∈ maxHulls Z hZ b, H ⊆ Ball (r H) (c H)) →
        ∀ u v, Step u v →
        ∃ p : (latticeGraph (RouteRegion Z (maxHulls Z hZ b)
          (fun H => Ball (r H + 1) (c H)) u v)).Walk
            (collapse (maxHulls Z hZ b) rep u) (collapse (maxHulls Z hZ b) rep v), p.IsPath := by
  let F := maxHulls Z hZ b
  have hF := maxHulls_disjoint Z hZ b hb
  have hBn : ∀ H ∈ F, (Boundary H).Nonempty := fun H hH =>
    allHulls_boundary_nonempty Z hZ b hb ((mem_maxHulls ..).mp hH).prop
  let rep (H : Set (Site d)) : Site d := if h : H ∈ F then (hBn H h).choose else 0
  have hrB : ∀ H ∈ F, rep H ∈ Boundary H := by
    intro H hH
    simpa only [rep,dite_eq_left hH] using (hBn H hH).choose_spec
  have hclear : ∀ H ∈ F, Boundary H ⊆ Zᶜ := by
    intro H hH v hv
    obtain ⟨x,hx,rfl⟩ := (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
    have hbC : b ∉ Thick 4 (Component Z x) := by
      rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
    exact boundary_unit_clear Z hbC hv (ball_self (by omega) v)
  refine ⟨rep,hrB,collapse_survives Z F rep (maxHulls_cover Z hZ b hb)
    (fun H hH => hclear H hH (hrB H hH)),?_⟩
  intro c r hbound u v huv
  apply reach_has_simple_path
  apply route_exists Z F hF rep _ (maxHulls_cover Z hZ b hb) _ hclear huv
  intro H hH w hw
  obtain ⟨x,hx,he⟩ := (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨a,ha,hba⟩; exact hb ⟨a,ha.1,hba⟩
  have hv : rep H ∈ Boundary (Hull (Thick 4 (Component Z x)) b) := by
    simpa only [he] using hrB H hH
  have hw' : w ∈ Boundary (Hull (Thick 4 (Component Z x)) b) := by
    simpa only [he] using hw
  have hB : Hull (Thick 4 (Component Z x)) b ⊆ Ball (r H) (c H) := by
    simpa only [he] using hbound H hH
  exact surviving_boundary_confined Z hx hbC (r H) hB (rep H) w hv hw'

lemma exists_exterior_base (hd : 1 ≤ d) (Z : Set (Site d)) (hZ : Z.Finite) :
    ∃ (r : ℕ) (b : Site d), Thick 4 Z ⊆ Box (r : ℤ) ∧ b ∉ Box (r : ℤ) := by
  obtain ⟨r,hr⟩ := finite_contained_box (Thick 4 Z) (thick_finite 4 Z hZ)
  refine ⟨r,(fun _ => (r : ℤ)+1),hr,?_⟩
  intro h
  have h0 := h ⟨0,by omega⟩
  simp only [abs_of_nonneg (by positivity : (0:ℤ) ≤ (r:ℤ)+1)] at h0
  omega

end Heisenberg.HullRouting
end

end OAI
