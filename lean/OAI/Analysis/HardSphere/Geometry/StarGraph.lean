import Mathlib
import OAI.Analysis.HardSphere.Geometry.FilledRegion

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

def starGraph : SimpleGraph Vertex where
  Adj := starStep
  symm := ⟨fun _ _ ↦ starStep_symm⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

def restrictedStarGraph (D : Set Vertex) : SimpleGraph Vertex where
  Adj x y := x ∈ D ∧ y ∈ D ∧ starStep x y
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, starStep_symm h.2.2⟩⟩
  loopless := ⟨fun _ h ↦ h.2.2.1 rfl⟩

lemma withinReach_star_path {D : Set Vertex} {v w : Vertex} (hv : v ∈ D)
    (h : withinReach starStep D v w) :
    ∃ p : starGraph.Walk v w, p.IsPath ∧ ∀ x ∈ p.support, x ∈ D := by
  have hr : (restrictedStarGraph D).Reachable v w :=
    (SimpleGraph.reachable_iff_reflTransGen v w).mpr h
  obtain ⟨q⟩ := hr
  let f : restrictedStarGraph D →g starGraph := ⟨id,fun {_ _} h ↦ h.2.2⟩
  have hs : ∀ {u z : Vertex} (p : (restrictedStarGraph D).Walk u z),
      u ∈ D → ∀ x ∈ p.support, x ∈ D := by
    intro u z p
    induction p with
    | nil =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact hu
    | @cons u v z huv p ih =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih huv.2.1 x hx
  refine ⟨q.toPath.val.map f, SimpleGraph.Walk.IsPath.map (fun _ _ h ↦ h) q.toPath.isPath, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
  change y = x at he
  subst x
  exact hs q.toPath.val hv y hy

lemma withinReach_star_first_entry {D A : Set Vertex} {x y : Vertex}
    (h : withinReach starStep D x y) (hxD : x ∈ D) (hx : x ∉ A) (hy : y ∈ A) :
    ∃ u v, withinReach starStep (D ∩ Aᶜ) x u ∧ u ∈ D ∧ u ∉ A ∧
      v ∈ D ∧ v ∈ A ∧ starStep u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hx hy).elim
  | @head z w hzw _ ih =>
    by_cases hw : w ∈ A
    · exact ⟨z,w,.refl,hxD,hx,hzw.2.1,hw,hzw.2.2⟩
    · obtain ⟨u,v,hu,huD,huA,hvD,hvA,huv⟩ := ih hzw.2.1 hw
      exact ⟨u,v,hu.head ⟨⟨hxD,hx⟩,⟨hzw.2.1,hw⟩,hzw.2.2⟩,huD,huA,hvD,hvA,huv⟩

theorem star_first_exit {D : Set Vertex} {z w : Vertex} {h d : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hz : z ∈ D)
    (hp : withinReach starStep D z w) (hw : ∃ i, d ≤ h * |(w i : ℝ) - z i|) :
    ∃ v, ∃ p : starGraph.Walk z v,
      (∀ x ∈ p.support, x ∈ D ∧ ∀ i, h * |(x i : ℝ) - z i| ≤ d + h) ∧
      (∃ i, d ≤ h * |(v i : ℝ) - z i|) := by
  let A : Set Vertex := {x | ∃ i, d ≤ h * |(x i : ℝ) - z i|}
  have hzA : z ∉ A := by simpa [A] using hd
  obtain ⟨u,v,hu,_,huA,hvD,hvA,huv⟩ := withinReach_star_first_entry hp hz hzA hw
  obtain ⟨p,_,hpD⟩ := withinReach_star_path (D := D ∩ Aᶜ) ⟨hz,hzA⟩ hu
  let q : starGraph.Walk z v := p.concat huv
  refine ⟨v,q,?_,hvA⟩
  intro x hx
  have hlocal (x : Vertex) (hx : x ∉ A) (i : Fin 3) :
      h * |(x i : ℝ) - z i| < d := by
    exact lt_of_not_ge (fun hi ↦ hx ⟨i,hi⟩)
  change x ∈ (p.concat (show starGraph.Adj u v from huv)).support at hx
  rw [SimpleGraph.Walk.support_concat] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | he
  · exact ⟨(hpD x hx).1, fun i ↦ (hlocal x (hpD x hx).2 i).le.trans (by linarith)⟩
  · subst x
    refine ⟨hvD,fun i ↦ ?_⟩
    have hedge : |(v i : ℝ) - u i| ≤ 1 := by
      exact_mod_cast (starStep_symm huv).2 i
    calc
      h * |(v i : ℝ) - z i| ≤ h * (|(v i : ℝ) - u i| + |(u i : ℝ) - z i|) :=
        mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) hh.le
      _ ≤ h * (1 + |(u i : ℝ) - z i|) := mul_le_mul_of_nonneg_left (add_le_add hedge le_rfl) hh.le
      _ ≤ d + h := by nlinarith [hlocal u huA i]

lemma star_path_span {z v : Vertex} (p : starGraph.Walk z v) (i : Fin 3) :
    |z i - v i| ≤ p.support.toFinset.card - 1 := by
  classical
  let S : Set Vertex := {x | x ∈ p.support}
  have hfin : S.Finite := p.support.finite_toSet
  let : Fintype S := hfin.fintype
  have hs : Fintype.card S = p.support.toFinset.card := by
    rw [Set.fintypeCard_eq_ncard]
    change {x | x ∈ p.support}.ncard = p.support.toFinset.card
    simpa only [List.coe_toFinset] using Set.ncard_coe_finset p.support.toFinset
  have hspan := connected_coordinate_span (starGraph.induce S)
    p.connected_induce_support.preconnected (fun x ↦ x.val) 1
    (fun x y hxy j ↦ hxy.2 j) ⟨z,p.start_mem_support⟩ ⟨v,p.end_mem_support⟩ i
  simpa only [Nat.cast_one, one_mul, hs] using hspan

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma local_projection_injective {J : ℕ} {h d : ℝ} (hh : 0 < h)
    (hwide : 2*d < h*J) (z : Vertex) :
    Set.InjOn (torusProjection J) {x | ∀ i, h * |(x i : ℝ) - z i| ≤ d} := by
  intro x hx y hy he
  ext i
  apply sub_eq_zero.mp
  apply small_multiple_zero
  · simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  · have hab : h * |(x i : ℝ) - y i| < h*J := by
      calc
        _ ≤ h * (|(x i : ℝ) - z i| + |(y i : ℝ) - z i|) := by
          apply mul_le_mul_of_nonneg_left _ hh.le
          simpa only [abs_sub_comm (z i : ℝ) (y i : ℝ)] using abs_sub_le (x i : ℝ) (z i : ℝ) (y i : ℝ)
        _ ≤ 2*d := by nlinarith [hx i, hy i]
        _ < _ := hwide
    have hc : |(x i : ℝ) - y i| < (J : ℝ) := (mul_lt_mul_iff_right₀ hh).mp hab
    exact_mod_cast hc

lemma card_witness_sites_le {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (Y : Configuration n L) (S : Finset Vertex)
    (hinj : Set.InjOn (torusProjection J) (↑S)) (j : Fin n)
    (hw : ∀ z ∈ S, ∃ x ∈ microCube L h z, torusDistance L x (Y j) ≤ r) :
    S.card ≤ 343 := by
  have hJ : J ≠ 0 := by
    intro he
    have hp := L.property
    simp only [he, Nat.cast_zero, mul_zero] at hperiod
    linarith
  let : NeZero J := ⟨hJ⟩
  calc
    S.card = (torusProjection J '' (↑S : Set Vertex)).ncard := by
      rw [hinj.ncard_image, Set.ncard_coe_finset]
    _ ≤ (torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x (Y j) ≤ r}).ncard :=
      Set.ncard_le_ncard (Set.image_mono hw) (Set.toFinite _)
    _ ≤ 343 := ncard_ball_bad_sites_le hh hperiod hr (Y j)

end HardSphere.BathSlice

end

end OAI
