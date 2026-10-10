import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Encounter.Geometry

namespace OAI

/-! Intrinsic distance and closest vertices in percolation clusters. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory SimpleGraph
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Along.exists_open_walk_length_le {G : BondGraph V E} {ω : Set E}
    {x y : V} {l : List E} (h : Along G x l y) (ho : ∀ e ∈ l, e ∈ ω) :
    ∃ w : (openSimpleGraph G ω).Walk x y, w.length ≤ l.length := by
  induction h with
  | nil => exact ⟨.nil,le_rfl⟩
  | @cons x z y l e he ht ih =>
      obtain ⟨w,hw⟩ := ih (fun a ha => ho a (by simp [ha]))
      by_cases hxz : x = z
      · subst z
        exact ⟨w,hw.trans (by simp)⟩
      · exact ⟨.cons ⟨hxz,e,ho e (by simp),he⟩ w,by change w.length + 1 ≤ l.length + 1; omega⟩

theorem mem_intrinsicBall_iff (G : BondGraph V E) (ω : Set E) (x y : V) (n : ℕ) :
    y ∈ intrinsicBall G ω x n ↔ Conn G ω x y ∧ (openSimpleGraph G ω).dist x y ≤ n := by
  constructor
  · rintro ⟨l,hl,hlen,ho⟩
    obtain ⟨w,hw⟩ := hl.exists_open_walk_length_le ho
    exact ⟨hl.conn ho,(SimpleGraph.dist_le w).trans (hw.trans hlen)⟩
  · rintro ⟨h,hn⟩
    obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp h).exists_walk_length_eq_dist
    obtain ⟨l,hl,hm,ho⟩ := walk_lift_bonds G ω w
    refine ⟨l,hl,?_,ho⟩
    have he := congrArg List.length hm
    have hh : l.length = (openSimpleGraph G ω).dist x y := by
      simpa only [List.length_map,Walk.length_edges,hw] using he
    exact hh ▸ hn

theorem measurableSet_mem_intrinsicBall [Countable E] (G : BondGraph V E)
    (x y : V) (n : ℕ) : MeasurableSet {ω | y ∈ intrinsicBall G ω x n} := by
  have he : {ω | y ∈ intrinsicBall G ω x n} =
      ⋃ (l : List E), {ω | Along G x l y ∧ l.length ≤ n ∧ ∀ e ∈ l, e ∈ ω} := by
    ext ω; simp [intrinsicBall]
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  by_cases hl : Along G x l y ∧ l.length ≤ n
  · have hm : MeasurableSet {ω : Set E | ∀ e ∈ l, e ∈ ω} := by
      simpa only [Set.ofPred_forall] using MeasurableSet.iInter (fun e =>
        MeasurableSet.iInter (fun _ : e ∈ l => (measurableSet_setOfPred.mpr (measurable_set_mem e))))
    simpa [hl.1,hl.2] using hm
  · have he : {ω : Set E | Along G x l y ∧ l.length ≤ n ∧ ∀ e ∈ l, e ∈ ω} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      intro h; exact hl ⟨h.1,h.2.1⟩
    rw [he]; exact MeasurableSet.empty

def closest (H : SimpleGraph V) (A : Set V) (x : V) : Set V :=
  {y | y ∈ A ∧ H.Reachable x y ∧ ∀ z ∈ A, H.Reachable x z → H.dist x y ≤ H.dist x z}

theorem closest_finite (G : BondGraph V E) (hloc : LocallyFinite G) (ω : Set E)
    (A : Set V) (x : V) : (closest (openSimpleGraph G ω) A x).Finite := by
  by_cases he : (closest (openSimpleGraph G ω) A x).Nonempty
  · obtain ⟨y,hy⟩ := he
    apply (finite_reachBall hloc x ((openSimpleGraph G ω).dist x y)).subset
    intro z hz
    apply intrinsicBall_subset_reachBall G ω x _
    exact (mem_intrinsicBall_iff G ω x z _).mpr
      ⟨(conn_iff_reachable G ω x z).mpr hz.2.1,hz.2.2 y hy.1 hy.2.1⟩
  · exact (Set.not_nonempty_iff_eq_empty.mp he) ▸ Set.finite_empty

theorem closest_nonempty (H : SimpleGraph V) (A : Set V) (x : V)
    (he : ∃ y ∈ A, H.Reachable x y) : (closest H A x).Nonempty := by
  let P : ℕ → Prop := fun n => ∃ y ∈ A, H.Reachable x y ∧ H.dist x y = n
  have hP : ∃ n, P n := by
    obtain ⟨y,hy,hr⟩ := he
    exact ⟨H.dist x y,y,hy,hr,rfl⟩
  obtain ⟨y,hy,hr,hd⟩ := Nat.find_spec hP
  refine ⟨y,hy,hr,?_⟩
  intro z hz hzr
  rw [hd]
  exact Nat.find_min' hP ⟨z,hz,hzr,rfl⟩

theorem mem_closest_iff_balls (G : BondGraph V E) (ω : Set E) (A : Set V) (x y : V) :
    y ∈ closest (openSimpleGraph G ω) A x ↔ y ∈ A ∧ Conn G ω x y ∧
      ∀ n z, z ∈ A → z ∈ intrinsicBall G ω x n → y ∈ intrinsicBall G ω x n := by
  constructor
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,(conn_iff_reachable G ω x y).mpr hr,?_⟩
    intro n z hz hzb
    obtain ⟨hzc,hzd⟩ := (mem_intrinsicBall_iff G ω x z n).mp hzb
    exact (mem_intrinsicBall_iff G ω x y n).mpr
      ⟨(conn_iff_reachable G ω x y).mpr hr,
        (hmin z hz ((conn_iff_reachable G ω x z).mp hzc)).trans hzd⟩
  · rintro ⟨hy,hc,hmin⟩
    refine ⟨hy,(conn_iff_reachable G ω x y).mp hc,?_⟩
    intro z hz hzr
    have hzb := (mem_intrinsicBall_iff G ω x z ((openSimpleGraph G ω).dist x z)).mpr
      ⟨(conn_iff_reachable G ω x z).mpr hzr,le_rfl⟩
    exact ((mem_intrinsicBall_iff G ω x y _).mp (hmin _ z hz hzb)).2

theorem measurableSet_mem_closest [Countable V] [Countable E]
    (G : BondGraph V E) (A : Set E → Set V)
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (x y : V) :
    MeasurableSet {ω | y ∈ closest (openSimpleGraph G ω) (A ω) x} := by
  simp only [mem_closest_iff_balls,Set.ofPred_and,Set.ofPred_forall]
  apply (hA y).inter
  apply (measurableSet_conn G x y).inter
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro z
  have he : {ω | z ∈ A ω → z ∈ intrinsicBall G ω x n → y ∈ intrinsicBall G ω x n} =
      {ω | z ∈ A ω}ᶜ ∪ {ω | z ∈ intrinsicBall G ω x n}ᶜ ∪
        {ω | y ∈ intrinsicBall G ω x n} := by ext ω; simp; tauto
  rw [he]
  exact ((hA z).compl.union (measurableSet_mem_intrinsicBall G x z n).compl).union
    (measurableSet_mem_intrinsicBall G x y n)

def openAutIso (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E)
    (h : IsAut G a b) (ω : Set E) :
    openSimpleGraph G (b ⁻¹' ω) ≃g openSimpleGraph G ω where
  toEquiv := a
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hxy,e,he,heq⟩
      refine ⟨fun hh => hxy (congrArg a hh),b.symm e,by simpa using he,?_⟩
      have hh := (isAut_symm G h) e
      rw [heq,Sym2.map_mk] at hh
      simpa only [Equiv.symm_apply_apply] using hh
    · rintro ⟨hxy,e,he,heq⟩
      exact ⟨fun hh => hxy (a.injective hh),b e,he,by rw [h,heq,Sym2.map_mk]⟩

theorem iso_dist {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (x y : V) : K.dist (f x) (f y) = H.dist x y := by
  by_cases hr : H.Reachable x y
  · obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
    have hr' := hr.map f.toHom
    obtain ⟨w',hw'⟩ := hr'.exists_walk_length_eq_dist
    apply le_antisymm
    · have hh := SimpleGraph.dist_le (w.map f.toHom)
      rw [Walk.length_map,hw] at hh
      exact hh
    · have hh := SimpleGraph.dist_le (w'.map f.symm.toHom)
      rw [Walk.length_map,hw'] at hh
      simpa using hh
  · have hr' : ¬K.Reachable (f x) (f y) := fun hh => hr (Iso.reachable_iff.mp hh)
    simp [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr),
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr')]

theorem closest_iso {W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : H ≃g K) (A : Set W) (x y : V) :
    y ∈ closest H (f ⁻¹' A) x ↔ f y ∈ closest K A (f x) := by
  constructor
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,hr.map f.toHom,?_⟩
    intro z hz hzr
    obtain ⟨z,rfl⟩ := f.surjective z
    simpa only [iso_dist] using hmin z hz (Iso.reachable_iff.mp hzr)
  · rintro ⟨hy,hr,hmin⟩
    refine ⟨hy,Iso.reachable_iff.mp hr,?_⟩
    intro z hz hzr
    simpa only [iso_dist] using hmin (f z) hz (hzr.map f.toHom)

theorem dist_lt_of_cut_separates (H : SimpleGraph V) {x y z : V}
    (hyr : H.Reachable y z) (hcut : ¬ (cutVertex H x).Reachable y z)
    (hxz : x ≠ z) : H.dist y x < H.dist y z := by
  obtain ⟨w,hw⟩ := hyr.exists_walk_length_eq_dist
  have hmem : x ∈ w.support := by
    by_contra hnot
    apply hcut
    exact walk_reachable_cut H H id (fun h => h) x w
      (fun a ha he => hnot (he ▸ ha))
  exact (SimpleGraph.dist_le (w.takeUntil x hmem)).trans_lt
    (hw ▸ w.length_takeUntil_lt_length hmem hxz)

theorem closest_eq_singleton_of_branch (H : SimpleGraph V) (A : Set V)
    {x y : V} (hx : x ∈ A) (hy : H.Reachable y x)
    (hbranch : ∀ z ∈ A, z ≠ x → ¬ (cutVertex H x).Reachable y z) :
    closest H A y = {x} := by
  have hstrict (z : V) (hz : z ∈ A) (hne : z ≠ x) (hr : H.Reachable y z) :
      H.dist y x < H.dist y z :=
    dist_lt_of_cut_separates H hr (hbranch z hz hne) hne.symm
  ext z
  constructor
  · intro hz
    have he : z = x := by
      by_contra hn
      exact (not_le_of_gt (hstrict z hz.1 hn hz.2.1)) (hz.2.2 x hx hy)
    exact he
  · intro hz
    have he : z = x := hz
    subst z
    refine ⟨hx,hy,?_⟩
    intro a ha hr
    by_cases he : a = x
    · subst a; exact le_rfl
    · exact (hstrict a ha he hr).le

end Percolation

end OAI
