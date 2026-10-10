import OAI.Probability.BenjaminiSchramm.PublishedConsequences
import OAI.Probability.UnimodularPercolation.Subdivision.Coupling
import OAI.Probability.UnimodularPercolation.Deformation.Derivatives

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq Classical.propDecidable

theorem subdivision_open_adj_inl_inr (G : BondGraph V E) (ν : Set (E × Bool))
    (x : V) (e : E) :
    (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Adj (.inl x) (.inr e) ↔
      ∃ hx : x ∈ G e, (⟨(e, x), hx⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν := by
  change (_ ≠ _ ∧ ∃ d ∈ subdivisionOpen G ν, subdivision G d = s(Sum.inl x, Sum.inr e)) ↔ _
  rw [and_iff_right (by simp)]
  exact subdivision_open_adj_iff G ν x e

theorem exists_subdivision_lift_walk (G : BondGraph V E) (ν : Set (E × Bool))
    {x y : V} (w : (openSimpleGraph G (seriesOpen ν)).Walk x y) :
    ∃ q : (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Walk (.inl x) (.inl y),
      q.length = 2 * w.length := by
  induction w with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x z y h w ih =>
    obtain ⟨e, he, heq⟩ := h.2
    have hx : x ∈ G e := by simp [heq]
    have hz : z ∈ G e := by simp [heq]
    have hxe : (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Adj
        (.inl x) (.inr e) :=
      (subdivision_open_adj_inl_inr G ν x e).mpr ⟨hx, he _⟩
    have hze : (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Adj
        (.inl z) (.inr e) :=
      (subdivision_open_adj_inl_inr G ν z e).mpr ⟨hz, he _⟩
    obtain ⟨q, hq⟩ := ih
    refine ⟨.cons hxe (.cons hze.symm q), ?_⟩
    simp only [SimpleGraph.Walk.length_cons, hq]
    omega

theorem exists_subdivision_compress_walk (G : BondGraph V E) (ν : Set (E × Bool))
    {x y : V}
    (w : (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Walk (.inl x) (.inl y)) :
    ∃ q : (openSimpleGraph G (seriesOpen ν)).Walk x y,
      2 * q.length ≤ w.length := by
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases w with
    | nil => exact ⟨.nil, by simp⟩
    | @cons _ z _ h₁ w =>
      cases z with
      | inl z => exact (subdivision_adj_inl_inl G x z ⟨_, h₁.2.choose_spec.2⟩).elim
      | inr e =>
        cases w with
        | @cons _ z _ h₂ w =>
          cases z with
          | inr f => exact (subdivision_adj_inr_inr G e f ⟨_, h₂.2.choose_spec.2⟩).elim
          | inl z =>
            simp only [SimpleGraph.Walk.length_cons] at hn
            have hlen : w.length < n := by
              omega
            obtain ⟨q, hq⟩ := ih w.length hlen w rfl
            by_cases hxz : x = z
            · subst z
              refine ⟨q, ?_⟩
              omega
            · obtain ⟨hx, hxo⟩ := (subdivision_open_adj_inl_inr G ν x e).mp h₁
              obtain ⟨hz, hzo⟩ := (subdivision_open_adj_inl_inr G ν z e).mp h₂.symm
              have hseries := seriesOpen_of_two_incident G ν e x z hx hz hxz hxo hzo
              have hadj : (openSimpleGraph G (seriesOpen ν)).Adj x z :=
                ⟨hxz, e, hseries, (Sym2.mem_and_mem_iff hxz).mp ⟨hx, hz⟩⟩
              refine ⟨.cons hadj q, ?_⟩
              simp only [SimpleGraph.Walk.length_cons]
              omega

theorem subdivision_open_distance (G : BondGraph V E) (ν : Set (E × Bool))
    (x y : V) :
    (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).dist (.inl x) (.inl y) =
      2 * (openSimpleGraph G (seriesOpen ν)).dist x y := by
  by_cases hc : Conn G (seriesOpen ν) x y
  · have hr := (conn_iff_reachable G (seriesOpen ν) x y).mp hc
    have hs := (conn_iff_reachable (subdivision G) (subdivisionOpen G ν) (.inl x) (.inl y)).mp
      ((conn_subdivision_iff G ν x y).mpr hc)
    obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := exists_subdivision_lift_walk G ν w
    have hu : (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).dist (.inl x) (.inl y) ≤
        2 * (openSimpleGraph G (seriesOpen ν)).dist x y := by
      rw [← hw, ← hq]
      exact SimpleGraph.dist_le q
    obtain ⟨w', hw'⟩ := hs.exists_walk_length_eq_dist
    obtain ⟨q', hq'⟩ := exists_subdivision_compress_walk G ν w'
    have hl := Nat.mul_le_mul_left 2 (SimpleGraph.dist_le q')
    omega
  · have hr : ¬(openSimpleGraph G (seriesOpen ν)).Reachable x y :=
      fun h => hc ((conn_iff_reachable G (seriesOpen ν) x y).mpr h)
    have hs : ¬(openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Reachable
        (.inl x) (.inl y) := by
      intro h
      exact hc ((conn_subdivision_iff G ν x y).mp
        ((conn_iff_reachable (subdivision G) (subdivisionOpen G ν) (.inl x) (.inl y)).mpr h))
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hr,
      SimpleGraph.dist_eq_zero_of_not_reachable hs, mul_zero]

theorem subdivision_ambient_distance (G : BondGraph V E) (x y : V) :
    graphDistance (subdivision G) (.inl x) (.inl y) = 2 * graphDistance G x y := by
  have ho : subdivisionOpen G (Set.univ : Set (E × Bool)) = Set.univ := by
    ext e
    simp [subdivisionOpen]
  have hs : seriesOpen (Set.univ : Set (E × Bool)) = Set.univ := by
    ext e
    simp [seriesOpen]
  simpa only [graphDistance, ho, hs] using
    subdivision_open_distance G Set.univ x y

theorem subdivision_cluster_ncard_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (ν : Set (E × Bool)) (x : V)
    (hf : (cluster G (seriesOpen ν) x).Finite) :
    (cluster G (seriesOpen ν) x).ncard ≤
        (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).ncard ∧
    (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).ncard ≤
      (d + 1) * (cluster G (seriesOpen ν) x).ncard := by
  let S := hf.toFinset
  let I := incidentSupport G hloc S
  have hfin := (finite_cluster_subdivision_iff G hloc ν x).mpr hf
  have hinl : (Sum.inl : V → V ⊕ E) '' cluster G (seriesOpen ν) x ⊆
      cluster (subdivision G) (subdivisionOpen G ν) (.inl x) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (conn_subdivision_iff G ν x y).mpr hy
  have hcover : cluster (subdivision G) (subdivisionOpen G ν) (.inl x) ⊆
      (Sum.inl : V → V ⊕ E) '' cluster G (seriesOpen ν) x ∪
        (Sum.inr : E → V ⊕ E) '' (I : Set E) := by
    intro z hz
    cases z with
    | inl y => exact Or.inl ⟨y, (conn_subdivision_iff G ν x y).mp hz, rfl⟩
    | inr e =>
      obtain ⟨y, hy, hye⟩ := conn_subdivision_inr G ν x e hz
      apply Or.inr
      refine ⟨e, ?_, rfl⟩
      exact (mem_incidentSupport G hloc S e).mpr ⟨y, hf.mem_toFinset.mpr hy, hye⟩
  constructor
  · have hcard := Set.ncard_le_ncard hinl hfin
    simpa only [Set.ncard_image_of_injective _ Sum.inl_injective] using hcard
  · calc
      _ ≤ ((Sum.inl : V → V ⊕ E) '' cluster G (seriesOpen ν) x ∪
          (Sum.inr : E → V ⊕ E) '' (I : Set E)).ncard :=
        Set.ncard_le_ncard hcover ((hf.image _).union (I.finite_toSet.image _))
      _ ≤ ((Sum.inl : V → V ⊕ E) '' cluster G (seriesOpen ν) x).ncard +
          ((Sum.inr : E → V ⊕ E) '' (I : Set E)).ncard := Set.ncard_union_le _ _
      _ = (cluster G (seriesOpen ν) x).ncard + I.card := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_coe_finset]
      _ ≤ (cluster G (seriesOpen ν) x).ncard + S.card * d :=
        Nat.add_le_add_left (incidentSupport_card_le G hloc d hd S) _
      _ = (d + 1) * (cluster G (seriesOpen ν) x).ncard := by
        simp only [S, Set.ncard_eq_toFinset_card _ hf]
        ring

theorem conn_subdivision_inr_adj (G : BondGraph V E) (ν : Set (E × Bool))
    (x : V) (e : E)
    (hc : Conn (subdivision G) (subdivisionOpen G ν) (.inl x) (.inr e)) :
    ∃ y, Conn G (seriesOpen ν) x y ∧
      (openSimpleGraph (subdivision G) (subdivisionOpen G ν)).Adj (.inl y) (.inr e) := by
  rcases hc.cases_tail with h | ⟨z, hxz, hze⟩
  · cases h
  · cases z with
    | inl y =>
      exact ⟨y, (conn_subdivision_iff G ν x y).mp hxz, by exact ⟨by simp, hze⟩⟩
    | inr f =>
      obtain ⟨d, _, hd⟩ := hze
      exact (subdivision_adj_inr_inr G f e ⟨d, hd⟩).elim

theorem subdivision_intrinsicRadiusEvent (G : BondGraph V E)
    (ν : Set (E × Bool)) (x : V) (n : ℕ) :
    subdivisionOpen G ν ∈ intrinsicRadiusEvent (subdivision G) (.inl x) (2 * n) ↔
      seriesOpen ν ∈ intrinsicRadiusEvent G x n := by
  constructor
  · rintro ⟨z, hz, hdist⟩
    cases z with
    | inl y =>
      refine ⟨y, (conn_subdivision_iff G ν x y).mp hz, ?_⟩
      rw [subdivision_open_distance G ν x y] at hdist
      omega
    | inr e =>
      obtain ⟨y, hy, hadj⟩ := conn_subdivision_inr_adj G ν x e hz
      refine ⟨y, hy, ?_⟩
      have ht := hadj.reachable.dist_triangle_right (.inl x)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, subdivision_open_distance G ν x y] at ht
      omega
  · rintro ⟨y, hy, hdist⟩
    refine ⟨.inl y, (conn_subdivision_iff G ν x y).mpr hy, ?_⟩
    rw [subdivision_open_distance G ν x y]
    omega

theorem subdivision_extrinsicRadiusEvent (G : BondGraph V E)
    (ν : Set (E × Bool)) (x : V) (n : ℕ) :
    subdivisionOpen G ν ∈ extrinsicRadiusEvent (subdivision G) (.inl x) (2 * n) ↔
      seriesOpen ν ∈ extrinsicRadiusEvent G x n := by
  constructor
  · rintro ⟨z, hz, hdist⟩
    cases z with
    | inl y =>
      refine ⟨y, (conn_subdivision_iff G ν x y).mp hz, ?_⟩
      rw [subdivision_ambient_distance G x y] at hdist
      omega
    | inr e =>
      obtain ⟨y, hy, hadj⟩ := conn_subdivision_inr_adj G ν x e hz
      refine ⟨y, hy, ?_⟩
      have hfull : (openSimpleGraph (subdivision G) Set.univ).Adj (.inl y) (.inr e) := by
        obtain ⟨a, _, ha⟩ := hadj.2
        exact ⟨by simp, a, Set.mem_univ _, ha⟩
      have ht := hfull.reachable.dist_triangle_right (.inl x)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hfull] at ht
      change graphDistance (subdivision G) (.inl x) (.inr e) ≤
        graphDistance (subdivision G) (.inl x) (.inl y) + 1 at ht
      rw [subdivision_ambient_distance G x y] at ht
      omega
  · rintro ⟨y, hy, hdist⟩
    refine ⟨.inl y, (conn_subdivision_iff G ν x y).mpr hy, ?_⟩
    rw [subdivision_ambient_distance G x y]
    omega

theorem subdivision_volumeEvent_lower (G : BondGraph V E)
    (ν : Set (E × Bool)) (x : V) (n : ℕ)
    (h : seriesOpen ν ∈ volumeEvent G x n) :
    subdivisionOpen G ν ∈ volumeEvent (subdivision G) (.inl x) n := by
  change (n : ℕ∞) ≤ (cluster G (seriesOpen ν) x).encard at h
  change (n : ℕ∞) ≤ (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).encard
  apply h.trans
  exact Set.encard_le_encard_of_injOn
    (fun y hy => (conn_subdivision_iff G ν x y).mpr hy) Sum.inl_injective.injOn

theorem subdivision_volumeEvent_upper (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (ν : Set (E × Bool)) (x : V) (n : ℕ)
    (h : subdivisionOpen G ν ∈ volumeEvent (subdivision G) (.inl x) ((d + 1) * n)) :
    seriesOpen ν ∈ volumeEvent G x n := by
  by_cases hf : (cluster G (seriesOpen ν) x).Finite
  · have hfin := (finite_cluster_subdivision_iff G hloc ν x).mpr hf
    have hb := (subdivision_cluster_ncard_bounds G hloc d hd ν x hf).2
    have hcard : (d + 1) * n ≤
        (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).ncard := by
      change (((d + 1) * n : ℕ) : ℕ∞) ≤
        (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).encard at h
      rw [← hfin.cast_ncard_eq] at h
      exact_mod_cast h
    have hn : n ≤ (cluster G (seriesOpen ν) x).ncard := by
      exact Nat.le_of_mul_le_mul_left (hcard.trans hb) (by omega : 0 < d + 1)
    change (n : ℕ∞) ≤ (cluster G (seriesOpen ν) x).encard
    rw [← hf.cast_ncard_eq]
    exact_mod_cast hn
  · change (n : ℕ∞) ≤ (cluster G (seriesOpen ν) x).encard
    rw [Set.Infinite.encard_eq (Set.not_finite.mp hf)]
    exact le_top

end Percolation.BenjaminiSchramm

end OAI
