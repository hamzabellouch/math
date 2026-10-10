import OAI.Probability.BenjaminiSchramm.IntrinsicBallExposure

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def intrinsicSphere (G : BondGraph V E) (ω : Set E) (x : V) (n : ℕ) : Set V :=
  {y | Conn G ω x y ∧ (openSimpleGraph G ω).dist x y = n}

theorem exists_intrinsic_distance_eq (G : BondGraph V E) (ω : Set E)
    (x y : V) (hc : Conn G ω x y) (n : ℕ)
    (hn : n ≤ (openSimpleGraph G ω).dist x y) :
    ∃ z, Conn G ω x z ∧ (openSimpleGraph G ω).dist x z = n := by
  obtain ⟨w,hw⟩ := ((conn_iff_reachable G ω x y).mp hc).exists_walk_length_eq_dist
  have hshort := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_take n)
  have hlen : (w.take n).length = n := by
    rw [SimpleGraph.Walk.take_length,Nat.min_eq_left (by omega)]
  exact ⟨w.getVert n,(conn_iff_reachable G ω x _).mpr (w.take n).reachable,
    hshort.symm.trans hlen⟩

theorem intrinsicRadiusEvent_iff_sphere (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) :
    ω ∈ intrinsicRadiusEvent G x n ↔ (intrinsicSphere G ω x n).Nonempty := by
  constructor
  · rintro ⟨y,hc,hn⟩
    exact exists_intrinsic_distance_eq G ω x y hc n hn
  · rintro ⟨y,hc,hn⟩
    exact ⟨y,hc,hn.ge⟩

theorem intrinsicSphere_eq_ball_sdiff (G : BondGraph V E) (ω : Set E)
    (x : V) (n : ℕ) (hn : 0 < n) :
    intrinsicSphere G ω x n = intrinsicBall G ω x n \ intrinsicBall G ω x (n-1) := by
  ext y
  constructor
  · rintro ⟨hc,hd⟩
    refine ⟨(intrinsicBall_iff_distance_le G ω x y n hc).mpr hd.le,?_⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n-1) hc,hd]
    omega
  · rintro ⟨hy,hnot⟩
    obtain ⟨l,hl,hlen,ho⟩ := hy
    have hc := hl.conn ho
    have hle := (intrinsicBall_iff_distance_le G ω x y n hc).mp ⟨l,hl,hlen,ho⟩
    rw [intrinsicBall_iff_distance_le G ω x y (n-1) hc] at hnot
    exact ⟨hc,by omega⟩

theorem intrinsicSphere_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (n : ℕ) : (intrinsicSphere G ω x n).Finite := by
  apply (finite_reachBall hloc x n).subset
  rintro y ⟨hc,hd⟩
  exact intrinsicBall_subset_reachBall G ω x n
    ((intrinsicBall_iff_distance_le G ω x y n hc).mpr hd.le)

theorem intrinsicRadiusEvent_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (n : ℕ) :
    ω ∩ (incidentSupport G hloc (finite_reachBall hloc x n).toFinset : Set E) ∈
      intrinsicRadiusEvent G x n ↔ ω ∈ intrinsicRadiusEvent G x n := by
  by_cases hn : n = 0
  · subst n
    constructor <;> intro _ <;> exact ⟨x,mem_cluster_self G _ x,Nat.zero_le _⟩
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    rw [intrinsicRadiusEvent_iff_sphere,intrinsicRadiusEvent_iff_sphere,
      intrinsicSphere_eq_ball_sdiff G _ x n hn0,intrinsicSphere_eq_ball_sdiff G _ x n hn0,
      intrinsicBall_restrict G hloc]
    have he : intrinsicBall G
        (ω ∩ (incidentSupport G hloc (finite_reachBall hloc x n).toFinset : Set E)) x (n-1) =
        intrinsicBall G ω x (n-1) := by
      apply Set.Subset.antisymm (intrinsicBall_mono G Set.inter_subset_left x (n-1))
      rintro y ⟨l,hl,hlen,ho⟩
      exact ⟨l,hl,hlen,fun e he => ⟨ho e he,
        hl.bonds_in_incidentBall hloc n (hlen.trans (Nat.sub_le n 1)) e he⟩⟩
    rw [he]

theorem intrinsicSphere_disjoint (G : BondGraph V E) (ω : Set E) (x : V)
    {m n : ℕ} (hmn : m ≠ n) : Disjoint (intrinsicSphere G ω x m) (intrinsicSphere G ω x n) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨_,hm⟩ ⟨_,hn⟩
  exact hmn (hm.symm.trans hn)

end Percolation.BenjaminiSchramm

end OAI
