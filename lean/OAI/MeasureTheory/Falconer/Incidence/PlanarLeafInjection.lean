import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds
import OAI.MeasureTheory.Falconer.Measures.PrefixMass

namespace OAI

/-! Inject the original separated point set into sufficiently small dyadic
leaves, preserving the exact finite prefix counts. -/
namespace Falconer
open Set
open Regularization
attribute [local instance] Classical.propDecidable

theorem separated_planar_cube_card_le_one {δ : ℝ} {P : Finset (Space 2)}
    (hP : FiniteSeparatedAt δ P) (Q : DyadicCube 2) (hQ : 0 ≤ Q.side)
    (hsmall : Real.sqrt 2*Q.side < δ) :
    (P.filter fun x => x ∈ Q.carrier).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxP,hxQ⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyP,hyQ⟩ := Finset.mem_filter.mp hy
  have hs := hP x hxP y hyP hxy
  have hd := Q.dist_le hQ hxQ hyQ
  norm_num only [Nat.cast_ofNat] at hd
  linarith

theorem exists_planar_leaf_injection {δ : ℝ} {P : Finset (Space 2)}
    (hP : FiniteSeparatedAt δ P) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (hcarry : ∀ x ∈ P, x ∈ Q.carrier) (N : ℕ)
    (hsmall : Real.sqrt 2*(Q.side/(2 : ℝ)^N) < δ) :
    ∃ l : Space 2 → CellPath 2,
      (∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier) ∧
      Set.InjOn l (P : Set (Space 2)) := by
  classical
  have hex (x : Space 2) : ∃ p : CellPath 2,
      x ∈ P → p ∈ cubePaths 2 N ∧ x ∈ (Q.descendant p).carrier := by
    by_cases hx : x ∈ P
    · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth N (hcarry x hx)
      exact ⟨p,fun _ => ⟨hp,hxp⟩⟩
    · exact ⟨[],fun h => False.elim (hx h)⟩
  choose l hl using hex
  refine ⟨l,hl,?_⟩
  intro x hx y hy he
  by_contra hxy
  have hxQ := (hl x hx).2
  have hyQ := (hl y hy).2
  rw [← he] at hyQ
  have hside : 0 ≤ (Q.descendant (l x)).side := by rw [Q.descendant_side]; positivity
  have hd := (Q.descendant (l x)).dist_le hside hxQ hyQ
  have hlen : (l x).length = N := (mem_cubePaths _ _ _).mp (hl x hx).1
  rw [Q.descendant_side,hlen] at hd
  have hs := hP x hx y hy hxy
  linarith

theorem leaf_image_prefixFiber (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (k : ℕ) (p : CellPath 2) :
    prefixFiber (P.image l) k p = (P.filter fun x => (l x).take k = p).image l := by
  classical
  ext q
  simp only [prefixFiber,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,hp⟩,rfl⟩
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hp⟩

theorem leaf_image_prefixFiber_card {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2))) (k : ℕ) (p : CellPath 2) :
    (prefixFiber (P.image l) k p).card = (P.filter fun x => (l x).take k = p).card := by
  classical
  rw [leaf_image_prefixFiber]
  exact Finset.card_image_iff.mpr (hl.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))

theorem leaf_prefix_card_ball_bound {δ s K r : ℝ} {P : Finset (Space 2)}
    (hball : NormalizedFiniteBallBound δ s K P) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {l : Space 2 → CellPath 2} (hl : Set.InjOn l (P : Set (Space 2)))
    (hcarry : ∀ x ∈ P, x ∈ (Q.descendant (l x)).carrier)
    (k : ℕ) (p : CellPath 2) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hdiam : Real.sqrt 2*(Q.descendant p).side ≤ r) :
    ((prefixFiber (P.image l) k p).card : ℝ) ≤ K*r^s*(P.card : ℝ) := by
  classical
  rw [leaf_image_prefixFiber_card hl]
  have hside : 0 < (Q.descendant p).side := by rw [Q.descendant_side]; positivity
  have hsub : (P.filter fun x => (l x).take k = p) ⊆
      P.filter (fun x => dist x (Q.descendant p).center ≤ r) := by
    intro x hx
    obtain ⟨hxP,hxp⟩ := Finset.mem_filter.mp hx
    have hc := descendant_subset_take Q hQ (l x) k (hcarry x hxP)
    rw [hxp] at hc
    exact Finset.mem_filter.mpr ⟨hxP,
      ((Q.descendant p).dist_le hside.le hc ((Q.descendant p).center_mem hside)).trans hdiam⟩
  have hcard : ((P.filter fun x => (l x).take k = p).card : ℝ) ≤
      (P.filter (fun x => dist x (Q.descendant p).center ≤ r)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hball _ r hdr hr1)

theorem leaf_image_prefix_count_bound {δ s K r : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    {P : Finset (Space 2)} (hball : NormalizedFiniteBallBound δ s K P)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) {N k : ℕ} (hk : k ≤ N)
    {l : Space 2 → CellPath 2} (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hdr : δ ≤ r) (hr1 : r ≤ 1) (hdiam : Real.sqrt 2*(Q.side/(2 : ℝ)^k) ≤ r)
    (p : CellPath 2) :
    ((prefixFiber (P.image l) k p).card : ℝ) ≤ K*r^s*((P.image l).card : ℝ) := by
  classical
  rw [Finset.card_image_iff.mpr hl]
  by_cases hp : (prefixFiber (P.image l) k p).Nonempty
  · obtain ⟨q,hq⟩ := hp
    obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    have hlen : p.length = k := by
      rw [← hqp,List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hk]
    apply leaf_prefix_card_ball_bound hball Q hQ hl (fun x hx => (hleaf x hx).2) k p hdr hr1
    simpa only [Q.descendant_side,hlen] using hdiam
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (hδ.le.trans hdr) _)) (Nat.cast_nonneg _)

end Falconer

end OAI
