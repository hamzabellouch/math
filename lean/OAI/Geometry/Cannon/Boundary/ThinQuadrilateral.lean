import Mathlib
import OAI.Geometry.Cannon.Boundary.Thin

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric
open Set Metric Topology

namespace CannonGraph

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma thin_quadrilateral (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    {a b c d : V} (p : G.Walk a b) (q : G.Walk b c)
    (r : G.Walk c d) (s : G.Walk d a)
    (hp : p.length = G.dist a b) (hq : q.length = G.dist b c)
    (hr : r.length = G.dist c d) (hs : s.length = G.dist d a)
    {x : V} (hx : x ∈ p.support) :
    ∃ y ∈ q.support ++ r.support ++ s.support, G.dist x y ≤ 2*δ := by
  obtain ⟨t,ht⟩ := hG.exists_walk_length_eq_dist b d
  obtain ⟨y,hy,hxy⟩ := hthin a b d p t s hp ht hs x hx
  rcases List.mem_append.mp hy with hy | hy
  · have htr : t.reverse.length = G.dist d b := by
      simpa [SimpleGraph.dist_comm] using ht
    obtain ⟨z,hz,hyz⟩ := hthin d b c t.reverse q r htr hq hr y (by simpa using hy)
    refine ⟨z, ?_, ?_⟩
    · exact List.mem_append_left _ hz
    · have := @Connected.dist_triangle _ G x y z hG
      omega
  · exact ⟨y, List.mem_append_right _ hy, by omega⟩

theorem asymptotic_rays_asynchronous (hG : G.Connected) {δ : ℕ} (hthin : Thin G δ)
    (r s : ℕ → V) (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (hs : ∀ i j, G.dist (s i) (s j) = Nat.dist i j)
    (hbounded : ∃ C : ℕ, ∀ n, G.dist (r n) (s n) ≤ C)
    {n : ℕ} (hn : G.dist (r 0) (s 0) + 2*δ < n) :
    ∃ m : ℕ, G.dist (r n) (s m) ≤ 2*δ ∧
      m ≤ n + G.dist (r 0) (s 0) + 2*δ ∧
      n ≤ m + G.dist (r 0) (s 0) + 2*δ := by
  obtain ⟨C,hC⟩ := hbounded
  let N := n+C+2*δ+1
  have hnN : n ≤ N := by dsimp [N]; omega
  let p := raySegment r hr N
  let q := raySegment s hs N
  obtain ⟨u,hu⟩ := hG.exists_walk_length_eq_dist (r N) (s N)
  obtain ⟨v,hv⟩ := hG.exists_walk_length_eq_dist (s 0) (r 0)
  have hp : p.length = G.dist (r 0) (r N) := by simp [p,hr,Nat.dist]
  have hq : q.reverse.length = G.dist (s N) (s 0) := by simp [q,hs,Nat.dist]
  have hrn : r n ∈ p.support := by
    rw [← raySegment_getVert r hr hnN]
    exact Walk.getVert_mem_support _ _
  obtain ⟨y,hy,hd⟩ := thin_quadrilateral hG hthin p u q.reverse v hp hu hq hv hrn
  rcases List.mem_append.mp hy with hy | hy
  · rcases List.mem_append.mp hy with hy | hy
    · have hNy : G.dist (r N) y ≤ C := by
        have he := of_mem_geodesic hG u hu hy
        have hCN := hC N
        omega
      have htri := @Connected.dist_triangle _ G (r N) y (r n) hG
      rw [SimpleGraph.dist_comm (u := y) (v := r n), hr] at htri
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hnN] at htri
      have hN : N = n+C+2*δ+1 := rfl
      omega
    · have hyq : y ∈ q.support := by simpa using hy
      obtain ⟨m,hm,hmb⟩ := Walk.mem_support_iff_exists_getVert.mp hyq
      have hmN : m ≤ N := by simpa [q] using hmb
      have hym : y = s m := by
        rw [← hm]
        exact raySegment_getVert s hs hmN
      rw [hym] at hd
      refine ⟨m,hd,?_,?_⟩
      · have ht₁ := @Connected.dist_triangle _ G (s 0) (r 0) (r n) hG
        have ht₂ := @Connected.dist_triangle _ G (s 0) (r n) (s m) hG
        rw [SimpleGraph.dist_comm (u := s 0) (v := r 0), hr] at ht₁
        rw [hs] at ht₂
        simp only [Nat.dist_zero_left] at ht₁ ht₂
        omega
      · have ht₁ := @Connected.dist_triangle _ G (r 0) (s 0) (s m) hG
        have ht₂ := @Connected.dist_triangle _ G (r 0) (s m) (r n) hG
        rw [hs] at ht₁
        rw [hr, SimpleGraph.dist_comm (u := s m) (v := r n)] at ht₂
        simp only [Nat.dist_zero_left] at ht₁ ht₂
        omega
  · have hy₀ : G.dist y (r 0) ≤ G.dist (r 0) (s 0) := by
      have he := of_mem_geodesic hG v hv hy
      rw [SimpleGraph.dist_comm (u := s 0) (v := r 0)] at he
      omega
    have ht := @Connected.dist_triangle _ G (r n) y (r 0) hG
    rw [hr] at ht
    simp only [Nat.dist_zero_right] at ht
    omega

end CannonGraph

namespace CannonGraph

open SimpleGraph

variable {H : Type*} [Group H] {G : SimpleGraph H}

theorem asymptotic_translate_card_bound (hG : G.Connected)
    (hleft : ∀ a x y : H, G.dist (a*x) (a*y) = G.dist x y)
    {δ : ℕ} (hthin : Thin G δ) (r : ℕ → H) (hr₀ : r 0 = 1)
    (hr : ∀ i j, G.dist (r i) (r j) = Nat.dist i j)
    (B : Finset H) (hB : ∀ x, G.dist 1 x ≤ 2*δ → x ∈ B)
    (F : Finset H) (t : ℕ)
    (ht : ∀ q ∈ F, G.dist 1 q ≤ t)
    (hfix : ∀ q ∈ F, ∃ C : ℕ, ∀ n, G.dist (q*r n) (r n) ≤ C) :
    F.card ≤ (2*t+4*δ+2) * B.card := by
  classical
  let n := t+2*δ+1
  have hnear : ∀ q : {q // q ∈ F}, ∃ m : ℕ,
      G.dist (q.val*r n) (r m) ≤ 2*δ ∧ m < 2*t+4*δ+2 := by
    intro q
    have hqr : ∀ i j, G.dist (q.val*r i) (q.val*r j) = Nat.dist i j := by
      intro i j
      rw [hleft,hr]
    have hd₀ : G.dist (q.val*r 0) (r 0) = G.dist 1 q.val := by
      rw [hr₀,mul_one,SimpleGraph.dist_comm]
    have hqn : G.dist (q.val*r 0) (r 0) + 2*δ < n := by
      rw [hd₀]
      have := ht q.val q.property
      dsimp [n]
      omega
    obtain ⟨m,hm,hm₁,_⟩ := asymptotic_rays_asynchronous hG hthin
      (fun k => q.val*r k) r hqr hr (hfix q.val q.property) hqn
    refine ⟨m,hm,?_⟩
    rw [hd₀] at hm₁
    have := ht q.val q.property
    dsimp [n] at hm₁
    omega
  choose m hm using hnear
  have hmem : ∀ q : {q // q ∈ F}, (r (m q))⁻¹ * (q.val*r n) ∈ B := by
    intro q
    apply hB
    have he := hleft (r (m q)) 1 ((r (m q))⁻¹ * (q.val*r n))
    simp only [mul_one,mul_inv_cancel_left] at he
    rw [← he, SimpleGraph.dist_comm]
    exact (hm q).1
  let f : {q // q ∈ F} → Fin (2*t+4*δ+2) × {x // x ∈ B} := fun q =>
    (⟨m q,(hm q).2⟩, ⟨(r (m q))⁻¹ * (q.val*r n),hmem q⟩)
  have hf : Function.Injective f := by
    intro q q' he
    have hm' : m q = m q' := congrArg (fun p => p.1.val) he
    have hx : (r (m q))⁻¹ * (q.val*r n) = (r (m q'))⁻¹ * (q'.val*r n) :=
      congrArg (fun p => p.2.val) he
    rw [hm'] at hx
    exact Subtype.ext (mul_right_cancel (mul_left_cancel hx))
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

end CannonGraph

end
end
end
end
end
end
end
end
end
end

end OAI
