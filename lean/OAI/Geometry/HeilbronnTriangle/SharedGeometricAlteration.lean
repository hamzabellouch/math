import OAI.Geometry.HeilbronnTriangle.ConditionalSamples
import OAI.Geometry.HeilbronnTriangle.GeometricAlteration

namespace OAI


open Finset

noncomputable section

namespace Problem355.SharedGeometricAlteration

lemma triangleArea_swap_left (p q r : Point) : triangleArea p q r = triangleArea q p r := by
  unfold triangleArea
  have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
      -((p.1 - q.1) * (r.2 - q.2) - (p.2 - q.2) * (r.1 - q.1)) := by ring
  rw [h, abs_neg]

lemma triangleArea_swap_right (p q r : Point) : triangleArea p q r = triangleArea p r q := by
  unfold triangleArea
  have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
      -((r.1 - p.1) * (q.2 - p.2) - (r.2 - p.2) * (q.1 - p.1)) := by ring
  rw [h, abs_neg]

lemma pair_collision_iff {I : Type*} [DecidableEq I] (S : Finset I) (f : I → Point)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    {i, j} ∈ Alteration.collisionEdges S f ↔ f i = f j := by
  classical
  constructor
  · intro h
    simp only [Alteration.collisionEdges, mem_filter] at h
    obtain ⟨u, hu, v, hv, huv, he⟩ := h.2
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> aesop
  · exact Alteration.pair_mem_collisionEdges S f hi hj hij

lemma triple_bad_iff {I : Type*} [DecidableEq I] (S : Finset I) (f : I → Point)
    (a : ℝ) {i j k : I} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    {i, j, k} ∈ Alteration.badTripleEdges S f (Alteration.smallTriangle a) ↔
      Alteration.smallTriangle a (f i) (f j) (f k) := by
  classical
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw, he⟩ := (mem_filter.mp h).2
    simp only [mem_insert, mem_singleton] at hu hv hw
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl <;>
      simp_all [Alteration.smallTriangle, ne_comm, triangleArea_swap_left, triangleArea_swap_right]
  · exact Alteration.triple_mem_badTripleEdges S f (Alteration.smallTriangle a)
      hi hj hk hij hik hjk

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

def pairMass (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) : ℝ := by
  classical
  exact ∑ z : Θ × (Fin 2 → X),
    if point z.1 (z.2 0) = point z.1 (z.2 1)
      then ConditionalSamples.sharedWeight ρ μ z else 0

def tripleMass (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point) (a : ℝ) : ℝ := by
  classical
  exact ∑ z : Θ × (Fin 3 → X),
    if Alteration.smallTriangle a (point z.1 (z.2 0)) (point z.1 (z.2 1))
        (point z.1 (z.2 2))
      then ConditionalSamples.sharedWeight ρ μ z else 0

theorem exists_configuration (m n : ℕ) (hn : n ≤ m) (a p q : ℝ)
    (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point)
    (hρ0 : ∀ θ, 0 ≤ ρ θ) (hρ1 : ∑ θ, ρ θ = 1)
    (hμ0 : ∀ θ x, 0 ≤ μ θ x) (hμ1 : ∀ θ, ∑ x, μ θ x = 1)
    (hsquare : ∀ θ x, pointInUnitSquare (point θ x))
    (hpair : pairMass ρ μ point ≤ p) (htriple : tripleMass ρ μ point a ≤ q)
    (hbudget : (Nat.choose m 2 : ℝ) * p + (Nat.choose m 3 : ℝ) * q <
      ((m - n + 1 : ℕ) : ℝ)) :
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧ triangleAreasAtLeast P a := by
  classical
  let W : Θ × (Fin m → X) → ℝ := ConditionalSamples.sharedWeight ρ μ
  let f : (Θ × (Fin m → X)) → Fin m → Point := fun z i => point z.1 (z.2 i)
  apply Alteration.exists_point_configuration_of_marginal_bounds
    (univ : Finset (Θ × (Fin m → X))) W (univ : Finset (Fin m)) f n a
    (fun z _ => ConditionalSamples.sharedWeight_nonneg ρ μ hρ0 hμ0 z)
    (ConditionalSamples.sum_sharedWeight ρ μ hρ1 hμ1)
    (fun z _ i _ => hsquare z.1 (z.2 i)) (by simpa using hn) p q
  · intro e he
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
    have hiff (z : Θ × (Fin m → X)) :
        {i, j} ∈ Alteration.collisionEdges univ (f z) ↔
          point z.1 (z.2 i) = point z.1 (z.2 j) :=
      pair_collision_iff univ (f z) (mem_univ i) (mem_univ j) hij
    have hm := ConditionalSamples.shared_pair_marginal ρ μ hμ1 hij
      (fun θ x y => if point θ x = point θ y then (1 : ℝ) else 0)
    have heq : (∑ z : Θ × (Fin m → X),
        if {i, j} ∈ Alteration.collisionEdges univ (f z) then W z else 0) =
          pairMass ρ μ point := by
      simp_rw [hiff]
      simpa only [W, pairMass, mul_ite, mul_one, mul_zero] using hm
    exact heq.trans_le hpair
  · intro e he
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := card_eq_three.mp (mem_powersetCard.mp he).2
    have hiff (z : Θ × (Fin m → X)) :
        {i, j, k} ∈ Alteration.badTripleEdges univ (f z) (Alteration.smallTriangle a) ↔
          Alteration.smallTriangle a (point z.1 (z.2 i)) (point z.1 (z.2 j))
            (point z.1 (z.2 k)) :=
      triple_bad_iff univ (f z) a (mem_univ i) (mem_univ j) (mem_univ k) hij hik hjk
    have hm := ConditionalSamples.shared_triple_marginal ρ μ hμ1 hij hik hjk
      (fun θ x y z => if Alteration.smallTriangle a (point θ x) (point θ y) (point θ z)
        then (1 : ℝ) else 0)
    have heq : (∑ z : Θ × (Fin m → X),
        if {i, j, k} ∈ Alteration.badTripleEdges univ (f z) (Alteration.smallTriangle a)
          then W z else 0) = tripleMass ρ μ point a := by
      simp_rw [hiff]
      simpa only [W, tripleMass, mul_ite, mul_one, mul_zero] using hm
    exact heq.trans_le htriple
  · simpa using hbudget

end Problem355.SharedGeometricAlteration

end

end OAI
