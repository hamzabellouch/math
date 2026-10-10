import OAI.Combinatorics.CliqueFree.Splitting
import OAI.Combinatorics.CliqueFree.WalkCoupling
import OAI.Combinatorics.CliqueFree.FiniteCoupling

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
open FiniteCoupling
variable {G : SimpleGraph V}

omit [Fintype V] in
lemma bad_survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) :
    bad (Survives F good t) ≤ bad (F t.edge12 = F t.edge13) +
      bad (F t.edge12.rev = F t.edge23) + bad (F t.edge13.rev = F t.edge23.rev) +
      bad (good t.edge12) + bad (good t.edge12.rev) + bad (good t.edge13) +
      bad (good t.edge13.rev) + bad (good t.edge23) + bad (good t.edge23.rev) := by
  unfold Survives
  have h1 := bad_and (F t.edge12 = F t.edge13)
    (F t.edge12.rev = F t.edge23 ∧ F t.edge13.rev = F t.edge23.rev ∧
      good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h2 := bad_and (F t.edge12.rev = F t.edge23)
    (F t.edge13.rev = F t.edge23.rev ∧ good t.edge12 ∧ good t.edge12.rev ∧
      good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h3 := bad_and (F t.edge13.rev = F t.edge23.rev)
    (good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h4 := bad_and (good t.edge12)
    (good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h5 := bad_and (good t.edge12.rev)
    (good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h6 := bad_and (good t.edge13) (good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h7 := bad_and (good t.edge13.rev) (good t.edge23 ∧ good t.edge23.rev)
  have h8 := bad_and (good t.edge23) (good t.edge23.rev)
  linarith

lemma bad_mass_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t)) ≤
      3 * (∑ t, TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) +
      6 * (∑ t, TriangleState.weight w t * bad (good t.edge12)) := by
  have h := sum_le_sum (s := univ) fun t _ ↦
    mul_le_mul_of_nonneg_left (bad_survives F good t)
      (show 0 ≤ TriangleState.weight w t from
        mul_nonneg (mul_nonneg (hw t.first) (hw t.second)) (hw t.third))
  simp only [mul_add, sum_add_distrib] at h
  obtain ⟨h1,h2,h3,h4,h5⟩ := TriangleState.sum_edge_permutations w (fun e ↦ bad (good e))
  have hc2 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12.rev = F t.edge23)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) := by
    have h := TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13))
    convert h using 1
    apply sum_congr rfl
    intro t _
    change _ * bad (F t.edge12.rev = F t.edge23) = _ * bad (F t.edge23 = F t.edge12.rev)
    rw [eq_comm (a := F t.edge23)]
  have hc3 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge13.rev = F t.edge23.rev)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) :=
    (TriangleState.sum_rotate w (fun t ↦ bad (F (TriangleState.rotate t).edge12 = F (TriangleState.rotate t).edge13))).trans
      (TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13)))
  rw [h1,h2,h3,h4,h5,hc2,hc3] at h
  linarith

lemma surviving_mass_eq {w : V → ℝ}
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, if Survives F good t then TriangleState.weight w t else 0) =
      6 * triangleMass G w - ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t) := by
  rw [← TriangleState.sum_weight, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : Survives F good t <;> simp [bad, ht]

open FiniteEntropy FiniteKernel LocalWalk

/-- The finite-law aggregate of all corner and incidence losses. -/
lemma expected_loss_le [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) {q : (EdgeState G → EdgeState G) → ℝ}
    (hq : Law q) (hm : ∀ i y, (∑ F, if F i = y then q F else 0) = K i y)
    (hp : ∀ i j, (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j))
    (good : (EdgeState G → EdgeState G) → EdgeState G → Prop)
    (b : EdgeState G → EdgeState G → Prop)
    (hb : ∀ F e, good F e ↔ b e (F e)) :
    (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w *
        (6 * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) +
         6 * (∑ e, law G w e * ∑ y, K e y * bad (b e y))) := by
  have hcoup (i j : EdgeState G) : (∑ F, q F * bad (F i = F j)) ≤ 2 * tv (K i) (K j) := by
    convert hp i j using 1
    apply sum_congr rfl
    intro F _
    by_cases h : F i = F j <;> simp [bad, h]
  have hadm (e : EdgeState G) : (∑ F, q F * bad (good F e)) = ∑ y, K e y * bad (b e y) := by
    simp_rw [hb]
    exact marginal_expectation hm e (fun y ↦ bad (b e y))
  have hcorner : (∑ F, q F * ∑ t : TriangleState G,
      TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) ≤
      2 * normalizer G w * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (F t.edge12 = F t.edge13) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ ≤ ∑ t : TriangleState G, TriangleState.weight w t * (2 * tv (K t.edge12) (K t.edge13)) :=
        sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hcoup _ _) (TriangleState.weight_pos hw t).le
      _ = 2 * ∑ t : TriangleState G, TriangleState.weight w t * tv (K t.edge12) (K t.edge13) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ = _ := by
        rw [triangle_pair_sum hw hc (fun e z ↦ tv (K e) (K z))]
        ring
  have hincidence : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (good F t.edge12)) =
      normalizer G w * ∑ e, law G w e * ∑ y, K e y * bad (b e y) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (good F t.edge12) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ = _ := by simp_rw [hadm]; exact triangle_edge_sum hw hc (fun e ↦ ∑ y, K e y * bad (b e y))
  have h := sum_le_sum (s := univ) fun F _ ↦
    mul_le_mul_of_nonneg_left (bad_mass_le (fun u ↦ (hw u).le) F (good F)) (hq.1 F)
  simp only [mul_add, sum_add_distrib, ← mul_assoc] at h
  have hid (a : ℝ) (f : (EdgeState G → EdgeState G) → ℝ) :
      (∑ F, q F * a * f F) = a * ∑ F, q F * f F := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro F _
    ring
  rw [hid, hid, hincidence] at h
  nlinarith

/-- Splitting from a joint kernel preserving first coordinates, with two averaged losses. -/
lemma exists_graph [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) (hK : Stochastic K)
    (hblock : ∀ e z, e.src ≠ z.src → K e z = 0)
    {a D δ : ℝ}
    (hD : (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) ≤ D)
    (hδ : (∑ e, law G w e * ∑ y,
      if K y e < w e.dst * Real.exp (-a) then K e y else 0) ≤ δ) :
    ∃ H : SimpleGraph (EdgeState G), EdgeProjection H G EdgeState.src ∧
      (∀ z, neighborMass H (w ∘ EdgeState.src) z ≤ Real.exp a) ∧
      (1 - 6 * D - 6 * δ) * triangleMass G w ≤ triangleMass H (w ∘ EdgeState.src) := by
  obtain ⟨q,hq,hm,hp⟩ := shared_rejection K hK
  have hp' (i j : EdgeState G) : (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j) :=
    (hp i j).trans (sharp_bound_le (K i) (K j))
  let b : EdgeState G → EdgeState G → Prop := fun e y ↦ w e.dst * Real.exp (-a) ≤ K y e
  let good : (EdgeState G → EdgeState G) → EdgeState G → Prop := fun F e ↦ b e (F e)
  have hb (e y : EdgeState G) : K e y * bad (b e y) =
      if K y e < w e.dst * Real.exp (-a) then K e y else 0 := by
    by_cases h : K y e < w e.dst * Real.exp (-a)
    · simp [b,bad,h,not_le.2 h]
    · simp [b,bad,h,le_of_not_gt h]
  have hloss := expected_loss_le hw hc K hq hm hp' good b (fun _ _ ↦ Iff.rfl)
  simp_rw [hb] at hloss
  have hZ := (normalizer_pos hw hc).le
  have hZeq := normalizer_eq G w
  have hbound : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w * (6 * D + 6 * δ) :=
    hloss.trans (mul_le_mul_of_nonneg_left (by linarith [hD,hδ]) hZ)
  let S : (EdgeState G → EdgeState G) → ℝ := fun F ↦
    ∑ t : TriangleState G, if Survives F (good F) t then TriangleState.weight w t else 0
  have havg : normalizer G w * (1 - 6 * D - 6 * δ) ≤ ∑ F, q F * S F := by
    dsimp [S]
    simp_rw [surviving_mass_eq]
    rw [show (∑ F, q F * (6 * triangleMass G w -
        ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t))) =
        6 * triangleMass G w - ∑ F, q F * ∑ t : TriangleState G,
          TriangleState.weight w t * bad (Survives F (good F) t) by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hq.2, one_mul]]
    nlinarith
  obtain ⟨F,hFq,hFS⟩ := exists_positive_ge hq S havg
  have hF (e : EdgeState G) : (F e).src = e.src := by
    have hpos := positive_output hq hm hFq e
    by_contra hn
    have hzero := hblock e (F e) (Ne.symm hn)
    linarith
  let H := graph F hF (good F)
  refine ⟨H,projection F hF (good F),?_,?_⟩
  · intro z
    apply neighborMass_le w F hF (good F) K (fun a e ↦ (hK a).1 e)
      (fun a ↦ (hK a).2) (Real.exp_pos a).le ?_ z
    intro e he
    have hh : w e.dst * Real.exp (-a) ≤ K (F e) e := he
    have ht := mul_le_mul_of_nonneg_left hh (Real.exp_pos a).le
    have hid : Real.exp a * (w e.dst * Real.exp (-a)) = w e.dst := by
      calc
        _ = w e.dst * (Real.exp a * Real.exp (-a)) := by ring
        _ = _ := by rw [← Real.exp_add]; simp
    rwa [hid] at ht
  · have ht := triangleMass_surviving_le (fun v ↦ (hw v).le) F hF (good F)
    change S F ≤ 6 * triangleMass H (w ∘ EdgeState.src) at ht
    rw [hZeq] at hFS
    nlinarith only [ht, hFS]

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI
