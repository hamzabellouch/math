import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryControlledDiskCover
import OAI.Geometry.Cannon.PlaneTopology.IncidentEdges

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonEmbeddedArc
namespace Arc
open Set Metric

variable {X : Type*} [MetricSpace X]

theorem separated_arc_coloring {T κ : Type*} [Fintype T] [Fintype κ]
    (q : T → X) (src tgt : κ → T) (hpair : Function.Injective (fun i => (src i,tgt i)))
    (A : κ → Arc X) (h₀ : ∀ i, A i 0=q (src i)) (h₁ : ∀ i, A i 1=q (tgt i))
    {B : ℝ} (hB : 0<B) (hd : ∀ i, diam (range (A i))≤B) (K : ℕ)
    (hlocal : ∀ x, ((Finset.univ : Finset T).filter (fun t => dist x (q t)≤7*B)).card≤K) :
    ∃ color : κ → Fin (K^2+1), ∀ i j, i≠j → color i=color j →
      ∀ x∈range (A i), ∀ y∈range (A j), 4*B<dist x y := by
  classical
  let R : κ → κ → Prop := fun i j => dist (q (src i)) (q (src j))≤6*B
  have hcount (i : κ) : ((Finset.univ : Finset κ).filter (R i)).card≤K^2 := by
    let S := (Finset.univ : Finset T).filter (fun t => dist (q (src i)) (q t)≤7*B)
    have hmaps : Set.MapsTo (fun j => (src j,tgt j))
        (↑((Finset.univ : Finset κ).filter (R i)) : Set κ) (↑(S×ˢS) : Set (T×T)) := by
      intro j hj
      have hh := (Finset.mem_filter.mp hj).2
      have hst : dist (q (src j)) (q (tgt j))≤B := by
        rw [← h₀ j,← h₁ j]
        exact (Metric.dist_le_diam_of_mem (A j).compact_range.isBounded
          (mem_range_self 0) (mem_range_self 1)).trans (hd j)
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
      · dsimp [R] at hh
        linarith
      · have ht := dist_triangle (q (src i)) (q (src j)) (q (tgt j))
        dsimp [R] at hh
        linarith
    calc
      _ ≤ (S×ˢS).card := Finset.card_le_card_of_injOn _ hmaps hpair.injOn
      _ = S.card^2 := by simp [pow_two]
      _ ≤ K^2 := Nat.pow_le_pow_left (hlocal (q (src i))) 2
  obtain ⟨color,hc⟩ := CannonDiskColoring.finite_relation_coloring R
    (fun i j h => by simpa only [R,dist_comm] using h) hcount
  refine ⟨color,?_⟩
  intro i j hij hcij x hx y hy
  have hfar : 6*B<dist (q (src i)) (q (src j)) := lt_of_not_ge (fun h => hc i j hij h hcij)
  have hxi : dist (q (src i)) x≤B := by
    rw [← h₀ i]
    exact (Metric.dist_le_diam_of_mem (A i).compact_range.isBounded (mem_range_self 0) hx).trans (hd i)
  have hyj : dist y (q (src j))≤B := by
    rw [← h₀ j]
    exact (Metric.dist_le_diam_of_mem (A j).compact_range.isBounded hy (mem_range_self 0)).trans (hd j)
  have ht := dist_triangle4 (q (src i)) x y (q (src j))
  linarith

theorem net_arc_graph (Q : ℕ) (C L : ℝ)
    (hp : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hL : 1≤L) :
    ∃ K : ℕ, ∀ (r : ℝ), 0<r → 7*L*r≤1 → ∀ T : Finset X,
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
        ∃ a : Arc X, a 0=x ∧ a 1=y ∧ diam (range a)≤L*r) →
      ∃ n : ℕ, ∃ F : Fin n → Arc X,
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
           Vertex F x ∧ Vertex F y ∧ ∃ b : Arc X, b 0=x ∧ b 1=y ∧
             range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*L*r) ∧
        (∀ j, diam (range (F j))≤L*r) ∧
        (∀ x, intersectionCount F (ball x (2*L*r))≤K) := by
  classical
  have hLpos : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨K,hK⟩ := CannonPacking.exists_overlap_bound Q C (7*L) 1 hp hC (by positivity) zero_lt_one
  refine ⟨colorBound (K^2+1),?_⟩
  intro r hr hs T hsep harc
  let P := {p : T×T // p.1≠p.2 ∧ dist p.1.val p.2.val<4*r}
  have hAP (p : P) : ∃ a : Arc X, a 0=p.val.1.val ∧ a 1=p.val.2.val ∧ diam (range a)≤L*r :=
    harc p.val.1.val p.val.1.property p.val.2.val p.val.2.property
      (fun h => p.property.1 (Subtype.ext h)) p.property.2
  choose A h₀ h₁ hd using hAP
  have hlocal (x : X) : ((Finset.univ : Finset T).filter
      (fun t => dist x t.val≤7*(L*r))).card≤K := by
    have hscale : max (7*L) 1*r≤1 := by rw [max_eq_left (by linarith : (1:ℝ)≤7*L)]; exact hs
    have hsep' : ∀ i∈(Finset.univ : Finset T), ∀ j∈(Finset.univ : Finset T),
        i≠j → 1*r≤dist i.val j.val := by
      intro i _ j _ hij
      simpa only [one_mul] using (hsep i.val i.property j.val j.property
        (fun h => hij (Subtype.ext h)))
    simpa only [mul_assoc] using hK (fun t : T => t.val) Finset.univ x r hr hscale hsep'
  obtain ⟨color,hcolor⟩ := separated_arc_coloring (fun t : T => t.val)
    (fun p : P => p.val.1) (fun p : P => p.val.2)
    (fun i j h => Subtype.ext h) A h₀ h₁ (mul_pos hLpos hr) hd K hlocal
  obtain ⟨n,F,hFc,hFv,hFj,hFd,hFt,_⟩ := colored_arc_graph A (K^2+1) color (mul_pos hLpos hr) hd hcolor
  refine ⟨n,F,hFc,?_,hFd,?_⟩
  · intro x hx y hy hxy hnear
    let p : P := ⟨(⟨x,hx⟩,⟨y,hy⟩),fun h => hxy (congrArg Subtype.val h),hnear⟩
    have hv := hFv p
    obtain ⟨b,hb₀,hb₁,hbs,hbd⟩ := hFj p
    refine ⟨?_,?_,b,?_,?_,hbs,?_⟩
    · simpa only [h₀,p] using hv.1
    · simpa only [h₁,p] using hv.2
    · exact hb₀.trans (h₀ p)
    · exact hb₁.trans (h₁ p)
    · simpa only [mul_assoc] using hbd
  · simpa only [mul_assoc] using hFt

end Arc
end CannonEmbeddedArc

end
end
end
end
end
end

end OAI
