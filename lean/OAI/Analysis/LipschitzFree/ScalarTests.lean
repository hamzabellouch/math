import OAI.Analysis.LipschitzFree.Attachment
import OAI.Analysis.LipschitzFree.GraphWalks
import OAI.Analysis.LipschitzFree.LabelBumps

namespace OAI

/-!
# Finite-state records and opposing scalar Lipschitz tests
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X E C : Type*} [Fintype C] [Fintype E]
    (G : PortGraph X E) (color : X → C) (cap R L K : ℕ) [Fact (0 < R)]

def Compatible (x : X) (j : Point G color cap R) : Prop :=
  dist (originalLabel G color cap x) (label G color cap R j) ≤ (K+2*L+1 : ℕ)

def Transition (j k : Point G color cap R) : Prop := dist j k ≤ (2*L : ℕ)

def supportColors (j : Point G color cap R) : Finset C :=
  Finset.univ.filter (fun i => (label G color cap R j i).val < cap)

omit [Fact (0 < R)] in
theorem supportColors_card (j : Point G color cap R) :
    (supportColors G color cap R j).card ≤ Fintype.card (BoundedWords E cap) := by
  have h := label_support_card G color cap R j
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, supportColors] using h

omit [Fintype E] [Fact (0 < R)] in
theorem compatible_color (hcap : K+2*L+1 < cap) (x : X) (j : Point G color cap R)
    (h : Compatible G color cap R L K x j) : color x ∈ supportColors G color cap R j := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, color_in_support G color cap R x j ?_⟩
  exact h.trans_lt (by exact_mod_cast hcap)

theorem transition_card (hR : 2*L < R) (S : Finset (Point G color cap R)) (j : S) :
    Fintype.card {k : S // Transition G color cap R L j.val k.val} ≤
      Fintype.card (BoundedWords E (2*L)) := by
  have hf := closedBall_finite G color cap R (2*L) hR j.val
  have : Finite (Metric.closedBall j.val ((2*L : ℕ) : ℝ)) := hf.to_subtype
  let f : {k : S // Transition G color cap R L j.val k.val} →
      Metric.closedBall j.val ((2*L : ℕ) : ℝ) := fun k => ⟨k.val.val, by
        rw [Metric.mem_closedBall, dist_comm]
        exact k.property⟩
  have hfi : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) huv
  have hh := (Nat.card_le_card_of_injective f hfi).trans
    (closedBall_card_le G color cap R (2*L) hR j.val)
  simpa only [Nat.card_eq_fintype_card] using hh

def exceptionSet (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E) : Set S :=
  {j | ¬ G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x ∨
    Exceptional (G.record (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x) e j}

omit [Fintype E] in
theorem exceptional_unique_good (S : Finset (Point G color cap R)) (n : ℕ) (x : X)
    (hx : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x)
    (j : S) (e f : E) (he : j ∈ exceptionSet G color cap R L K S n x e)
    (hf : j ∈ exceptionSet G color cap R L K S n x f) : e = f := by
  exact exceptional_unique (he.resolve_left (not_not.mpr hx)) (hf.resolve_left (not_not.mpr hx))

omit [Fintype E] in
theorem exceptional_endpoint (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E)
    (j k : S) (hj : Compatible G color cap R L K x j.val)
    (hk : Compatible G color cap R L K (G.move x e) k.val)
    (ht : Transition G color cap R L j.val k.val) :
    j ∈ exceptionSet G color cap R L K S n x e ∨
      k ∈ exceptionSet G color cap R L K S n (G.move x e) (G.reverse e) := by
  by_cases hx : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x
  · by_cases hy : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
        (fun j k : S => Transition G color cap R L j.val k.val) n (G.move x e)
    · have hh := G.matched_exceptional_endpoint
        (fun x (j : S) => Compatible G color cap R L K x j.val)
        (fun j k : S => Transition G color cap R L j.val k.val) hx hy hj hk ht
        (show Transition G color cap R L k.val j.val by simpa only [Transition, dist_comm] using ht)
      exact hh.imp Or.inr Or.inr
    · exact Or.inr (Or.inl hy)
  · exact Or.inl (Or.inl hx)

omit [Fintype E] in

theorem positive_bump_compatible (hL : 0 < L) (hK : 0 < K)
    (x : X) (e : E) (j k : Point G color cap R) (hjk : dist j k < (2*L : ℕ))
    (hj : 0 < labelBump (label G color cap R) (originalLabel G color cap x) L K j) :
    Compatible G color cap R L K x j ∧ Compatible G color cap R L K (G.move x e) k := by
  have hLj : dist (originalLabel G color cap x) (label G color cap R j) < K :=
    labelBump_positive _ _ (by exact_mod_cast hL) (by exact_mod_cast hK) hj
  have hedge : dist (originalLabel G color cap (G.move x e)) (originalLabel G color cap x) ≤ 1 := by
    rw [BoxLabel.dist_eq, BoxLabel.distance_comm]
    exact_mod_cast originalLabel_step G color cap x e
  have hstates : dist (label G color cap R j) (label G color cap R k) ≤ dist j k := by
    simpa only [NNReal.coe_one, one_mul] using (label_lipschitz G color cap R).dist_le_mul j k
  constructor
  · unfold Compatible
    push_cast
    linarith [show 0 ≤ (L : ℝ) from Nat.cast_nonneg L]
  · have htri := dist_triangle (originalLabel G color cap (G.move x e))
      (originalLabel G color cap x) (label G color cap R k)
    have htri' := dist_triangle (originalLabel G color cap x)
      (label G color cap R j) (label G color cap R k)
    unfold Compatible
    push_cast at hjk ⊢
    linarith

omit [Fintype E] in

theorem edge_test (hL : 0 < L) (hK : 0 < K) (hLK : L ≤ K)
    (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E) :
    ∃ f : Point G color cap R → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n x e →
        f j.val = labelBump (label G color cap R) (originalLabel G color cap x) L K j.val) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n (G.move x e) (G.reverse e) →
        f j.val = -labelBump (label G color cap R) (originalLabel G color cap (G.move x e)) L K j.val) := by
  let E₁ := exceptionSet G color cap R L K S n x e
  let E₂ := exceptionSet G color cap R L K S n (G.move x e) (G.reverse e)
  let P : Set (Point G color cap R) := {j | ∃ hj : j ∈ S, (⟨j,hj⟩ : S) ∉ E₁}
  let Q : Set (Point G color cap R) := {j | ∃ hj : j ∈ S, (⟨j,hj⟩ : S) ∉ E₂}
  let b := labelBump (label G color cap R) (originalLabel G color cap x) (L : ℝ) (K : ℝ)
  let c := labelBump (label G color cap R) (originalLabel G color cap (G.move x e)) (L : ℝ) (K : ℝ)
  have hL' : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  have hLK' : (L : ℝ) ≤ K := by exact_mod_cast hLK
  have hb (z) : 0 ≤ b z ∧ b z ≤ L := ⟨labelBump_nonneg _ _ hL' _, labelBump_le _ _ hL' hK' _⟩
  have hc (z) : 0 ≤ c z ∧ c z ≤ L := ⟨labelBump_nonneg _ _ hL' _, labelBump_le _ _ hL' hK' _⟩
  have hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2*(L : ℝ) → b j = 0 ∧ c k = 0 := by
    rintro j ⟨hj,hEj⟩ k ⟨hk,hEk⟩ hd
    have hd' : dist j k < (2*L : ℕ) := by exact_mod_cast hd
    have hfalse (hcompat : Compatible G color cap R L K x j ∧
        Compatible G color cap R L K (G.move x e) k) : False := by
      have hex := exceptional_endpoint G color cap R L K S n x e ⟨j,hj⟩ ⟨k,hk⟩
        hcompat.1 hcompat.2 hd'.le
      exact hex.elim hEj hEk
    constructor
    · by_contra hne
      exact hfalse (positive_bump_compatible G color cap R L K hL hK x e j k hd'
        (lt_of_le_of_ne (hb j).1 (Ne.symm hne)))
    · by_contra hne
      have hcomp := positive_bump_compatible G color cap R L K hL hK (G.move x e) (G.reverse e) k j
        (by simpa only [dist_comm] using hd') (lt_of_le_of_ne (hc k).1 (Ne.symm hne))
      rw [G.move_reverse] at hcomp
      exact hfalse hcomp.symm
  obtain ⟨f,hf,hbound,hfP,hfQ⟩ := opposing_scalar_extension P Q b c L hL'
    (labelBump_lipschitz _ (label_lipschitz G color cap R) _ hL' hK' hLK')
    (labelBump_lipschitz _ (label_lipschitz G color cap R) _ hL' hK' hLK') hb hc hcross
  exact ⟨f,hf,hbound,fun j hj => hfP ⟨j.property,hj⟩,fun j hj => hfQ ⟨j.property,hj⟩⟩

end DiscreteFree.MetricBlock
end

end

end OAI
