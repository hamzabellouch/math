import OAI.Analysis.LipschitzFree.BoxLabels
import OAI.Analysis.LipschitzFree.PortGraphs
import OAI.Analysis.LipschitzFree.MetricClosure

namespace OAI

/-!
# Metric blocks obtained by adjoining finite label anchors
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

def originalLabel (x : X) : BoxLabel C cap :=
  fun i => ⟨G.label color cap i x, Nat.lt_succ_of_le (G.label_le color cap i x)⟩

def Anchor := {a : BoxLabel C cap // a ∈ Set.range (originalLabel G color cap)}

instance : Fintype (Anchor G color cap) := inferInstanceAs (Fintype {a : BoxLabel C cap // a ∈ Set.range (originalLabel G color cap)})

def Point (_R : ℕ) := X ⊕ Anchor G color cap

instance [Countable X] : Countable (Point G color cap R) := inferInstanceAs (Countable (X ⊕ Anchor G color cap))

def ofVertex (x : X) : Point G color cap R := Sum.inl x

def ofAnchor (a : Anchor G color cap) : Point G color cap R := Sum.inr a

def anchorOf (x : X) : Anchor G color cap := ⟨originalLabel G color cap x, x, rfl⟩

def label : Point G color cap R → BoxLabel C cap
  | Sum.inl x => originalLabel G color cap x
  | Sum.inr a => a.val

def Adj (x y : X) : Prop := ∃ e, G.move x e = y

theorem adj_symm {x y : X} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨G.reverse e, G.move_reverse x e⟩

theorem adj_comm (x y : X) : Adj G x y ↔ Adj G y x := ⟨adj_symm G, adj_symm G⟩

def weight (u v : Point G color cap R) : ℕ :=
  if u = v then 0 else match u, v with
  | Sum.inl x, Sum.inl y => if Adj G x y then 1 else 4*R+cap
  | Sum.inl x, Sum.inr a => if originalLabel G color cap x = a.val then R else 4*R+cap
  | Sum.inr a, Sum.inl x => if originalLabel G color cap x = a.val then R else 4*R+cap
  | Sum.inr a, Sum.inr b => 2*R + BoxLabel.distance a.val b.val

@[simp] theorem weight_self (u : Point G color cap R) : weight G color cap R u u = 0 := by
  simp [weight]

theorem weight_symm (u v : Point G color cap R) : weight G color cap R u v = weight G color cap R v u := by
  by_cases h : u = v
  · subst v; rfl
  · cases u <;> cases v <;>
      simp only [weight, ite_eq_right h, ite_eq_right (Ne.symm h)]
    · rw [adj_comm]
    · rw [BoxLabel.distance_comm]

theorem weight_pos (hR : 0 < R) {u v : Point G color cap R} (huv : u ≠ v) :
    0 < weight G color cap R u v := by
  cases u <;> cases v <;> simp only [weight, ite_eq_right huv]
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · omega

theorem weight_zero (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v = 0) : u = v := by
  by_contra hne
  have hp := weight_pos G color cap R hR hne
  omega

abbrev metric (hR : 0 < R) : MetricSpace (Point G color cap R) :=
  NatMetricClosure.metricSpace (weight G color cap R) (weight_self G color cap R)
    (weight_symm G color cap R) (weight_zero G color cap R hR)

instance [Fact (0 < R)] : MetricSpace (Point G color cap R) := metric G color cap R Fact.out

variable [Fact (0 < R)]

theorem dist_eq (u v : Point G color cap R) : dist u v =
    (NatMetricClosure.distance (weight G color cap R) u v : ℝ) := rfl

theorem separated {u v : Point G color cap R} (h : u ≠ v) : 1 ≤ dist u v :=
  NatMetricClosure.separated (weight G color cap R) (weight_self G color cap R)
    (weight_symm G color cap R) (weight_zero G color cap R Fact.out) h

theorem weight_bound (u v : Point G color cap R) : weight G color cap R u v ≤ 4*R+cap := by
  have hR : 0 < R := Fact.out
  by_cases h : u = v
  · simp [h]
  · cases u <;> cases v <;> simp only [weight, ite_eq_right h]
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · exact (Nat.add_le_add_left (BoxLabel.distance_bound _ _) _).trans (by omega)

theorem diameter_bound (u v : Point G color cap R) : dist u v ≤ (4*R+cap : ℕ) := by
  rw [dist_eq]
  exact_mod_cast (NatMetricClosure.distance_le _ u v).trans (weight_bound G color cap R u v)

theorem source_edge (x : X) (e : D) :
    dist (ofVertex G color cap R x) (ofVertex G color cap R (G.move x e)) ≤ 1 := by
  rw [dist_eq]
  unfold ofVertex
  have hn : NatMetricClosure.distance (weight G color cap R) (Sum.inl x) (Sum.inl (G.move x e)) ≤ 1 := by
    apply (NatMetricClosure.distance_le _ _ _).trans
    simp only [weight]
    split_ifs with h₁ h₂
    · exact Nat.zero_le _
    · exact le_rfl
    · exact False.elim (h₂ ⟨e, rfl⟩)
  exact_mod_cast hn

theorem attachment (x : X) :
    dist (ofVertex G color cap R x) (ofAnchor G color cap R (anchorOf G color cap x)) ≤ R := by
  rw [dist_eq]
  unfold ofVertex ofAnchor
  exact_mod_cast (NatMetricClosure.distance_le (weight G color cap R)
    (Sum.inl x) (Sum.inr (anchorOf G color cap x))).trans_eq (by simp [weight, anchorOf])

theorem originalLabel_step (x : X) (e : D) :
    BoxLabel.distance (originalLabel G color cap x) (originalLabel G color cap (G.move x e)) ≤ 1 := by
  rw [BoxLabel.distance_le_iff]
  intro i
  have h₁ := G.label_step_le color cap i x e
  have h₂ := G.label_step_le color cap i (G.move x e) (G.reverse e)
  rw [G.move_reverse] at h₂
  change Nat.dist (G.label color cap i x) (G.label color cap i (G.move x e)) ≤ 1
  unfold Nat.dist
  omega

omit [Fact (0 < R)] in
theorem label_weight (u v : Point G color cap R) :
    BoxLabel.distance (label G color cap R u) (label G color cap R v) ≤ weight G color cap R u v := by
  by_cases h : u = v
  · subst v; simp
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with he
        · obtain ⟨e, rfl⟩ := he
          exact originalLabel_step G color cap x e
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
      | inr a =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with ha
        · simp [ha]
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with ha
        · simp [ha]
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
      | inr b =>
        simp only [weight, ite_eq_right h, label]
        omega

theorem label_lipschitz : LipschitzWith 1 (label G color cap R) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  simp only [NNReal.coe_one, one_mul]
  exact NatMetricClosure.lipschitz_bound (weight G color cap R) (label G color cap R)
    (fun u v => by rw [BoxLabel.dist_eq]; exact_mod_cast label_weight G color cap R u v) u v

end DiscreteFree.MetricBlock
end

end

end OAI
