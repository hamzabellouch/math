import OAI.Analysis.LipschitzFree.BlockPaths

namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
theorem near_trans {m n : ℕ} {x y z : X} (hxy : G.Near m x y) (hyz : G.Near n y z) :
    G.Near (m+n) x z := by
  obtain ⟨u, hu, rfl⟩ := hxy
  obtain ⟨v, hv, rfl⟩ := hyz
  exact ⟨u++v, by simpa only [List.length_append] using Nat.add_le_add hu hv, G.walk_append _ _ _⟩
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

def ShortRelation (n : ℕ) : Point G color cap R → Point G color cap R → Prop
  | Sum.inl x, Sum.inl y => G.Near n x y
  | Sum.inr a, Sum.inr b => a = b
  | _, _ => False

omit [Fintype C] in
theorem short_self (n : ℕ) (u : Point G color cap R) : ShortRelation G color cap R n u u := by
  cases u with
  | inl x => exact G.near_self n x
  | inr a => rfl

omit [Fintype C] in
theorem short_trans {m n : ℕ} {u v w : Point G color cap R}
    (huv : ShortRelation G color cap R m u v) (hvw : ShortRelation G color cap R n v w) :
    ShortRelation G color cap R (m+n) u w := by
  cases u <;> cases v <;> cases w <;> simp only [ShortRelation] at *
  · exact G.near_trans huv hvw
  · exact huv.trans hvw

theorem short_edge (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v < R) :
    ShortRelation G color cap R (weight G color cap R u v) u v := by
  by_cases he : u = v
  · subst v
    exact short_self G color cap R _ u
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right he] at h ⊢
        split_ifs at h ⊢ with ha
        · obtain ⟨e, rfl⟩ := ha
          exact ⟨[e], by simp, rfl⟩
        · omega
      | inr a =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
      | inr b =>
        simp only [weight, ite_eq_right he] at h
        omega

theorem short_distance (hR : 0 < R) (u v : Point G color cap R)
    (h : NatMetricClosure.distance (weight G color cap R) u v < R) :
    ShortRelation G color cap R (NatMetricClosure.distance (weight G color cap R) u v) u v := by
  have hp := NatMetricClosure.path_relation (weight G color cap R)
    (fun n x y => n < R → ShortRelation G color cap R n x y)
    (fun x y => short_edge G color cap R hR x y)
    (by
      intro a b x y z hxy hyz hab
      exact short_trans G color cap R (hxy (by omega)) (hyz (by omega))) u v
  exact hp h

omit [Fintype C] in
theorem short_mono {m n : ℕ} (hmn : m ≤ n) {u v : Point G color cap R}
    (h : ShortRelation G color cap R m u v) : ShortRelation G color cap R n u v := by
  cases u <;> cases v <;> simp only [ShortRelation] at *
  · exact G.near_mono hmn h
  · exact h

variable [Fintype D]

omit [Fintype C] in
theorem short_finite (n : ℕ) (u : Point G color cap R) :
    {v | ShortRelation G color cap R n u v}.Finite := by
  cases u with
  | inl x =>
    apply ((G.near_finite n x).image (Sum.inl : X → Point G color cap R)).subset
    rintro (y|a) hy
    · exact ⟨y, hy, rfl⟩
    · exact False.elim hy
  | inr a =>
    apply (Set.finite_singleton (Sum.inr a : Point G color cap R)).subset
    rintro (x|b) hb
    · exact False.elim hb
    · exact Set.mem_singleton_iff.mpr (congrArg Sum.inr hb.symm)

omit [Fintype C] in
theorem short_card_le (n : ℕ) (u : Point G color cap R) :
    Nat.card {v : Point G color cap R // ShortRelation G color cap R n u v} ≤
      Fintype.card (BoundedWords D n) := by
  cases u with
  | inl x =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inl x) v} :=
      fun w => ⟨Sum.inl (G.walk x w.val), w.val, w.property, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(_|a), h⟩
      · obtain ⟨w, hw, rfl⟩ := h
        exact ⟨⟨w, hw⟩, rfl⟩
      · exact False.elim h
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf
  | inr a =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inr a) v} :=
      fun _ => ⟨Sum.inr a, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(x|b), h⟩
      · exact False.elim h
      · change a = b at h
        subst b
        exact ⟨⟨[], by simp⟩, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf

variable [Fact (0 < R)]

theorem closedBall_finite (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    (Metric.closedBall u (n : ℝ)).Finite := by
  apply (short_finite G color cap R n u).subset
  intro v hv
  have hv' : NatMetricClosure.distance (weight G color cap R) u v ≤ n := by
    have hv' := Metric.mem_closedBall.mp hv
    rw [dist_comm, dist_eq] at hv'
    exact_mod_cast hv'
  exact short_mono G color cap R hv' (short_distance G color cap R Fact.out u v (hv'.trans_lt hn))

theorem closedBall_card_le (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    Nat.card (Metric.closedBall u (n : ℝ)) ≤ Fintype.card (BoundedWords D n) := by
  let f : Metric.closedBall u (n : ℝ) → {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    fun v => ⟨v.val, by
      have hv : NatMetricClosure.distance (weight G color cap R) u v.val ≤ n := by
        have hv' := Metric.mem_closedBall.mp v.property
        rw [dist_comm, dist_eq] at hv'
        exact_mod_cast hv'
      exact short_mono G color cap R hv (short_distance G color cap R Fact.out u v.val (hv.trans_lt hn))⟩
  have : Finite {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    (short_finite G color cap R n u).to_subtype
  exact (Nat.card_le_card_of_injective f (by intro v w h; exact Subtype.ext (congrArg (fun z => z.val) h))).trans
    (short_card_le G color cap R n u)

omit [Fact (0 < R)] [Fintype C] [Fintype D] in

theorem label_occurs (u : Point G color cap R) :
    ∃ x, label G color cap R u = originalLabel G color cap x := by
  cases u with
  | inl x => exact ⟨x, rfl⟩
  | inr a => exact a.property.imp (fun _ h => h.symm)

omit [Fact (0 < R)] in
theorem label_support_card (u : Point G color cap R) :
    Nat.card {i : C // (label G color cap R u i).val < cap} ≤
      Fintype.card (BoundedWords D cap) := by
  obtain ⟨x, hx⟩ := label_occurs G color cap R u
  rw [hx]
  exact G.label_support_le color cap x

omit [Fact (0 < R)] [Fintype D] in

theorem color_in_support (x : X) (u : Point G color cap R)
    (h : dist (originalLabel G color cap x) (label G color cap R u) < cap) :
    (label G color cap R u (color x)).val < cap := by
  have hc := BoxLabel.real_coord_le (originalLabel G color cap x) (label G color cap R u) (color x)
  simp only [originalLabel, G.label_own_color, Nat.cast_zero, zero_sub, abs_neg,
    Nat.abs_cast] at hc
  exact_mod_cast hc.trans_lt h

end MetricBlock
end DiscreteFree
end

end

end OAI
