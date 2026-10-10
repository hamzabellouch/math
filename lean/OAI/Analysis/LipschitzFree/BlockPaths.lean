import OAI.Analysis.LipschitzFree.MetricBlock

namespace OAI

/-!
# Exact shortest paths through graph and attachment edges
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

inductive SourcePath : ℕ → Point G color cap R → Point G color cap R → Prop
  | nil (u) : SourcePath 0 u u
  | original (x y : X) (h : Adj G x y) :
      SourcePath 1 (ofVertex G color cap R x) (ofVertex G color cap R y)
  | attach (x : X) : SourcePath R (ofVertex G color cap R x)
      (ofAnchor G color cap R (anchorOf G color cap x))
  | detach (x : X) : SourcePath R (ofAnchor G color cap R (anchorOf G color cap x))
      (ofVertex G color cap R x)
  | anchor (a b : Anchor G color cap) (h : a ≠ b) :
      SourcePath (2*R + BoxLabel.distance a.val b.val)
        (ofAnchor G color cap R a) (ofAnchor G color cap R b)
  | trans {i j u v w} : SourcePath i u v → SourcePath j v w → SourcePath (i+j) u w

def SourceBound (n : ℕ) (u v : Point G color cap R) : Prop :=
  ∃ m ≤ n, SourcePath G color cap R m u v

theorem sourceBound_mono {i j : ℕ} {u v : Point G color cap R}
    (hi : SourceBound G color cap R i u v) (hij : i ≤ j) : SourceBound G color cap R j u v := by
  obtain ⟨m,hm,hp⟩ := hi
  exact ⟨m,hm.trans hij,hp⟩

theorem sourceBound_trans {i j : ℕ} {u v w : Point G color cap R}
    (hi : SourceBound G color cap R i u v) (hj : SourceBound G color cap R j v w) :
    SourceBound G color cap R (i+j) u w := by
  obtain ⟨a,ha,hpa⟩ := hi
  obtain ⟨b,hb,hpb⟩ := hj
  exact ⟨a+b,Nat.add_le_add ha hb,SourcePath.trans hpa hpb⟩

theorem sourceBound_anchor (a b : Anchor G color cap) :
    SourceBound G color cap R (2*R+cap) (ofAnchor G color cap R a) (ofAnchor G color cap R b) := by
  by_cases h : a = b
  · subst b
    exact ⟨0,Nat.zero_le _,SourcePath.nil _⟩
  · exact ⟨_,Nat.add_le_add_left (BoxLabel.distance_bound _ _) _,SourcePath.anchor a b h⟩

theorem sourceBound_weight (u v : Point G color cap R) :
    SourceBound G color cap R (weight G color cap R u v) u v := by
  by_cases huv : u = v
  · subst v
    exact ⟨0,by simp,SourcePath.nil _⟩
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      simp only [weight,ite_eq_right huv]
      by_cases h : Adj G x y
      · rw [ite_eq_left h]
        exact ⟨1,le_rfl,SourcePath.original x y h⟩
      · rw [ite_eq_right h]
        have hxa : SourceBound G color cap R R (ofVertex G color cap R x) (ofAnchor G color cap R (anchorOf G color cap x)) :=
          ⟨R,le_rfl,SourcePath.attach x⟩
        have hay : SourceBound G color cap R R (ofAnchor G color cap R (anchorOf G color cap y)) (ofVertex G color cap R y) :=
          ⟨R,le_rfl,SourcePath.detach y⟩
        exact sourceBound_mono G color cap R (sourceBound_trans G color cap R
          (sourceBound_trans G color cap R hxa (sourceBound_anchor G color cap R _ _)) hay) (by omega)
    | inr a =>
      simp only [weight,ite_eq_right huv]
      by_cases h : originalLabel G color cap x = a.val
      · rw [ite_eq_left h]
        have ha : anchorOf G color cap x = a := Subtype.ext h
        refine ⟨R,le_rfl,?_⟩
        change SourcePath G color cap R R (ofVertex G color cap R x) (ofAnchor G color cap R a)
        rw [← ha]
        exact SourcePath.attach x
      · rw [ite_eq_right h]
        have hx : SourceBound G color cap R R (ofVertex G color cap R x) (ofAnchor G color cap R (anchorOf G color cap x)) :=
          ⟨R,le_rfl,SourcePath.attach x⟩
        exact sourceBound_mono G color cap R (sourceBound_trans G color cap R hx
          (sourceBound_anchor G color cap R _ _)) (by omega)
  | inr a =>
    cases v with
    | inl x =>
      simp only [weight,ite_eq_right huv]
      by_cases h : originalLabel G color cap x = a.val
      · rw [ite_eq_left h]
        have ha : anchorOf G color cap x = a := Subtype.ext h
        refine ⟨R,le_rfl,?_⟩
        change SourcePath G color cap R R (ofAnchor G color cap R a) (ofVertex G color cap R x)
        rw [← ha]
        exact SourcePath.detach x
      · rw [ite_eq_right h]
        have hx : SourceBound G color cap R R (ofAnchor G color cap R (anchorOf G color cap x)) (ofVertex G color cap R x) :=
          ⟨R,le_rfl,SourcePath.detach x⟩
        exact sourceBound_mono G color cap R (sourceBound_trans G color cap R
          (sourceBound_anchor G color cap R _ _) hx) (by omega)
    | inr b =>
      simp only [weight,ite_eq_right huv]
      exact ⟨_,le_rfl,SourcePath.anchor a b (fun h => huv (congrArg Sum.inr h))⟩

theorem sourcePath_distance_le [Fact (0 < R)] {n : ℕ} {u v : Point G color cap R}
    (h : SourcePath G color cap R n u v) :
    NatMetricClosure.distance (weight G color cap R) u v ≤ n := by
  induction h with
  | nil u => simp [NatMetricClosure.distance_self,weight_self]
  | original x y h =>
    obtain ⟨e,rfl⟩ := h
    have he := source_edge G color cap R x e
    rw [dist_eq] at he
    exact_mod_cast he
  | attach x =>
    have he := attachment G color cap R x
    rw [dist_eq] at he
    exact_mod_cast he
  | detach x =>
    rw [NatMetricClosure.distance_comm _ (weight_symm G color cap R)]
    have he := attachment G color cap R x
    rw [dist_eq] at he
    exact_mod_cast he
  | anchor a b h =>
    have hw : weight G color cap R (ofAnchor G color cap R a) (ofAnchor G color cap R b) =
        2*R + BoxLabel.distance a.val b.val := by
      apply ite_eq_right
      intro hab
      exact h (Sum.inr.inj hab)
    exact (NatMetricClosure.distance_le _ _ _).trans_eq hw
  | trans hi hj ihi ihj => exact (NatMetricClosure.distance_triangle _ _ _ _).trans (Nat.add_le_add ihi ihj)

theorem source_shortest_path [Fact (0 < R)] (u v : Point G color cap R) :
    SourcePath G color cap R (NatMetricClosure.distance (weight G color cap R) u v) u v := by
  have hb := NatMetricClosure.path_relation (weight G color cap R) (SourceBound G color cap R)
    (sourceBound_weight G color cap R)
    (fun _ _ _ _ _ => sourceBound_trans G color cap R) u v
  obtain ⟨m,hm,hp⟩ := hb
  have he : m = NatMetricClosure.distance (weight G color cap R) u v :=
    Nat.le_antisymm hm (sourcePath_distance_le G color cap R hp)
  simpa only [he] using hp

end DiscreteFree.MetricBlock
end

end

end OAI
