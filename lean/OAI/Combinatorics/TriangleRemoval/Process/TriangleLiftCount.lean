import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RootedTemplates
import OAI.Combinatorics.TriangleRemoval.Process.CopyEdgeLoad

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def triangleLiftCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : ℝ :=
  ∑ a, intact (required a) G * ∑ e ∈ required a, (triangleDegree G e : ℝ)

theorem copyCount_triangleLift_drift {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (b : ℕ)
    (hsize : ∀ a, (required a).card ≤ b) (hG : (triangles G).Nonempty) :
    0 ≤ pmfMean (step G) (copyCount required) - copyCount required G +
      triangleLiftCount required G/(triangles G).card ∧
    pmfMean (step G) (copyCount required) - copyCount required G +
      triangleLiftCount required G/(triangles G).card ≤
        (b : ℝ)^2/(triangles G).card * copyCount required G := by
  classical
  let loss (a : α) : ℝ :=
    if required a ⊆ G then ((hittingTriangles G (required a)).card : ℝ) else 0
  have ha (a : α) :
      0 ≤ intact (required a) G * ∑ e ∈ required a, (triangleDegree G e : ℝ) - loss a ∧
      intact (required a) G * ∑ e ∈ required a, (triangleDegree G e : ℝ) - loss a ≤
        (b : ℝ)^2*intact (required a) G := by
    by_cases hpres : required a ⊆ G
    · simp only [intact,ite_eq_left hpres,one_mul,loss,mul_one]
      have hl : ((hittingTriangles G (required a)).card : ℝ) ≤
          ∑ e ∈ required a, (triangleDegree G e : ℝ) := by
        exact_mod_cast hittingTriangles_card_le_degree_sum G (required a)
      have hu : (∑ e ∈ required a, (triangleDegree G e : ℝ)) ≤
          ((hittingTriangles G (required a)).card : ℝ)+(b : ℝ)^2 := by
        have hh := degree_sum_le_hittingTriangles_add G (required a)
        have hb : (required a).card^2 ≤ b^2 := Nat.pow_le_pow_left (hsize a) 2
        exact_mod_cast hh.trans (Nat.add_le_add_left hb _)
      constructor <;> linarith
    · simp only [intact,ite_eq_right hpres,loss,zero_mul,mul_zero,sub_self,le_refl,and_self]
  have hsumlo : 0 ≤ triangleLiftCount required G-∑ a, loss a := by
    rw [triangleLiftCount,← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun a _ => (ha a).1)
  have hsumhi : triangleLiftCount required G-∑ a, loss a ≤
      (b : ℝ)^2*copyCount required G := by
    rw [triangleLiftCount,← Finset.sum_sub_distrib,copyCount,Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (ha a).2)
  have hQ : (0 : ℝ) < (triangles G).card := Nat.cast_pos.mpr hG.card_pos
  have hid : pmfMean (step G) (copyCount required)-copyCount required G+
      triangleLiftCount required G/(triangles G).card =
      (triangleLiftCount required G-∑ a, loss a)/(triangles G).card := by
    rw [step_mean_copyCount required G hG]
    change copyCount required G-(∑ a, loss a)/_ -copyCount required G+_ = _
    ring
  rw [hid]
  refine ⟨div_nonneg hsumlo hQ.le,?_⟩
  exact (div_le_div_of_nonneg_right hsumhi hQ.le).trans_eq (by ring)

abbrev TriangleLiftIndex {n : ℕ} {α : Type*} (required : α → Graph n) :=
  {p : α × (Finset (Fin n) × Finset (Fin n)) //
    p.2.1 ∈ required p.1 ∧ p.2.2.card = 3 ∧ p.2.1 ∈ p.2.2.powersetCard 2}

def triangleLiftRequired {n : ℕ} {α : Type*} (required : α → Graph n)
    (a : TriangleLiftIndex required) : Graph n :=
  required a.val.1 ∪ a.val.2.2.powersetCard 2

lemma intact_union {n : ℕ} (F E G : Graph n) :
    intact (F ∪ E) G = intact F G * intact E G := by
  classical
  unfold intact
  by_cases hF : F ⊆ G <;> by_cases hE : E ⊆ G <;>
    simp [hF,hE,Finset.union_subset_iff]

lemma triangleDegree_eq_intact_sum {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    (triangleDegree G e : ℝ) =
      ∑ t : Finset (Fin n), if t.card = 3 ∧ e ∈ t.powersetCard 2 then
        intact (t.powersetCard 2) G else 0 := by
  classical
  have ht : (triangleDegree G e : ℝ) =
      ∑ t : Finset (Fin n), if t ∈ incidentTriangles G e then (1 : ℝ) else 0 := by
    simp [triangleDegree]
  rw [ht]
  apply Finset.sum_congr rfl
  intro t _
  simp only [incidentTriangles,Finset.mem_filter,mem_triangles,intact]
  by_cases hc : t.card = 3 <;> by_cases he : e ∈ t.powersetCard 2 <;>
    by_cases hG : t.powersetCard 2 ⊆ G <;> simp [hc,he,hG]

theorem triangleLiftCount_eq_copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) :
    triangleLiftCount required G = copyCount (triangleLiftRequired required) G := by
  classical
  let pred (p : α × (Finset (Fin n) × Finset (Fin n))) : Prop :=
    p.2.1 ∈ required p.1 ∧ p.2.2.card = 3 ∧ p.2.1 ∈ p.2.2.powersetCard 2
  have hh := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter pred)
    (by intro p; simp : ∀ p, p ∈ Finset.univ.filter pred ↔ pred p)
    (fun p => intact (required p.1 ∪ p.2.2.powersetCard 2) G)
  change triangleLiftCount required G =
    ∑ a : {p // pred p}, intact (required a.val.1 ∪ a.val.2.2.powersetCard 2) G
  rw [← hh,Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  unfold triangleLiftCount
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  calc
    _ = ∑ e : Finset (Fin n), if e ∈ required a then
        intact (required a) G * (triangleDegree G e : ℝ) else 0 := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ required a
      · simp only [ite_eq_left he,triangleDegree_eq_intact_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        simp only [he,true_and,intact_union,mul_ite,mul_zero]
      · simp only [he,false_and,ite_false,Finset.sum_const_zero]

lemma triangleLiftRequired_card_le {n : ℕ} {α : Type*}
    (required : α → Graph n) (a : TriangleLiftIndex required) :
    (triangleLiftRequired required a).card ≤ (required a.val.1).card + 2 := by
  classical
  have htri : (a.val.2.2.powersetCard 2).card = 3 := by
    rw [Finset.card_powersetCard,a.property.2.1]
    decide
  have hmeet : 1 ≤ ((required a.val.1) ∩ a.val.2.2.powersetCard 2).card := by
    apply Nat.succ_le_iff.mpr
    apply Finset.card_pos.mpr
    exact ⟨a.val.2.1,Finset.mem_inter.mpr ⟨a.property.1,a.property.2.2⟩⟩
  have he := Finset.card_union_add_card_inter (required a.val.1) (a.val.2.2.powersetCard 2)
  unfold triangleLiftRequired
  omega

lemma copyEdgeLoad_eq_subfamily {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (e : Finset (Fin n)) :
    copyEdgeLoad required G e =
      copyCount (fun a : {a // e ∈ required a} => required a.val) G := by
  classical
  rw [copyEdgeLoad,copyCount]
  have hh := Finset.sum_subtype (F := inferInstance)
    (Finset.univ.filter (fun a => e ∈ required a))
    (by intro a; simp : ∀ a, a ∈ Finset.univ.filter (fun a => e ∈ required a) ↔
      e ∈ required a) (fun a => intact (required a) G)
  rw [← hh,Finset.sum_filter]

theorem copyCount_triangleLift_drift_all {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (b : ℕ)
    (hsize : ∀ a, (required a).card ≤ b) :
    0 ≤ pmfMean (step G) (copyCount required) - copyCount required G +
      triangleLiftCount required G/(triangles G).card ∧
    pmfMean (step G) (copyCount required) - copyCount required G +
      triangleLiftCount required G/(triangles G).card ≤
        (b : ℝ)^2/(triangles G).card * copyCount required G := by
  by_cases hG : (triangles G).Nonempty
  · exact copyCount_triangleLift_drift required G b hsize hG
  · have hG0 : triangles G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
    simp only [step_absorbing hG0,pmfMean_pure,sub_self,hG0,Finset.card_empty,
      Nat.cast_zero,div_zero,zero_mul,add_zero,le_refl,and_self]

lemma rootedCount_triangleLift_drift {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) :
    0 ≤ pmfMean (step G) (rootedCount T ψ) - rootedCount T ψ G +
      triangleLiftCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) G /
        (triangles G).card ∧
    pmfMean (step G) (rootedCount T ψ) - rootedCount T ψ G +
      triangleLiftCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) G /
        (triangles G).card ≤
      (T.edges.card : ℝ)^2/(triangles G).card * rootedCount T ψ G := by
  exact copyCount_triangleLift_drift_all
    (fun φ : RootedInjection T ψ => imageEdges T φ.val) G T.edges.card
    (fun φ => (imageEdges_card T φ.val).le)

end SharpTerminalLeave

end

end OAI
