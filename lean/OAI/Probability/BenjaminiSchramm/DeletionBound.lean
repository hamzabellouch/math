import OAI.Probability.BenjaminiSchramm.SusceptibilityDerivative
import OAI.Probability.UnimodularPercolation.Deformation.ClusterProducts

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem connection_or_first_deleted_vertex (G : BondGraph V E) (D : Set V)
    (ω : Set E) (x y : V) (hc : Conn G ω x y) :
    (x ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y) ∨
      ∃ z ∉ D, ω ∈ DisjointOccurrence {η | Conn G η x z} {η | Conn G η z y} := by
  obtain ⟨p₀⟩ := (conn_iff_reachable G ω x y).mp hc
  let p := p₀.toPath.val
  by_cases h : ∀ z ∈ p.support, z ∈ D
  · exact Or.inl ⟨h x p.start_mem_support,walk_conn_restrict_vertices G ω p D h⟩
  · push Not at h
    obtain ⟨z,hz,hzD⟩ := h
    exact Or.inr ⟨z,hzD,simplePath_disjoint_at G ω p p₀.toPath.property hz⟩

theorem first_hit_deletion_probability [Countable V] [Countable E]
    (G : BondGraph V E) (D : Set V) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} ≤
      (if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
      ∑' z, if z ∈ D then 0 else
        law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y} := by
  let B : Set (Set E) := {ω | x ∈ D ∧ Conn G (ω ∩ internalEdges G D) x y}
  let C (z : V) : Set (Set E) := if z ∈ D then ∅ else
    DisjointOccurrence {ω | Conn G ω x z} {ω | Conn G ω z y}
  have hc : {ω | Conn G ω x y} ⊆ B ∪ ⋃ z, C z := by
    intro ω hω
    rcases connection_or_first_deleted_vertex G D ω x y hω with hb | ⟨z,hz,hzω⟩
    · exact Or.inl hb
    · exact Or.inr (Set.mem_iUnion.mpr ⟨z,by simpa only [C,ite_eq_right hz] using hzω⟩)
  have hB : law p B = if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0 := by
    by_cases hx : x ∈ D <;> simp [B,hx]
  have hC (z : V) : law p (C z) ≤ if z ∈ D then 0 else
      law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y} := by
    by_cases hz : z ∈ D
    · simp only [C,ite_eq_left hz,measure_empty,le_refl]
    · simp only [C,ite_eq_right hz]
      exact bk_ennreal p _ _
        (fun _ _ h hconn => conn_mono G h hconn)
        (fun _ _ h hconn => conn_mono G h hconn)
        (finiteWitness_conn G x z) (finiteWitness_conn G z y)
  calc
    _ ≤ law p B + law p (⋃ z, C z) := (measure_mono hc).trans (measure_union_le _ _)
    _ ≤ law p B + ∑' z, law p (C z) := add_le_add_right (measure_iUnion_le C) _
    _ ≤ _ := by rw [hB]; exact add_le_add_right (ENNReal.tsum_le_tsum hC) _

theorem ennreal_inducedSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (x : V) :
    ENNReal.ofReal (inducedSusceptibility G D p x) =
      ∑' y, if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0 := by
  by_cases hx : x ∈ D
  · simp only [inducedSusceptibility,ite_eq_left hx,restrictedSusceptibility]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg)
      (summable_restrictedTwoPoint G hloc hqt p hp _ x)]
    exact tsum_congr (fun _ => ENNReal.ofReal_toReal (measure_ne_top _ _))
  · simp only [inducedSusceptibility,ite_eq_right hx,ENNReal.ofReal_zero,tsum_zero]

theorem susceptibility_deletion_ennreal [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x : V) :
    ENNReal.ofReal (susceptibility G p x) ≤
      ENNReal.ofReal (inducedSusceptibility G D p x) +
        (∑' z, if z ∈ D then 0 else law p {ω | Conn G ω x z}) * C := by
  rw [ennreal_susceptibility G hloc hqt p hp x,
    ennreal_inducedSusceptibility G hloc hqt p hp D x]
  calc
    _ ≤ ∑' y, ((if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
        ∑' z, if z ∈ D then 0 else law p {ω | Conn G ω x z} * law p {ω | Conn G ω z y}) :=
      ENNReal.tsum_le_tsum (first_hit_deletion_probability G D p x)
    _ = (∑' y, if x ∈ D then law p {ω | Conn G (ω ∩ internalEdges G D) x y} else 0) +
        ∑' z, (if z ∈ D then 0 else law p {ω | Conn G ω x z}) *
          (∑' y, law p {ω | Conn G ω z y}) := by
      rw [ENNReal.tsum_add,ENNReal.tsum_comm]
      congr 1
      apply tsum_congr
      intro z
      by_cases hz : z ∈ D
      · simp only [ite_eq_left hz,tsum_zero,zero_mul]
      · simp only [ite_eq_right hz,ENNReal.tsum_mul_left]
    _ ≤ _ := by
      apply add_le_add_right
      rw [←ENNReal.tsum_mul_right]
      apply ENNReal.tsum_le_tsum
      intro z
      rw [←ennreal_susceptibility G hloc hqt p hp z]
      exact mul_le_mul' le_rfl (hC z)

end Percolation.BenjaminiSchramm

end OAI
