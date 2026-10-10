import OAI.Algebra.AuslanderReiten.Cocycles.SparseCocycle

namespace OAI

noncomputable section

namespace ArExplicit
namespace TIndex

def lowerSource : Letter → Bool
  | .e | .x | .y | .z | .u | .v => false
  | .t | .j | .f | .n => true

def lowerTarget : Letter → Bool
  | .e | .x | .y | .z | .t | .j => false
  | .u | .v | .f | .n => true

def source (i : TIndex) : Bool := if i.1 then lowerTarget i.2 else lowerSource i.2
def target (i : TIndex) : Bool := if i.1 then lowerSource i.2 else lowerTarget i.2

def vertex (b : Bool) : TIndex := (false, if b then .f else .e)

def weight (i : TIndex) : ℕ := if i.1 then 1 else 0

end TIndex

namespace CocycleData

theorem cochain_data_properties : cochain.all (fun p => decide (
    (∀ b : Bool, p.first ≠ TIndex.vertex b ∧ p.second ≠ TIndex.vertex b ∧ p.third ≠ TIndex.vertex b) ∧
    p.first.target = p.second.source ∧ p.second.target = p.third.source ∧
    p.first.source = p.output.source ∧ p.third.target = p.output.target ∧
    p.first.weight + p.second.weight + p.third.weight = p.output.weight + 1)) = true := by
  decide +kernel

theorem cochain_term_properties (t : TripleMonomial) (ht : t ∈ cochain) :
    (∀ b : Bool, t.first ≠ TIndex.vertex b ∧ t.second ≠ TIndex.vertex b ∧ t.third ≠ TIndex.vertex b) ∧
    t.first.target = t.second.source ∧ t.second.target = t.third.source ∧
    t.first.source = t.output.source ∧ t.third.target = t.output.target ∧
    t.first.weight + t.second.weight + t.third.weight = t.output.weight + 1 := by
  exact of_decide_eq_true ((List.all_eq_true.mp cochain_data_properties) t ht)

variable {k : Type*} [Field k] (q : k)

theorem coefficient_mul_vertex (a : T k q) (i : TIndex) (v : Bool) :
    T.coefficient q i (a * T.vector q (TIndex.vertex v)) =
      if i.target = v then T.coefficient q i a else 0 := by
  obtain ⟨b, i⟩ := i
  cases v <;> cases b <;> cases i <;>
    simp [TIndex.vertex, TIndex.target, TIndex.lowerSource, TIndex.lowerTarget,
      T.vector, T.lower, TrivialExtension.inl, T.coefficient,
      BaseAlgebra.product, BaseAlgebra.basis_mul, BaseAlgebra.multiplicationTable]

theorem coefficient_vertex_mul (a : T k q) (i : TIndex) (v : Bool) :
    T.coefficient q i (T.vector q (TIndex.vertex v) * a) =
      if i.source = v then T.coefficient q i a else 0 := by
  obtain ⟨b, i⟩ := i
  cases v <;> cases b <;> cases i <;>
    simp [TIndex.vertex, TIndex.source, TIndex.lowerSource, TIndex.lowerTarget,
      T.vector, T.lower, TrivialExtension.inl, T.coefficient,
      BaseAlgebra.product, BaseAlgebra.basis_mul, BaseAlgebra.multiplicationTable]

theorem p_normalized_first (v : Bool) (b c : T k q) :
    p q (T.vector q (TIndex.vertex v)) b c = 0 := by
  rw [p_apply]
  have hh : cochain.map (evalTriple q (T.vector q (TIndex.vertex v)) b c) = cochain.map (fun _ => 0) := by
    apply List.map_congr_left
    intro t ht
    have hn := (cochain_term_properties t ht).1 v
    simp [evalTriple, hn.1]
  rw [hh]
  simp

theorem p_normalized_second (v : Bool) (a c : T k q) :
    p q a (T.vector q (TIndex.vertex v)) c = 0 := by
  rw [p_apply]
  have hh : cochain.map (evalTriple q a (T.vector q (TIndex.vertex v)) c) = cochain.map (fun _ => 0) := by
    apply List.map_congr_left
    intro t ht
    have hn := (cochain_term_properties t ht).1 v
    simp [evalTriple, hn.2.1]
  rw [hh]
  simp

theorem p_normalized_third (v : Bool) (a b : T k q) :
    p q a b (T.vector q (TIndex.vertex v)) = 0 := by
  rw [p_apply]
  have hh : cochain.map (evalTriple q a b (T.vector q (TIndex.vertex v))) = cochain.map (fun _ => 0) := by
    apply List.map_congr_left
    intro t ht
    have hn := (cochain_term_properties t ht).1 v
    simp [evalTriple, hn.2.2]
  rw [hh]
  simp

theorem p_balanced_first (a b c : T k q) (v : Bool) :
    p q (a * T.vector q (TIndex.vertex v)) b c =
      p q a (T.vector q (TIndex.vertex v) * b) c := by
  simp only [p_apply]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hc := (cochain_term_properties t ht).2.1
  simp only [evalTriple, coefficient_mul_vertex, coefficient_vertex_mul, hc]
  split_ifs <;> simp

theorem p_balanced_second (a b c : T k q) (v : Bool) :
    p q a (b * T.vector q (TIndex.vertex v)) c =
      p q a b (T.vector q (TIndex.vertex v) * c) := by
  simp only [p_apply]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hc := (cochain_term_properties t ht).2.2.1
  simp only [evalTriple, coefficient_mul_vertex, coefficient_vertex_mul, hc]
  split_ifs <;> simp

theorem vertex_mul_vector (i : TIndex) (v : Bool) :
    T.vector q (TIndex.vertex v) * T.vector q i =
      if i.source = v then T.vector q i else 0 := by
  apply T.coordinate_ext q
  intro j
  rw [coefficient_vertex_mul]
  by_cases hj : j = i <;> by_cases hv : i.source = v <;> simp_all

theorem vector_mul_vertex (i : TIndex) (v : Bool) :
    T.vector q i * T.vector q (TIndex.vertex v) =
      if i.target = v then T.vector q i else 0 := by
  apply T.coordinate_ext q
  intro j
  rw [coefficient_mul_vertex]
  by_cases hj : j = i <;> by_cases hv : i.target = v <;> simp_all

theorem p_left_vertex (a b c : T k q) (v : Bool) :
    T.vector q (TIndex.vertex v) * p q a b c =
      p q (T.vector q (TIndex.vertex v) * a) b c := by
  rw [p_apply, p_apply]
  change (LinearMap.mulLeft k (T.vector q (TIndex.vertex v))) _ = _
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hc := (cochain_term_properties t ht).2.2.2.1
  change T.vector q (TIndex.vertex v) * evalTriple q a b c t = _
  simp only [evalTriple, Algebra.mul_smul_comm, vertex_mul_vector, coefficient_vertex_mul, hc]
  split_ifs <;> simp

theorem p_right_vertex (a b c : T k q) (v : Bool) :
    p q a b c * T.vector q (TIndex.vertex v) =
      p q a b (c * T.vector q (TIndex.vertex v)) := by
  rw [p_apply, p_apply]
  change (LinearMap.mulRight k (T.vector q (TIndex.vertex v))) _ = _
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hc := (cochain_term_properties t ht).2.2.2.2.1
  change evalTriple q a b c t * T.vector q (TIndex.vertex v) = _
  simp only [evalTriple, Algebra.smul_mul_assoc, vector_mul_vertex, coefficient_mul_vertex, hc]
  split_ifs <;> simp

end CocycleData
end ArExplicit

end

end OAI
