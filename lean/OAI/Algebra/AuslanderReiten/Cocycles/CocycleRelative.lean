import OAI.Algebra.AuslanderReiten.Cocycles.CocycleCorners

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def vertexSpace : Submodule k (T k q) :=
  Submodule.span k (Set.range fun v : Bool => T.vector q (TIndex.vertex v))

private theorem vertexSpace_induction {P : T k q → Prop}
    (hvertex : ∀ v, P (T.vector q (TIndex.vertex v))) (hzero : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (r : k) a, P a → P (r • a))
    {a : T k q} (ha : a ∈ vertexSpace q) : P a := by
  apply Submodule.span_induction (p := fun a _ => P a) _ _ _ _ ha
  · rintro _ ⟨v, rfl⟩
    exact hvertex v
  · exact hzero
  · intro a b _ _ ha hb
    exact hadd a b ha hb
  · intro r a _ ha
    exact hsmul r a ha

theorem p_normalized_first_relative {v : T k q} (hv : v ∈ vertexSpace q) (b c : T k q) :
    p q v b c = 0 := by
  apply vertexSpace_induction q (fun v => p_normalized_first q v b c) _ _ _ hv
  · simp
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    simp [ha]

theorem p_normalized_second_relative {v : T k q} (hv : v ∈ vertexSpace q) (a c : T k q) :
    p q a v c = 0 := by
  apply vertexSpace_induction q (fun v => p_normalized_second q v a c) _ _ _ hv
  · simp
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    simp [ha]

theorem p_normalized_third_relative {v : T k q} (hv : v ∈ vertexSpace q) (a b : T k q) :
    p q a b v = 0 := by
  apply vertexSpace_induction q (fun v => p_normalized_third q v a b) _ _ _ hv
  · simp
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    simp [ha]

theorem p_balanced_first_relative {v : T k q} (hv : v ∈ vertexSpace q) (a b c : T k q) :
    p q (a * v) b c = p q a (v * b) c := by
  apply vertexSpace_induction q (fun v => p_balanced_first q a b c v) _ _ _ hv
  · simp
  · intro v w hv hw
    simp [mul_add, add_mul, hv, hw]
  · intro r v hv
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hv]

theorem p_balanced_second_relative {v : T k q} (hv : v ∈ vertexSpace q) (a b c : T k q) :
    p q a (b * v) c = p q a b (v * c) := by
  apply vertexSpace_induction q (fun v => p_balanced_second q a b c v) _ _ _ hv
  · simp
  · intro v w hv hw
    simp [mul_add, add_mul, hv, hw]
  · intro r v hv
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hv]

theorem p_left_relative {v : T k q} (hv : v ∈ vertexSpace q) (a b c : T k q) :
    v * p q a b c = p q (v * a) b c := by
  apply vertexSpace_induction q (fun v => p_left_vertex q a b c v) _ _ _ hv
  · simp
  · intro v w hv hw
    simp [add_mul, hv, hw]
  · intro r v hv
    simp [Algebra.smul_mul_assoc, hv]

theorem p_right_relative {v : T k q} (hv : v ∈ vertexSpace q) (a b c : T k q) :
    p q a b c * v = p q a b (c * v) := by
  apply vertexSpace_induction q (fun v => p_right_vertex q a b c v) _ _ _ hv
  · simp
  · intro v w hv hw
    simp [mul_add, hv, hw]
  · intro r v hv
    simp [Algebra.mul_smul_comm, hv]

end ArExplicit.CocycleData

end

end OAI
