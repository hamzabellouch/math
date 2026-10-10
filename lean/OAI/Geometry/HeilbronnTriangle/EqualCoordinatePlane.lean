import OAI.Geometry.HeilbronnTriangle.PlaneFunctional

namespace OAI


noncomputable section

namespace Problem355.PlaneFunctional

variable {ι K : Type*} [Fintype ι] [Field K]

def coordinateDifference (i j : ι) : ι → K := by
  classical
  exact Pi.single i 1 - Pi.single j 1

@[simp] theorem coordinateDifference_dot (i j : ι) (v : ι → K) :
    dotProduct (coordinateDifference i j) v = v i - v j := by
  classical
  simp only [coordinateDifference, sub_dotProduct, single_dotProduct, one_mul]

omit [Fintype ι] in
theorem coordinateDifference_ne_zero {i j : ι} (hij : i ≠ j) :
    (coordinateDifference i j : ι → K) ≠ 0 := by
  classical
  intro h
  have hi := congrFun h i
  simp [coordinateDifference, hij] at hi

omit [Fintype ι] in

theorem not_exists_smul_swap (x d : ι → K) (hd : d ≠ 0)
    (hx : ¬ ∃ a : K, x = a • d) : ¬ ∃ a : K, d = a • x := by
  rintro ⟨a, ha⟩
  have hapos : a ≠ 0 := by
    intro hz
    apply hd
    simpa [hz] using ha
  apply hx
  refine ⟨a⁻¹, ?_⟩
  rw [ha, smul_smul, inv_mul_cancel₀ hapos, one_smul]

def equalCoordinateSubgroup (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ)) (i j : ι) :
    AddSubgroup L :=
  ((modularDotHom q (coordinateDifference i j)).comp L.subtype).ker

@[simp] theorem mem_equalCoordinateSubgroup (q : ℕ) [Fact q.Prime] (L : AddSubgroup (ι → ℤ))
    (i j : ι) (v : L) :
    v ∈ equalCoordinateSubgroup q L i j ↔
      (((v : ι → ℤ) i : ℤ) : ZMod q) = (((v : ι → ℤ) j : ℤ) : ZMod q) := by
  change dotProduct (coordinateDifference i j)
    (fun a => (((v : ι → ℤ) a : ℤ) : ZMod q)) = 0 ↔ _
  rw [coordinateDifference_dot, sub_eq_zero]

theorem equalCoordinateSubgroup_index (q : ℕ) [Fact q.Prime]
    (x : ι → ZMod q) (hx : x ≠ 0) (i j : ι) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, x = a • coordinateDifference i j)
    (L : AddSubgroup (ι → ℤ))
    (hL : ∀ v : ι → ZMod q, dotProduct x v = 0 →
      ∃ w : L, ∀ a, ((w : ι → ℤ) a : ZMod q) = v a) :
    (equalCoordinateSubgroup q L i j).index = q := by
  exact modular_equation_index q x (coordinateDifference i j) hx
    (not_exists_smul_swap x (coordinateDifference i j)
      (coordinateDifference_ne_zero hij) hspan) L hL

end Problem355.PlaneFunctional

end

end OAI
