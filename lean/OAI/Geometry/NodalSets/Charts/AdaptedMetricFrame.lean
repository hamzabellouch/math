import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem positive_form_adapted_basis (g : LinearMap.BilinForm ℝ V)
    (hpos : ∀ v : V, v ≠ 0 → 0 < g v v) (hsym : ∀ u v, g u v = g v u)
    (hdim : Module.finrank ℝ V = 4) (p q : V) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hpp : g p p = a^2) (hqq : g q q = b^2)
    (hpq : g p q = 0) :
    ∃ e : Module.Basis (Fin 4) ℝ V,
      e 0 = a⁻¹ • p ∧ e 1 = b⁻¹ • q ∧
      ∀ i j, g (e i) (e j) = if i = j then 1 else 0 := by
  classical
  let core : InnerProductSpace.Core ℝ V :=
    { inner := fun u v ↦ g u v
      conj_inner_symm := fun u v ↦ hsym v u
      re_inner_nonneg := fun v ↦ by
        by_cases hv : v = 0
        · simp [hv]
        · exact (hpos v hv).le
      add_left := fun u v w ↦ by simp
      smul_left := fun u v r ↦ by simp
      definite := fun v hv ↦ by
        by_contra hn
        exact (ne_of_gt (hpos v hn)) hv }
  let : NormedAddCommGroup V := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ V)
  let v : Fin 4 → V := ![a⁻¹ • p, b⁻¹ • q, 0, 0]
  let s : Set (Fin 4) := {0,1}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    change g (v i) (v j) = if (⟨i,hi⟩ : s) = ⟨j,hj⟩ then 1 else 0
    have hqp : g q p = 0 := by rw [hsym q p, hpq]
    change i = 0 ∨ i = 1 at hi
    change j = 0 ∨ j = 1 at hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [v, hpp, hqq, hpq, hqp, smul_eq_mul]
    all_goals try (intro hh; have hval := congrArg Subtype.val hh; norm_num at hval)
    all_goals field_simp [ne_of_gt ha, ne_of_gt hb]
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  refine ⟨e.toBasis, he 0 (by simp [s]), he 1 (by simp [s]), ?_⟩
  intro i j
  exact (orthonormal_iff_ite.mp e.orthonormal) i j

end
end Yau.Geometry

end OAI
