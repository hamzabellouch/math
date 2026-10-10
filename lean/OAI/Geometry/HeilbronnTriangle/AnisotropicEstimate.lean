import OAI.Geometry.HeilbronnTriangle.AnisotropicCount
import OAI.Geometry.HeilbronnTriangle.FixedDetReduction

namespace OAI


noncomputable section

namespace Problem355.FixedDetReduction

open scoped BigOperators Matrix

def anisotropicConstant : ℝ := 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2

lemma anisotropicConstant_pos : 0 < anisotropicConstant :=
  Anisotropic.anisotropic_constant_pos

theorem anisotropicEstimate : AnisotropicEstimate anisotropicConstant := by
  classical
  intro r u T hr hr₂ hu hT
  let columns : Matrix (Fin 3) (Fin 3) ℤ → Anisotropic.Triple :=
    fun Q => (fun i => Q i 0, fun i => Q i 1, fun i => Q i 2)
  have hinj : Function.Injective columns := by
    intro Q Q' h
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg (fun x : Anisotropic.Triple => x.2.1) h
    have h₂ := congrArg (fun x : Anisotropic.Triple => x.2.2) h
    ext i j
    fin_cases j
    · exact congrFun h₀ i
    · exact congrFun h₁ i
    · exact congrFun h₂ i
  have hdet : ∀ x ∈ T.image columns,
      x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = u := by
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    have hd := (hT Q hQ).1
    convert hd using 1
    simp [columns, Matrix.det_fin_three, dotProduct, Fin.sum_univ_succ,
      cross_apply]
    ring
  have hnorm : ∀ x ∈ T.image columns,
      Anisotropic.length x.1 ≤ r 0 ∧ Anisotropic.length x.2.1 ≤ r 1 ∧
        Anisotropic.length x.2.2 ≤ r 2 := by
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(hT Q hQ).2 0, (hT Q hQ).2 1, (hT Q hQ).2 2⟩
  have h := Anisotropic.anisotropic_count (T.image columns) u hu
    (r 0) (r 1) (r 2) hr₂ (hr (by decide)) (hr (by decide)) hdet hnorm
  rw [Finset.card_image_of_injective T hinj] at h
  simpa [anisotropicConstant, Fin.prod_univ_succ, mul_assoc] using h

end Problem355.FixedDetReduction

end

end OAI
