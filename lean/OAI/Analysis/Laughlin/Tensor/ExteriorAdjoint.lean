import OAI.Analysis.Laughlin.Tensor.FockEnergy

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def normalizedTensorReadout (n Q : ℕ) (x : Space Q) : State n Q :=
  fun a => ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * occupationInner Q (orderedWedge a) x

theorem orderedWedge_swap {n Q : ℕ} (a : Configuration n Q) (i j : Fin n) (hij : i≠j) :
    orderedWedge (a ∘ Equiv.swap i j) = -orderedWedge a := by
  exact (ExteriorAlgebra.ιMulti ℂ n).map_swap (fun k => mode (a k)) hij

theorem normalizedTensorReadout_antisymmetric (n Q : ℕ) (x : Space Q) :
    Antisymmetric (normalizedTensorReadout n Q x) := by
  intro i j hij a
  simp [normalizedTensorReadout,orderedWedge_swap a i j hij,occupationInner]

theorem tensorExterior_single (n Q : ℕ) (a : Configuration n Q) :
    tensorExterior n Q (Pi.single a 1) = orderedWedge a := by
  simp [tensorExterior,Pi.single_apply,orderedWedge]

theorem normalizedTensorReadout_left_inverse (n Q : ℕ) (ψ : State n Q)
    (hψ : Antisymmetric ψ) :
    normalizedTensorReadout n Q (normalizedTensorExterior n Q ψ) = ψ := by
  funext a
  have h := normalizedTensorExterior_inner n Q (Pi.single a 1) ψ hψ
  rw [normalizedTensorExterior,tensorExterior_single,occupationInner_smul_left] at h
  have hr : star (((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)) =
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) := by simp
  rw [hr] at h
  simpa [normalizedTensorReadout,Pi.single_apply] using h

theorem normalizedTensorExterior_adjoint (n Q : ℕ) (ψ : State n Q) (x : Space Q) :
    occupationInner Q (normalizedTensorExterior n Q ψ) x =
      ∑ a, star (ψ a)*normalizedTensorReadout n Q x a := by
  simp only [normalizedTensorExterior,tensorExterior,occupationInner_smul_left,
    occupationInner_sum_left,normalizedTensorReadout,orderedWedge]
  simp only [Complex.star_def,map_inv₀,Complex.conj_ofReal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem normalizedTensorReadout_sub (n Q : ℕ) (x y : Space Q) :
    normalizedTensorReadout n Q (x-y) =
      fun a => normalizedTensorReadout n Q x a - normalizedTensorReadout n Q y a := by
  funext a
  simp [normalizedTensorReadout,occupationInner,mul_sub,Finset.sum_sub_distrib]

theorem normalizedTensorReadout_norm_le (n Q : ℕ) (x : Space Q) :
    (∑ a, ‖normalizedTensorReadout n Q x a‖^2) ≤ occupationNormSq Q x := by
  let ψ := normalizedTensorReadout n Q x
  let z := normalizedTensorExterior n Q ψ
  let S : ℝ := ∑ a, ‖ψ a‖^2
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  have hzx : occupationInner Q z x = (S : ℂ) := by
    rw [normalizedTensorExterior_adjoint]
    change (∑ a, star (ψ a)*ψ a) = (S : ℂ)
    simp only [he,← Complex.ofReal_sum]
    rfl
  have hzz : occupationInner Q z z = (S : ℂ) := by
    rw [occupationInner_self,normalizedTensorExterior_norm n Q ψ
      (normalizedTensorReadout_antisymmetric n Q x)]
  have hxz : occupationInner Q x z = (S : ℂ) := by
    rw [← occupationInner_star,hzx]
    simp
  have hs : occupationNormSq Q (x-z) = occupationNormSq Q x-S := by
    apply Complex.ofReal_injective
    rw [← occupationInner_self]
    have hsub : occupationInner Q (x-z) (x-z) =
        occupationInner Q x x - occupationInner Q x z -
          occupationInner Q z x + occupationInner Q z z := by
      simp [occupationInner,sub_mul,mul_sub,Finset.sum_sub_distrib]
      ring
    rw [hsub,occupationInner_self,hzx,hxz,hzz]
    push_cast
    ring
  have hp := occupationNormSq_nonneg Q (x-z)
  rw [hs] at hp
  exact sub_nonneg.mp hp

end Laughlin.Fock

end OAI
