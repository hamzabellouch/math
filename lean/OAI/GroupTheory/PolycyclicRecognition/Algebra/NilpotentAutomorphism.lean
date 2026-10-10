import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Integrating the needed nilpotent automorphisms

The finite published Dynkin identity and bijectivity of the intrinsic
exponential suffice to integrate any Lie automorphism of the nilpotent
model. No general Lie-integration theorem is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

/-- Conjugation through the intrinsic exponential as a bijection. -/
def exponentialConjugate (F : L ≃ₗ⁅ℝ⁆ L) : G ≃ G :=
  let q : L ≃ G := Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)
  q.symm.trans (F.toLinearEquiv.toEquiv.trans q)

omit [T2Space G] in
@[simp] theorem exponentialConjugate_apply_exp (F : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    exponentialConjugate e Exp hbij F (Exp (e x)) = Exp (e (F x)) := by
  change Exp (e (F ((Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)).symm
    ((Equiv.ofBijective (Exp ∘ e) (hbij.comp e.bijective)) x)))) = _
  rw [Equiv.symm_apply_apply]

/-- A finite Lie polynomial commutes with `F`, so the same Dynkin formula
on both sides proves multiplicativity after exponentiation. -/
theorem exponentialConjugate_map_mul
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (F : L ≃ₗ⁅ℝ⁆ L) (g k : G) :
    exponentialConjugate e Exp hbij F (g * k) =
      exponentialConjugate e Exp hbij F g * exponentialConjugate e Exp hbij F k := by
  obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
  obtain ⟨y, rfl⟩ := (hbij.comp e.bijective).surjective k
  change exponentialConjugate e Exp hbij F (Exp (e x) * Exp (e y)) =
    exponentialConjugate e Exp hbij F (Exp (e x)) *
    exponentialConjugate e Exp hbij F (Exp (e y))
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc 2
  have hp (u v : L) : Exp (e u) * Exp (e v) =
      Exp (e (finiteDynkinPolynomial coeff ![u, v])) := by
    simpa [List.ofFn_succ] using hprod ![u, v]
  rw [hp, exponentialConjugate_apply_exp, exponentialConjugate_apply_exp,
    exponentialConjugate_apply_exp, hp]
  congr 2
  calc
    F (finiteDynkinPolynomial coeff ![x, y]) =
        finiteDynkinPolynomial coeff (fun i => F (![x, y] i)) :=
      finiteDynkinPolynomial_map F.toLieHom coeff ![x, y]
    _ = _ := by
      congr 1
      funext i
      fin_cases i <;> rfl

/-- The group automorphism needed for exact weight dilation. -/
def integrateNilpotentLieEquiv
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) : G ≃* G where
  __ := exponentialConjugate e Exp hbij F
  map_mul' := exponentialConjugate_map_mul e Exp hbij dynkin hExp hc F

@[simp] theorem integrateNilpotentLieEquiv_apply_exp
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    integrateNilpotentLieEquiv e Exp hbij dynkin hExp hc F (Exp (e x)) = Exp (e (F x)) :=
  exponentialConjugate_apply_exp e Exp hbij F x

end PolycyclicRecognition

end

end OAI
