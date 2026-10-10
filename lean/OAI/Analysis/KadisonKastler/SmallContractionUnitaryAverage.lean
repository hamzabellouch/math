import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Combination

namespace OAI

/-! # Small contractions as four-unitary averages

The half unit ball of a unital C-star algebra lies in the convex hull of
its unitaries. The explicit four-term formula is enough for the spatial
derivation argument; no unitary density theorem is required.
-/

namespace KadisonKastler

noncomputable section

open scoped ComplexStarModule

variable {A : Type*} [CStarAlgebra A]

theorem exists_four_unitaries_average (a : A) (ha : ‖a‖ ≤ 1 / 2) :
    ∃ u : Fin 4 → unitary A, a = (1 / 4 : ℝ) • ∑ i, (u i : A) := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  let b := (2 : ℝ) • a
  have hb : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_ofNat]
    linarith
  let u := selfAdjoint.unitarySelfAddISMul (ℜ b) ((realPart.norm_le b).trans hb)
  let v := selfAdjoint.unitarySelfAddISMul (ℑ b) ((imaginaryPart.norm_le b).trans hb)
  let iUnit : unitary ℂ := ⟨Complex.I, by simp [Unitary.mem_iff]⟩
  refine ⟨![u, star u, iUnit • v, iUnit • star v], ?_⟩
  have hu : (2⁻¹ : ℝ) • ((u : A) + star (u : A)) = (ℜ b : A) := by
    simpa only [realPart_apply_coe] using
      congrArg Subtype.val (selfAdjoint.realPart_unitarySelfAddISMul (ℜ b)
        ((realPart.norm_le b).trans hb))
  have hv : (2⁻¹ : ℝ) • ((v : A) + star (v : A)) = (ℑ b : A) := by
    simpa only [realPart_apply_coe] using
      congrArg Subtype.val (selfAdjoint.realPart_unitarySelfAddISMul (ℑ b)
        ((imaginaryPart.norm_le b).trans hb))
  have he := realPart_add_I_smul_imaginaryPart b
  rw [← hu, ← hv] at he
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Unitary.coe_star, Unitary.coe_smul]
  change a = (1 / 4 : ℝ) •
    ((u : A) + star (u : A) + Complex.I • (v : A) + Complex.I • star (v : A))
  calc
    a = (1 / 2 : ℝ) • b := by dsimp [b]; module
    _ = (1 / 2 : ℝ) • ((2⁻¹ : ℝ) • ((u : A) + star (u : A)) +
        Complex.I • (2⁻¹ : ℝ) • ((v : A) + star (v : A))) := congrArg _ he.symm
    _ = _ := by module

theorem map_small_contraction_mem_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : A →ₗ[ℝ] E) (s : Set E) (hs : Convex ℝ s)
    (hu : ∀ u : unitary A, f (u : A) ∈ s)
    (a : A) (ha : ‖a‖ ≤ 1 / 2) : f a ∈ s := by
  obtain ⟨u, he⟩ := exists_four_unitaries_average a ha
  rw [he, map_smul, map_sum]
  have h := hs.sum_mem (t := Finset.univ) (w := fun _ : Fin 4 => (1 / 4 : ℝ))
    (z := fun i => f (u i : A)) (by intros; norm_num) (by norm_num)
    (fun i _ => hu (u i))
  simpa only [← Finset.smul_sum] using h

theorem mul_small_contractions_mem_convex {B : Type*} [CStarAlgebra B]
    (φ : A →ₐ[ℝ] B) (c : B) (s : Set B) (hs : Convex ℝ s)
    (hu : ∀ u v : unitary A, φ (u : A) * c * φ (v : A) ∈ s)
    (a b : A) (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2) :
    φ a * c * φ b ∈ s := by
  have hright (u : unitary A) : φ (u : A) * c * φ b ∈ s := by
    let f : A →ₗ[ℝ] B := {
      toFun x := φ (u : A) * c * φ x
      map_add' x y := by simp only [map_add, mul_add]
      map_smul' t x := by simp only [map_smul, mul_smul_comm, RingHom.id_apply] }
    exact map_small_contraction_mem_convex f s hs (hu u) b hb
  let f : A →ₗ[ℝ] B := {
    toFun x := φ x * c * φ b
    map_add' x y := by simp only [map_add, add_mul]
    map_smul' t x := by simp only [map_smul, smul_mul_assoc, RingHom.id_apply] }
  exact map_small_contraction_mem_convex f s hs hright a ha

end

end KadisonKastler

end OAI
