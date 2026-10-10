import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeProduct
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductMellin

namespace OAI

/-! The actual detector semiprime kernel has independent prime variables.
Its roughness factors can therefore be absorbed into the two coefficients
before applying the centered bilinear estimates. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_pair_tuple_sum (P : Finset Eisenstein) (F : Eisenstein → Eisenstein → ℂ) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin 2 => P), F (f 0) (f 1)) =
      ∑ p ∈ P, ∑ q ∈ P, F p q := by
  trans ∑ x ∈ P.product P, F x.1 x.2
  swap
  · exact Finset.sum_product P P (fun x => F x.1 x.2)
  symm
  apply Finset.sum_bij (fun (x : Eisenstein × Eisenstein) _ => ![x.1,x.2])
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact (Finset.mem_product.mp hx).1
    · exact (Finset.mem_product.mp hx).2
  · intro x _ y _ h
    apply Prod.ext
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  · intro f hf
    refine ⟨(f 0,f 1),Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mp hf 0,Fintype.mem_piFinset.mp hf 1⟩,?_⟩
    funext i
    fin_cases i <;> rfl
  · intro x _
    rfl

def semiprimeRoughWeight (X : ℝ) (p : Eisenstein) : ℂ :=
  1-(primeDetectorCutoff (norm p/(X^(2/5:ℝ))):ℂ)

lemma semiprimeRoughWeight_norm_le (X : ℝ) (p : Eisenstein) :
    ‖semiprimeRoughWeight X p‖ ≤ 1 := by
  have hc : semiprimeRoughWeight X p =
      (((1-primeDetectorCutoff (norm p/(X^(2/5:ℝ)))):ℝ):ℂ) := by
    simp only [semiprimeRoughWeight,Complex.ofReal_sub,Complex.ofReal_one]
  rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (sub_nonneg.mpr (primeDetectorCutoff_le_one _))]
  linarith [primeDetectorCutoff_nonneg (norm p/(X^(2/5:ℝ)))]

lemma semiprimeRoughWeight_zero {X : ℝ} (hX : 0 < X) {p : Eisenstein}
    (hp : norm p ≤ X^(2/5:ℝ)) : semiprimeRoughWeight X p = 0 := by
  unfold semiprimeRoughWeight
  rw [primeDetectorCutoff_one ((div_le_one (Real.rpow_pos_of_pos hX _)).mpr hp)]
  simp

theorem centralSemiprimeProduct_eq_bilinear (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) :
    centralSemiprimeProduct ℓ H T X =
      (1/2:ℂ)*∑ p ∈ primeCutoff (3*X), ∑ q ∈ primeCutoff (3*X),
        semiprimeRoughWeight X p*semiprimeRoughWeight X q*
          centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q) := by
  rw [centralSemiprimeProduct_eq_ordered ℓ H T hX]
  congr 1
  convert prime_pair_tuple_sum (primeCutoff (3*X))
    (fun p q => semiprimeRoughWeight X p*semiprimeRoughWeight X q*
      centeredHeightKernel ℓ primeProductEnvelope H T X X (p*q)) using 1
  apply Finset.sum_congr rfl
  intro f _
  simp only [Fin.prod_univ_two,semiprimeRoughWeight]

end CubicFirstMoment

end

end OAI
