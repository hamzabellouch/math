import OAI.Analysis.Quantum.DimensionTen.ChoiPairing
import OAI.Analysis.Quantum.DimensionTen.CompoundTrace
import OAI.Analysis.Quantum.DimensionTen.ExteriorMaps

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma tensorMap_kronecker {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) (A : Mat a) (B : Mat c) :
    tensorMap F G (A ⊗ₖ B) = F A ⊗ₖ G B := by
  have hblock (i j : Fin c) : (fun u v => A u v * B i j) = B i j • A := by
    ext u v
    simp [Matrix.smul_apply, mul_comm]
  rw [linear_expansion G hG B]
  ext ⟨u,i⟩ ⟨v,j⟩
  simp only [tensorMap, Matrix.kronecker, Matrix.sum_apply, hblock, hF.2,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma exteriorMap_veronese (x : Fin 4 → ℂ) :
    exteriorMap (pure (veronese x)) = compound (pencilMap (pure x)) := by
  unfold exteriorMap
  rw [symmetric_pure_veronese, tensorMap_kronecker _ _ pencilMap_linear pencilMap_linear]
  exact exterior_compound _

lemma firstSix_isometry : firstSixᴴ * firstSix = (1 : Mat 6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, firstSix, Matrix.conjTranspose_apply,
      Matrix.one_apply]

lemma firstSix_compression (B : Mat 6) :
    firstSixᴴ * (firstSix * B * firstSixᴴ) * firstSix = B := by
  calc
    _ = (firstSixᴴ * firstSix) * B * (firstSixᴴ * firstSix) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [firstSix_isometry]; simp

lemma phiTwo_phiOne (A : Mat 10) :
    phiTwo (phiOne A) = hsAdjoint complementaryMap (exteriorMap Aᵀ) := by
  unfold phiTwo phiOne
  rw [firstSix_compression]

lemma compositeChoi_posSemidef : compositeChoi.PosSemidef := by
  exact cp_choi_posSemidef _ (cp_comp _ _ phiOne_ppt.2.1 phiTwo_ppt.2.1) (by decide)

lemma compositeChoi_pairing (u v : Fin 10 → ℂ) :
    star (productVector u v) ⬝ᵥ (compositeChoi *ᵥ productVector u v) =
      Matrix.trace (complementaryMap (pure v) * exteriorMap (pure u)) := by
  rw [compositeChoi, choi_product_dot _ (linear_comp _ _ phiOne_ppt.1 phiTwo_ppt.1)]
  simp only [Function.comp_apply, phiTwo_phiOne, Matrix.transpose_transpose]
  rw [complementaryMap_kraus, krausMap_adjoint, kraus_trace_adjoint]

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix
namespace DimensionTen
lemma blocksZ_zero_gram : (blocksZ 0)ᵀ * blocksZ 0 = (36:ℤ) • (1:Matrix (Fin 4) (Fin 4) ℤ) := by
  decide
lemma blocks_zero_gram : (blocks 0)ᴴ * blocks 0 = (36:ℂ) • (1:Mat 4) := by
  rw [blocks_conjTranspose]
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℤ => A.map (Int.castRingHom ℂ)) blocksZ_zero_gram
  have hm : ((36:ℤ) • (1:Matrix (Fin 4) (Fin 4) ℤ)).map (Int.castRingHom ℂ) =
      (36:ℂ) • (1:Mat 4) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.map_apply, Matrix.ofNat_apply]
  rw [hm] at h
  simpa only [Matrix.map_mul, Matrix.transpose_map, blocks] using h

lemma pencil_ezero : pencil (![1,0,0,0] : Fin 4 → ℂ) = blocks 0 := by
  simp [pencil, Fin.sum_univ_succ]
lemma pencilMap_ezero_fast : pencilMap (pure (![1,0,0,0] : Fin 4 → ℂ)) =
    (36 : ℂ) • (1 : Mat 4) := by
  change pencilMap (projector (![1,0,0,0] : Fin 4 → ℂ)) = _
  rw [pencilMap_projector_gram, pencil_ezero, blocks_zero_gram]
end DimensionTen

end
end

end OAI
