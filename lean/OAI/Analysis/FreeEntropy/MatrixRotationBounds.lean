import OAI.Analysis.FreeEntropy.VolumetricNet

namespace OAI

noncomputable section
open scoped Matrix.Norms.L2Operator
open Finset Set
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem unitary_matrix_norm {d : ℕ} (hd : 0<d) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    matrixOpNorm (U:Matrix (Fin d) (Fin d) ℂ)=1 := by
  have : NeZero d := ⟨by omega⟩
  exact CStarRing.norm_coe_unitary U
 theorem hsNorm_unitary_difference (hd : 0<d) (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ)-star (V:Matrix (Fin d) (Fin d) ℂ)*A*(V:Matrix (Fin d) (Fin d) ℂ)) ≤
      2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*hsNorm A := by
  have he : star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ)-star (V:Matrix (Fin d) (Fin d) ℂ)*A*(V:Matrix (Fin d) (Fin d) ℂ) =
    star (U:Matrix (Fin d) (Fin d) ℂ)*A*((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))+
      star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*A*(V:Matrix (Fin d) (Fin d) ℂ) := by rw [star_sub]; noncomm_ring
  rw [he]
  have hU : matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))=1 := by
    rw [show matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))=matrixOpNorm (U:Matrix (Fin d) (Fin d) ℂ) from Matrix.l2_opNorm_conjTranspose _]
    exact unitary_matrix_norm hd U
  have hUV : matrixOpNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))=
      matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)) := Matrix.l2_opNorm_conjTranspose _
  calc
    _ ≤ hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))+
      hsNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*A*(V:Matrix (Fin d) (Fin d) ℂ)) := hsNorm_add _ _
    _ ≤ (matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))*hsNorm A)*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))+
      (matrixOpNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))*hsNorm A)*matrixOpNorm (V:Matrix (Fin d) (Fin d) ℂ) := by
      apply add_le_add
      · exact (hsNorm_mul_right _ _).trans (mul_le_mul_of_nonneg_right (hsNorm_mul_left _ _) (matrixOpNorm_nonneg _))
      · exact (hsNorm_mul_right _ _).trans (mul_le_mul_of_nonneg_right (hsNorm_mul_left _ _) (matrixOpNorm_nonneg _))
    _ = _ := by rw [hU,hUV,unitary_matrix_norm hd V]; ring
 theorem rotateCoordinates_sub_norm (hd : 0<d) (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (a : MatrixCoordinates n d) :
    ‖rotateCoordinates U a-rotateCoordinates V a‖ ≤
      2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖ := by
  have hnn := matrixOpNorm_nonneg ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖)).mp
  rw [← hermitianChart_normSq]
  have he (i : Fin n) : hermitianMatrix (rotateCoordinates U a-rotateCoordinates V a) i = hermitianMatrix (rotateCoordinates U a) i-hermitianMatrix (rotateCoordinates V a) i := congrFun (map_sub (hermitianChart n d) _ _) i
  simp_rw [he]
  change (∑i,∑j,∑k,Complex.normSq ((hermitianMatrix (rotateCoordinates U a) i-hermitianMatrix (rotateCoordinates V a) i) j k)) ≤ _
  simp_rw [hermitianMatrix_rotate,← hsNorm_sq]
  calc
    _ ≤ ∑i,(2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*hsNorm (hermitianMatrix a i))^2 := by
      apply sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (hsNorm_nonneg _) (hsNorm_unitary_difference hd U V _) _
    _ = _ := by
      simp_rw [mul_pow,← mul_sum,hsNorm_sq,hermitianChart_normSq]
 theorem isCompact_unitary_matrix (hd : 0<d) :
    IsCompact (unitary (Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  apply (Metric.isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_unitary,?_⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℂ)]
  refine ⟨1,fun U hU => ?_⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  change matrixOpNorm U≤1
  exact (unitary_matrix_norm hd ⟨U,hU⟩).le
 theorem unitary_matrix_net (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃ s : Finset (unitary (Matrix (Fin d) (Fin d) ℂ)),
      (∀ U : unitary (Matrix (Fin d) (Fin d) ℂ), ∃ V∈s,matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))≤ε) ∧
      (s.card:ℝ)≤(1+2/ε)^(2*d^2) := by
  classical
  obtain ⟨s,hs,hcover,hcard⟩ := compact_finite_net _ (isCompact_unitary_matrix hd)
    (show (0:ℝ)≤1 by norm_num) hε (fun U hU => (unitary_matrix_norm hd ⟨U,hU⟩).le)
  let g : {U // U∈s} → unitary (Matrix (Fin d) (Fin d) ℂ) := fun U => ⟨U,hs U U.property⟩
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · intro U
    obtain ⟨V,hV,hUV⟩ := hcover U U.property
    refine ⟨g ⟨V,hV⟩,mem_image.mpr ⟨⟨V,hV⟩,mem_univ _,rfl⟩,?_⟩
    change ‖(U:Matrix (Fin d) (Fin d) ℂ)-V‖≤ε
    simpa only [dist_eq_norm] using hUV
  · have he : Module.finrank ℝ (Matrix (Fin d) (Fin d) ℂ)=2*d^2 := by
      rw [Module.finrank_matrix,Complex.finrank_real_complex]
      simp only [Fintype.card_fin]
      ring
    calc
      _ ≤ (s.card:ℝ) := by exact_mod_cast (Finset.card_image_le.trans_eq (by simp))
      _ ≤ _ := by simpa [he] using hcard
end FiniteEntropySeparation

end

end OAI
