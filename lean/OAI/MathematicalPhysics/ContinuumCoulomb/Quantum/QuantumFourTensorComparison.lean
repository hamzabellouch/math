import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorGround
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorEffectiveError

namespace OAI

/-! Explicit full-space comparison with the calibrated logical matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaEffectiveBottom_matrix_error
    (L : EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 2))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (B : EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (N : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) {δ : ℝ}
    (he : ∀ p : EuclideanSpace ℂ (Fin n → Fin 2), ‖p‖ = 1 →
      |Perturbation.effectiveForm L T B p-qmaQuadratic N (fun i => p i)| ≤ δ) :
    |Perturbation.effectiveBottom L T B-MediatorGraph.normalizedBottom N| ≤ δ := by
  obtain ⟨p,hp,hmin⟩ := Perturbation.effectiveForm_minimizer L T B u hu
  rw [Perturbation.effectiveBottom_eq L T B p hp hmin]
  have hlow := qmaNormalizedBottom_le N p hp
  have herror := abs_le.mp (he p hp)
  have hupp : Perturbation.effectiveForm L T B p-δ ≤ MediatorGraph.normalizedBottom N := by
    apply le_qmaNormalizedBottom N u hu
    intro x hx
    have hm := hmin x
    simp only [hx,one_pow,mul_one] at hm
    have herr := (abs_le.mp (he x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem qmaFourTensorPerturbation_operator (r : ℝ)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    (qmaMatrixOperator ((r:ℂ) • V+C)).restrictScalars ℝ = qmaFourTensorPerturbation r V C := by
  rw [qmaMatrixOperator_add,qmaMatrixOperator_smul]
  ext x s
  change (r:ℂ)*(qmaMatrixOperator V x) s+(qmaMatrixOperator C x) s =
    (r • qmaMatrixOperator V x+qmaMatrixOperator C x) s
  simp only [PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]

theorem qmaFourTensorOff_inverse_bound (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x) (hTn : ‖T‖ ≤ 1/(4*r^2))
    {v c : ℝ} (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖T (qmaFourTensorOff (qmaFourTensorPerturbation r V C) p)‖ ≤
      (v/(8*r)+c/(4*r^2))*‖p‖ := by
  rw [qmaFourTensorOff_split r V C hV p]
  apply qmaSecondOrder_inverse_column_bound T hr hTn
  · have h := qmaFourTensorInverse_column hr T hTA (V*qmaFourTensorEncoding n) hV hH p
    simpa only [qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,qmaFourTensorInclusion,
      ContinuousLinearMap.coe_restrictScalars'] using h
  · exact qmaFourTensor_column_norm V hVn p
  · apply ((qmaFourTensorHigh n).le_opNorm _).trans
    exact (mul_le_mul (qmaFourTensorHigh_norm n) (qmaFourTensor_column_norm C hCn p)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem qmaFourTensor_comparison (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hVs : V.conjTranspose = V) (hCs : C.conjTranspose = C)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1)
    (hsmall : 2*(r*v+c+‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖+
      (v*c/(4*r)+c^2/(4*r^2))) ≤ 4*r^2) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C))-
      MediatorGraph.normalizedBottom (qmaFourTensorEffectiveMatrix V C)| ≤
      2*(r*v+c+‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖+
        (v*c/(4*r)+c^2/(4*r^2)))*(v/(8*r)+c/(4*r^2))^2+
        (v*c/(4*r)+c^2/(4*r^2)) := by
  let δ := v*c/(4*r)+c^2/(4*r^2)
  let N := qmaFourTensorEffectiveMatrix V C
  let K := qmaFourTensorPerturbation r V C
  obtain ⟨T,hAT,hTA,hTn⟩ := qmaFourTensor_inverse_exists n hr
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have herror (p : EuclideanSpace ℂ (Fin n → Fin 2)) (hp : ‖p‖ = 1) :
      |Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p-
        qmaQuadratic N (fun i => p i)| ≤ δ := by
    simpa only [hp,one_pow,mul_one] using qmaFourTensorEffective_error r hr V C hV hH T hAT hTA hTn hv hc hVn hCn p
  have hbound (p : EuclideanSpace ℂ (Fin n → Fin 2)) (hp : ‖p‖ = 1) :
      |Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p| ≤
        ‖spinMatrixOperator N‖+δ := by
    have he := herror p hp
    have hn := qmaQuadratic_norm_bound N p
    simp only [hp,one_pow,mul_one] at hn
    have ht := abs_sub_le (Perturbation.effectiveForm (qmaFourTensorLow K) T (qmaFourTensorOff K) p)
      (qmaQuadratic N (fun i => p i)) 0
    simp only [sub_zero] at ht
    linarith
  have hU : ((r:ℂ) • V+C).conjTranspose = (r:ℂ) • V+C := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hVs,hCs,Complex.star_def,Complex.conj_ofReal]
  have hUn : ‖spinMatrixOperator ((r:ℂ) • V+C)‖ ≤ r*v+c := by
    rw [spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact add_le_add (mul_le_mul_of_nonneg_left hVn hr.le) hCn
  have hground := qmaFourTensorGround_error r hr ((r:ℂ) • V+C) hU T hAT
    (show 0 ≤ r*v+c by positivity) (show 0 ≤ ‖spinMatrixOperator N‖+δ by positivity)
    (show 0 ≤ v/(8*r)+c/(4*r^2) by positivity)
    (by simpa only [add_assoc] using hsmall) hUn
    (by rw [qmaFourTensorPerturbation_operator]; exact qmaFourTensorOff_inverse_bound r hr V C hV hH T hTA hTn hVn hCn)
    (by rw [qmaFourTensorPerturbation_operator]; exact hbound) u hu
  rw [qmaFourTensorPerturbation_operator] at hground
  have heff := qmaEffectiveBottom_matrix_error (qmaFourTensorLow K) T (qmaFourTensorOff K) N u hu herror
  have h := (abs_sub_le
    (MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r ((r:ℂ) • V+C)))
    (Perturbation.effectiveBottom (qmaFourTensorLow K) T (qmaFourTensorOff K))
    (MediatorGraph.normalizedBottom N)).trans (add_le_add hground heff)
  simpa only [N,δ,add_assoc] using h

end ContinuumCoulomb

end

end OAI
