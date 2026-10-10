import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorError
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamilyBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGroundComparison

namespace OAI

/-! Full physical ground-energy comparison for the four-spin tensor simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorPhysicalMatrix (r : ℝ) (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :=
  (r^2:ℂ) • qmaFourTensorPenalty n+U

theorem qmaFourTensorPhysicalMatrix_apply (r : ℝ)
    (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaMatrixOperator (qmaFourTensorPhysicalMatrix r U) x =
      qmaFourTensorPhysical r ((qmaMatrixOperator U).restrictScalars ℝ) x := by
  rw [qmaFourTensorPhysicalMatrix,qmaMatrixOperator_add,qmaMatrixOperator_smul,qmaFourTensorPhysical]
  ext s
  simp only [_root_.add_apply,_root_.smul_apply,PiLp.add_apply,PiLp.smul_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars',Complex.real_smul,Complex.ofReal_pow,
    smul_eq_mul]

theorem qmaFourTensorHighPerturbation_norm
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :
    ‖qmaFourTensorHighPerturbation K‖ ≤ ‖K‖ := by
  unfold qmaFourTensorHighPerturbation
  calc
    _ ≤ ‖qmaFourTensorHigh n‖*‖K.comp (qmaFourTensorHigh n)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(‖K‖*1) := mul_le_mul (qmaFourTensorHigh_norm n)
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (qmaFourTensorHigh_norm n) (norm_nonneg K)))
      (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem qmaFourTensorGround_error (r : ℝ) (hr : 0 < r)
    (U : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) (hU : U.conjTranspose = U)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x)
    {d m η : ℝ} (hd : 0 ≤ d) (hm : 0 ≤ m) (hη : 0 ≤ η)
    (hsmall : 2*(d+m) ≤ 4*r^2) (hUn : ‖spinMatrixOperator U‖ ≤ d)
    (hTB : ∀ p, ‖T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ) p)‖ ≤ η*‖p‖)
    (hbound : ∀ p : EuclideanSpace ℂ (Fin n → Fin 2), ‖p‖ = 1 →
      |Perturbation.effectiveForm (qmaFourTensorLow ((qmaMatrixOperator U).restrictScalars ℝ))
        T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ)) p| ≤ m)
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U)-
      Perturbation.effectiveBottom (qmaFourTensorLow ((qmaMatrixOperator U).restrictScalars ℝ))
        T (qmaFourTensorOff ((qmaMatrixOperator U).restrictScalars ℝ))| ≤ 2*(d+m)*η^2 := by
  let K := (qmaMatrixOperator U).restrictScalars ℝ
  let C := qmaFourTensorLow K
  let B := qmaFourTensorOff K
  let D := qmaFourTensorHighPerturbation K
  let A := qmaFourTensorPadded n r
  have hK : ∀ x y, ⟪x,K y⟫_ℝ = ⟪K x,y⟫_ℝ := qmaMatrixOperator_real_symmetric U hU
  have hDnorm : ‖D‖ ≤ d := (qmaFourTensorHighPerturbation_norm K).trans (by
    simpa only [K,ContinuousLinearMap.norm_restrictScalars,qmaMatrixOperator_square] using hUn)
  have hD (q : EuclideanSpace ℂ (Fin n → Fin 16)) : |⟪q,D q⟫_ℝ| ≤ d*‖q‖^2 := by
    simpa only [one_mul] using Perturbation.highPerturbation_abs_le D
      (g := d) (ε := 1) (by simpa only [one_mul] using hDnorm) q
  have hAsymm : ∀ x y, ⟪x,A y⟫_ℝ = ⟪A x,y⟫_ℝ := qmaFourTensorPadded_symmetric n r
  have hgap : ∀ q, (4*r^2)*‖q‖^2 ≤ Perturbation.penaltyForm A q :=
    qmaFourTensor_padded_gap n r
  obtain ⟨p,hp,hmin⟩ := Perturbation.effectiveForm_minimizer C T B u hu
  rw [Perturbation.effectiveBottom_eq C T B p hp hmin]
  let μ := Perturbation.effectiveForm C T B p
  let ε := 2*(d+m)*η^2
  have hμ : |μ| ≤ m := hbound p hp
  have hl (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
      (μ-ε)*‖x‖^2 ≤ ⟪x,qmaFourTensorPhysical r K x⟫_ℝ := by
    rw [qmaFourTensorPhysical_energy r K hK]
    have h := Perturbation.sharp_lowBlockEnergy_lower C A T D B hd hm hη hsmall hAT hAsymm hgap
      hTB hD (abs_le.mp hμ).2 hmin (qmaFourTensorRestriction n x) (qmaFourTensorHigh n x)
    rw [qmaFourTensor_norm_decomposition] at h
    have hle : ‖qmaFourTensorRestriction n x‖^2 ≤ ‖x‖^2 := by
      have hn := qmaFourTensor_norm_decomposition n x
      nlinarith [sq_nonneg ‖qmaFourTensorHigh n x‖]
    have he : 0 ≤ ε := by dsimp [ε]; positivity
    nlinarith
  have hu0 : ‖qmaFourTensorInclusion n u‖ = 1 := (qmaFourTensor_inclusion_norm n u).trans hu
  have hlow : μ-ε ≤ MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U) := by
    apply le_qmaNormalizedBottom _ (qmaFourTensorInclusion n u) hu0
    intro x hx
    rw [qmaQuadratic_operator,qmaFourTensorPhysicalMatrix_apply]
    simpa only [hx,one_pow,mul_one] using hl x
  let q := -(T (B p))
  let x := qmaFourTensorInclusion n p+q
  have hq : qmaFourTensorRestriction n q = 0 := by
    change qmaFourTensorRestriction n (-(T (B p))) = 0
    rw [map_neg,qmaFourTensorInverse_high hr T hAT (B p) (qmaFourTensorRestriction_high n _),neg_zero]
  have hxn : ‖x‖^2 = ‖p‖^2+‖q‖^2 :=
    Perturbation.orthogonalAssemble_norm _ _ (qmaFourTensor_restrict_include n)
      (qmaFourTensor_inclusion_adjoint n) p q hq
  have hxpos : 0 < ‖x‖^2 := by rw [hxn,hp]; positivity
  have hxe : ⟪x,qmaFourTensorPhysical r K x⟫_ℝ = Perturbation.lowBlockEnergy C A D B p q :=
    Perturbation.orthogonalBlock_energy _ _ _ _ _ _ _ (qmaFourTensor_restrict_include n)
      (qmaFourTensor_inclusion_adjoint n) (qmaFourTensorPhysical_symmetric r K hK)
      (qmaFourTensorPhysical_low r K) (fun _ => qmaFourTensorRestriction_high n _)
      (qmaFourTensorPhysical_high r K) p q hq
  have htrial : ⟪x,qmaFourTensorPhysical r K x⟫_ℝ/‖x‖^2 ≤ μ+(d+m)*η^2 := by
    rw [hxe,hxn]
    exact Perturbation.sharp_lowBlockRayleigh_trial_upper C A T D B hd hm hη hAT hTB hD
      (abs_le.mp hμ).1 p hp rfl
  have hb : BddBelow {e | ∃ x : EuclideanSpace ℂ (Fin n → Fin 16), 0 < ‖x‖^2 ∧
      e = ⟪x,spinMatrixOperator (qmaFourTensorPhysicalMatrix r U) x⟫_ℝ/‖x‖^2} := by
    refine ⟨μ-ε,?_⟩
    rintro e ⟨y,hy,rfl⟩
    rw [← qmaMatrixOperator_square,qmaFourTensorPhysicalMatrix_apply]
    exact (le_div_iff₀ hy).mpr (hl y)
  have hup : MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix r U) ≤ μ+(d+m)*η^2 := by
    rw [MediatorGraph.normalizedBottom_eq_rayleigh]
    apply (csInf_le hb ⟨x,hxpos,rfl⟩).trans
    simpa only [← qmaMatrixOperator_square,qmaFourTensorPhysicalMatrix_apply] using htrial
  have heps : (d+m)*η^2 ≤ ε := by
    dsimp [ε]
    nlinarith [mul_nonneg (add_nonneg hd hm) (sq_nonneg η)]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end ContinuumCoulomb

end

end OAI
