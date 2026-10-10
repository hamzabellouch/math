import OAI.Analysis.KadisonKastler.WeightedStripCenter
import OAI.Analysis.KadisonKastler.ModularRootCommutation

namespace OAI

/-! # Factoring the weighted strip boundaries through the middle operator -/

namespace KadisonKastler

noncomputable section

private theorem sandwich_reorder {A : Type*} [Ring A] (d r q u v x : A)
    (hrv : Commute r v) (hdq : Commute d q) (hdu : Commute d u) :
    (d * r * v) * x * (d * q * u) = d * v * (r * x * q) * u * d := by
  have hl : d * r * v = d * v * r := by
    rw [mul_assoc, hrv.eq, ← mul_assoc]
  have hh : d * q * u = q * u * d := by
    rw [hdq.eq, mul_assoc, hdu.eq, ← mul_assoc]
  rw [hl, hh]
  simp only [mul_assoc]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_commute_complement_root (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphComplementRoot (M := M) J Ω) := by
  rw [tomitaGraphComplementRoot, CFC.sqrt_eq_cfc]
  exact (((Commute.one_right _).sub_right
    (modularStrongGroup_commute_resolvent J Ω hsep hcyc t)).symm.cfc_nnreal NNReal.sqrt).symm

theorem modularStrongGroup_commute_middle (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaMiddleOperator (M := M) J Ω) :=
  (modularStrongGroup_commute_root J Ω hsep hcyc t).mul_right
    (modularStrongGroup_commute_complement_root J Ω hsep hcyc t)

theorem weightedStrip_boundary_factorization (X Y : H →L[ℂ] H) (α β : ℂ)
    (heq : tomitaMiddleOperator (M := M) J Ω * Y * tomitaMiddleOperator (M := M) J Ω =
      α • (graphResolvent M J Ω 1 * X * (1 - graphResolvent M J Ω 1)) +
      β • ((1 - graphResolvent M J Ω 1) * X * graphResolvent M J Ω 1)) (t : ℝ) :
    α • (weightedStripOperator (M := M) J Ω (-((1 / 2 : ℂ) + t * Complex.I)) * X *
        weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + t * Complex.I)) +
      β • (weightedStripOperator (M := M) J Ω (-((-1 / 2 : ℂ) + t * Complex.I)) * X *
        weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + t * Complex.I)) =
      weightedStripOperator (M := M) J Ω 0 *
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) * Y *
          (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)) *
        weightedStripOperator (M := M) J Ω 0 := by
  let R := graphResolvent M J Ω 1
  let Q := 1 - R
  let D := R * Q ^ 2
  let T := tomitaMiddleOperator (M := M) J Ω
  let U := (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
  let V := (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
  have hRQ : Commute R Q := (Commute.one_right R).sub_right (Commute.refl R)
  have hDR : Commute D R := (Commute.refl R).mul_left (hRQ.pow_right 2).symm
  have hDQ : Commute D Q := hRQ.mul_left (Commute.pow_self Q 2)
  have hUR : Commute U R := modularStrongGroup_commute_resolvent J Ω hsep hcyc t
  have hVR : Commute V R := modularStrongGroup_commute_resolvent J Ω hsep hcyc (-t)
  have hUQ : Commute U Q := (Commute.one_right U).sub_right hUR
  have hVQ : Commute V Q := (Commute.one_right V).sub_right hVR
  have hDU : Commute D U := (hUR.mul_right (hUQ.pow_right 2)).symm
  have hUT : Commute U T := modularStrongGroup_commute_middle J Ω hsep hcyc t
  have hVT : Commute V T := modularStrongGroup_commute_middle J Ω hsep hcyc (-t)
  have hTR : Commute T R := by
    change Commute (tomitaMiddleOperator (M := M) J Ω) (graphResolvent M J Ω 1)
    rw [← tomitaGraphRoot_square J Ω]
    have h : Commute (tomitaMiddleOperator (M := M) J Ω) (tomitaGraphRoot (M := M) J Ω) :=
      (Commute.refl _).mul_left (tomitaGraphRoots_commute J Ω).symm
    exact h.mul_right h
  have hTQ : Commute T Q := (Commute.one_right T).sub_right hTR
  have hDT : Commute D T := (hTR.mul_right (hTQ.pow_right 2)).symm
  have hr (s : ℝ) : weightedStripOperator (M := M) J Ω ((1 / 2 : ℂ) + s * Complex.I) =
      D * Q * (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s) : H →L[ℂ] H) := by
    rw [weightedStripOperator_right J Ω hsep hcyc]
    dsimp only [D, Q, R]
    noncomm_ring
  have hl (s : ℝ) : weightedStripOperator (M := M) J Ω ((-1 / 2 : ℂ) + s * Complex.I) =
      D * R * (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd s) : H →L[ℂ] H) := by
    rw [weightedStripOperator_left J Ω hsep hcyc]
    dsimp only [D, Q, R]
    noncomm_ring
  rw [show -((1 / 2 : ℂ) + t * Complex.I) = (-1 / 2 : ℂ) + (-t) * Complex.I by ring,
    show -((-1 / 2 : ℂ) + t * Complex.I) = (1 / 2 : ℂ) + (-t) * Complex.I by ring,
    ← Complex.ofReal_neg, hl (-t), hr t, hr (-t), hl t,
    weightedStripOperator_center J Ω hsep hcyc]
  change α • ((D * R * V) * X * (D * Q * U)) +
    β • ((D * Q * V) * X * (D * R * U)) = (D * T) * (V * Y * U) * (D * T)
  rw [sandwich_reorder D R Q U V X hVR.symm hDQ hDU,
    sandwich_reorder D Q R U V X hVQ.symm hDR hDU]
  calc
    _ = D * V * (α • (R * X * Q) + β • (Q * X * R)) * U * D := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    _ = D * V * (T * Y * T) * U * D := by rw [← heq]
    _ = (D * T * V) * Y * (D * T * U) :=
      (sandwich_reorder D T T U V Y hVT.symm hDT hDU).symm
    _ = (D * T) * (V * Y * U) * (D * T) := by
      rw [((hDU.mul_left hUT.symm).eq : D * T * U = U * (D * T))]
      simp only [mul_assoc]

end

end KadisonKastler

end OAI
