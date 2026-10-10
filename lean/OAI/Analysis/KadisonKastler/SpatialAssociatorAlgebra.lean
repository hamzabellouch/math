import OAI.Analysis.KadisonKastler.SpatialAssociator
import OAI.Analysis.KadisonKastler.SpatialMatrixDensity
import OAI.Analysis.KadisonKastler.CanonicalAmplification

namespace OAI

/-! # Associativity of represented spatial von Neumann products

The canonical Hilbert tensor associator transports the actual spatial
product algebras. The passage from algebraic generators to their von
Neumann algebras uses the existing bounded Kaplansky approximation input.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped TensorProduct Topology

noncomputable section

universe u

section LeftContinuity

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Bounded strong convergence is preserved by the first tensor leg. -/
theorem spatialLeft_tendsto_strong
    {ι : Type*} {l : Filter ι} (T : ι → H →L[ℂ] H) (a : H →L[ℂ] H)
    {C : ℝ} (hT : ∀ i, ‖T i‖ ≤ C)
    (ha : ∀ x, Tendsto (fun i => T i x) l (𝓝 (a x)))
    (z : SpatialHilbert H K) :
    Tendsto (fun i => spatialLeft (K := K) (T i) z) l
      (𝓝 (spatialLeft (K := K) a z)) := by
  have hequi : Equicontinuous
      (fun i : ι => (spatialLeft (K := K) (T i) : SpatialHilbert H K → SpatialHilbert H K)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C * t)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0))))
    intro x y i
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    have hn : ‖spatialLeft (K := K) (T i)‖ ≤ C := by
      calc
        _ ≤ ‖T i‖ * ‖(1 : K →L[ℂ] K)‖ := spatialTensorOp_norm_le _ _
        _ ≤ ‖T i‖ * 1 := mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le : ‖(1 : K →L[ℂ] K)‖ ≤ 1) (norm_nonneg _)
        _ ≤ C := by simpa only [mul_one] using hT i
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (spatialLeft (K := K) a).continuous
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      let L : H →L[ℂ] SpatialHilbert H K :=
        UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ H K).flip y)
      have h := L.continuous.continuousAt.tendsto.comp (ha x)
      change Tendsto (fun i => (((T i x) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K))
        l (𝓝 (((a x) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)) at h
      change Tendsto (fun i => spatialTensorOp (T i) (1 : K →L[ℂ] K) _) l
        (𝓝 (spatialTensorOp a (1 : K →L[ℂ] K) _))
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul, one_apply_eq_self] using h
    | add x y hx hy =>
      simpa only [map_add, UniformSpace.Completion.coe_add] using hx.add hy

end LeftContinuity

section Generated

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem spatialLeft_mem_generated_contraction
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialLeft (K := K) b ∈ A)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra B) (hn : ‖b‖ ≤ 1) :
    spatialLeft (K := K) b ∈ generatedVonNeumannAlgebra A := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (B : Set (H →L[ℂ] H))) := by
    change b ∈ (generatedVonNeumannAlgebra B : Set (H →L[ℂ] H)) at hb
    rwa [generatedVonNeumannAlgebra_coe] at hb
  obtain ⟨a, ha, hlim⟩ := hK.exists_strong_contraction_net B b hb' hn
  let c : Finset H × ℕ → Algebra (generatedVonNeumannAlgebra A) := fun d =>
    ⟨spatialLeft (K := K) (a d),
      subset_generatedVonNeumannAlgebra A (hBA _ (a d).property)⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := (atTop : Filter (Finset H × ℕ)))
    (generatedVonNeumannAlgebra A) c
  intro x y
  exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp
    (spatialLeft_tendsto_strong (fun d => (a d : H →L[ℂ] H)) b ha hlim x)

/-- The first-leg representation preserves membership in generated von Neumann algebras. -/
theorem spatialLeft_mem_generated
    (hK : PublishedKaplanskyDensity.{u})
    (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (SpatialHilbert H K →L[ℂ] SpatialHilbert H K))
    (hBA : ∀ b ∈ B, spatialLeft (K := K) b ∈ A)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra B) :
    spatialLeft (K := K) b ∈ generatedVonNeumannAlgebra A := by
  by_cases hzero : b = 0
  · rw [hzero, map_zero]
    exact (generatedVonNeumannAlgebra A).zero_mem
  have hp : 0 < ‖b‖ := norm_pos_iff.mpr hzero
  have hc : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hbn : ‖(‖b‖ : ℂ)⁻¹ • b‖ ≤ 1 := by
    simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp, inv_mul_cancel₀ hp.ne']
    exact le_rfl
  have hs := spatialLeft_mem_generated_contraction hK B A hBA
    ((‖b‖ : ℂ)⁻¹ • b) ((generatedVonNeumannAlgebra B).smul_mem hb _) hbn
  have hr := (generatedVonNeumannAlgebra A).smul_mem hs (‖b‖ : ℂ)
  rwa [← map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul] at hr

private theorem generated_of_vonNeumann (A : VonNeumannAlgebra H) :
    generatedVonNeumannAlgebra A.toStarSubalgebra = A := by
  apply le_antisymm
  · exact generatedVonNeumannAlgebra_le_of_le _ A le_rfl
  · exact subset_generatedVonNeumannAlgebra _

theorem spatialLeft_mem_of_generated
    (hK : PublishedKaplanskyDensity.{u}) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : VonNeumannAlgebra (SpatialHilbert H K))
    (hS : ∀ x ∈ S, spatialLeft (K := K) x ∈ Q)
    {x : H →L[ℂ] H} (hx : x ∈ generatedVonNeumannAlgebra S) :
    spatialLeft (K := K) x ∈ Q := by
  have h := spatialLeft_mem_generated hK S Q.toStarSubalgebra hS x hx
  rwa [generated_of_vonNeumann] at h

theorem spatialRight_mem_of_generated
    (hK : PublishedKaplanskyDensity.{u}) (S : StarSubalgebra ℂ (K →L[ℂ] K))
    (Q : VonNeumannAlgebra (SpatialHilbert H K))
    (hS : ∀ x ∈ S, spatialRight (H := H) x ∈ Q)
    {x : K →L[ℂ] K} (hx : x ∈ generatedVonNeumannAlgebra S) :
    spatialRight (H := H) x ∈ Q := by
  have h := spatialRight_mem_generated hK S Q.toStarSubalgebra hS x hx
  rwa [generated_of_vonNeumann] at h

end Generated

section Associativity

variable {H K L : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

private theorem assoc_left_left (a : H →L[ℂ] H) :
    (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
      (spatialLeft (K := L) (spatialLeft (K := K) a)) =
        spatialLeft (K := SpatialHilbert K L) a := by
  change (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
    (spatialTensorOp (spatialTensorOp a 1) 1) = spatialTensorOp a 1
  simpa only [Pureness.spatialTensorOp_one]
    using spatialAssociator_conjugate_tensor a (1 : K →L[ℂ] K) (1 : L →L[ℂ] L)

private theorem assoc_left_right (b : K →L[ℂ] K) :
    (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
      (spatialLeft (K := L) (spatialRight (H := H) b)) =
        spatialRight (H := H) (spatialLeft (K := L) b) := by
  exact spatialAssociator_conjugate_tensor (1 : H →L[ℂ] H) b (1 : L →L[ℂ] L)

private theorem assoc_right (c : L →L[ℂ] L) :
    (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
      (spatialRight (H := SpatialHilbert H K) c) =
        spatialRight (H := H) (spatialRight (H := K) c) := by
  change (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
    (spatialTensorOp 1 c) = spatialTensorOp 1 (spatialTensorOp 1 c)
  simpa only [Pureness.spatialTensorOp_one]
    using spatialAssociator_conjugate_tensor (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) c

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
private theorem mem_assoc_pullback
    (B : VonNeumannAlgebra (SpatialHilbert H (SpatialHilbert K L)))
    (T : SpatialHilbert (SpatialHilbert H K) L →L[ℂ]
      SpatialHilbert (SpatialHilbert H K) L) :
    T ∈ spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L)).symm B ↔
      (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv T ∈ B := by
  rw [mem_spatialTransportAlgebra]
  rfl

private theorem assoc_forward_le (hK : PublishedKaplanskyDensity.{u})
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L) :
    spatialProductAlgebra (spatialProductAlgebra M N) P ≤
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L)).symm
        (spatialProductAlgebra M (spatialProductAlgebra N P)) := by
  let Q := spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L)).symm
    (spatialProductAlgebra M (spatialProductAlgebra N P))
  apply generatedVonNeumannAlgebra_le_of_le
  apply sup_le
  · rintro _ ⟨a, ha, rfl⟩
    apply spatialLeft_mem_of_generated hK _ Q _ ha
    have hl : M.toStarSubalgebra.map (spatialLeft (K := K)) ≤
        Q.toStarSubalgebra.comap (spatialLeft (K := L)) := by
      rintro _ ⟨x, hx, rfl⟩
      apply (mem_assoc_pullback _ _).mpr
      change (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
        (spatialLeft (H := SpatialHilbert H K) (K := L)
          (spatialLeft (H := H) (K := K) x)) ∈
        spatialProductAlgebra M (spatialProductAlgebra N P)
      rw [assoc_left_left]
      exact spatialLeft_mem_product M (spatialProductAlgebra N P) hx
    have hr : N.toStarSubalgebra.map (spatialRight (H := H)) ≤
        Q.toStarSubalgebra.comap (spatialLeft (K := L)) := by
      rintro _ ⟨x, hx, rfl⟩
      apply (mem_assoc_pullback _ _).mpr
      change (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
        (spatialLeft (H := SpatialHilbert H K) (K := L)
          (spatialRight (H := H) (K := K) x)) ∈
        spatialProductAlgebra M (spatialProductAlgebra N P)
      rw [assoc_left_right]
      exact spatialRight_mem_product M (spatialProductAlgebra N P)
        (spatialLeft_mem_product N P hx)
    exact fun x hx => (sup_le hl hr) hx
  · rintro _ ⟨c, hc, rfl⟩
    apply (mem_assoc_pullback _ _).mpr
    change (spatialAssociator (H := H) (K := K) (L := L)).conjStarAlgEquiv
      (spatialRight (H := SpatialHilbert H K) (K := L) c) ∈
      spatialProductAlgebra M (spatialProductAlgebra N P)
    rw [assoc_right]
    exact spatialRight_mem_product M (spatialProductAlgebra N P)
      (spatialRight_mem_product N P hc)

private theorem conj_mem_transport {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (e : X ≃ₗᵢ[ℂ] Y) (M : VonNeumannAlgebra X) {T : X →L[ℂ] X} (hT : T ∈ M) :
    e.conjStarAlgEquiv T ∈ spatialTransportAlgebra e M := by
  apply (mem_spatialTransportAlgebra e M _).mpr
  simpa only [StarAlgEquiv.symm_apply_apply] using hT

private theorem assoc_left_mem
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L)
    {a : H →L[ℂ] H} (ha : a ∈ M) :
    spatialLeft (K := SpatialHilbert K L) a ∈
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
        (spatialProductAlgebra (spatialProductAlgebra M N) P) := by
  rw [← assoc_left_left]
  apply conj_mem_transport
  exact spatialLeft_mem_product (spatialProductAlgebra M N) P
    (spatialLeft_mem_product M N ha)

private theorem assoc_middle_mem
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L)
    {b : K →L[ℂ] K} (hb : b ∈ N) :
    spatialRight (H := H) (spatialLeft (K := L) b) ∈
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
        (spatialProductAlgebra (spatialProductAlgebra M N) P) := by
  rw [← assoc_left_right]
  apply conj_mem_transport
  exact spatialLeft_mem_product (spatialProductAlgebra M N) P
    (spatialRight_mem_product M N hb)

private theorem assoc_right_mem
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L)
    {c : L →L[ℂ] L} (hc : c ∈ P) :
    spatialRight (H := H) (spatialRight (H := K) c) ∈
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
        (spatialProductAlgebra (spatialProductAlgebra M N) P) := by
  rw [← assoc_right]
  apply conj_mem_transport
  exact spatialRight_mem_product (spatialProductAlgebra M N) P hc

private theorem assoc_inner_generators_mem
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L) :
    ∀ x ∈ (N.toStarSubalgebra.map (spatialLeft (K := L)) ⊔
      P.toStarSubalgebra.map (spatialRight (H := K))), spatialRight (H := H) x ∈
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
        (spatialProductAlgebra (spatialProductAlgebra M N) P) := by
  let R := spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
    (spatialProductAlgebra (spatialProductAlgebra M N) P)
  have hl : N.toStarSubalgebra.map (spatialLeft (K := L)) ≤
      R.toStarSubalgebra.comap (spatialRight (H := H)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact assoc_middle_mem M N P hb
  have hr : P.toStarSubalgebra.map (spatialRight (H := K)) ≤
      R.toStarSubalgebra.comap (spatialRight (H := H)) := by
    rintro _ ⟨c, hc, rfl⟩
    exact assoc_right_mem M N P hc
  exact fun x hx => (sup_le hl hr) hx

private theorem assoc_reverse_le (hK : PublishedKaplanskyDensity.{u})
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L) :
    spatialProductAlgebra M (spatialProductAlgebra N P) ≤
      spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
        (spatialProductAlgebra (spatialProductAlgebra M N) P) := by
  apply generatedVonNeumannAlgebra_le_of_le
  apply sup_le
  · rintro _ ⟨a, ha, rfl⟩
    exact assoc_left_mem M N P ha
  · rintro _ ⟨x, hx, rfl⟩
    exact spatialRight_mem_of_generated hK _ _ (assoc_inner_generators_mem M N P) hx

/-- The canonical tensor associator identifies the represented spatial products. -/
theorem spatialTransport_spatialProduct_assoc
    (hK : PublishedKaplanskyDensity.{u})
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) (P : VonNeumannAlgebra L) :
    spatialTransportAlgebra (spatialAssociator (H := H) (K := K) (L := L))
      (spatialProductAlgebra (spatialProductAlgebra M N) P) =
      spatialProductAlgebra M (spatialProductAlgebra N P) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact (mem_assoc_pullback _ _).mp (assoc_forward_le hK M N P ha)
  · exact assoc_reverse_le hK M N P

end Associativity

end

end KadisonKastler

end OAI
