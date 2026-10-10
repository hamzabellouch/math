import OAI.Analysis.KadisonKastler.CStarCommutatorClosure
import OAI.Analysis.KadisonKastler.DerivationStarReduction
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! # Spatial derivations pass to the bicommutant

Kaplansky's constructed bounded net transfers commutator membership to
the represented closure. Central projections in that closure therefore
commute with the spatial implementer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatial_commutator_mem_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    T * b - b * T ∈ generatedVonNeumannAlgebra S := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  let c (d : Finset H × ℕ) : Algebra (generatedVonNeumannAlgebra S) :=
    ⟨T * (a d).val - (a d).val * T, hS (a d)⟩
  apply Generator.Tracial.weak_operator_limit_mem (ι := Finset H × ℕ) (l := atTop)
    (generatedVonNeumannAlgebra S) c
    (T * b - b * T)
  intro ξ η
  have hlim : Tendsto (fun d => T ((a d).val ξ) - (a d).val (T ξ)) atTop
      (𝓝 (T (b ξ) - b (T ξ))) :=
    (T.continuous.tendsto _ |>.comp (ht ξ)).sub (ht (T ξ))
  exact (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) hlim

theorem spatial_commutator_mem_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) :
    T * b - b * T ∈ generatedVonNeumannAlgebra S := by
  let c : ℝ := ‖b‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let V := (generatedVonNeumannAlgebra S).toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars ℝ
  have hb' : (c⁻¹ : ℝ) • b ∈ generatedVonNeumannAlgebra S := V.smul_mem c⁻¹ hb
  have hn : ‖(c⁻¹ : ℝ) • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← div_eq_inv_mul]
    exact (div_le_one hc).mpr (by dsimp [c]; linarith)
  have h := spatial_commutator_mem_generated_contraction S T hS _ hb' hn
  have he : T * (c⁻¹ • b) - (c⁻¹ • b) * T = c⁻¹ • (T * b - b * T) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [he] at h
  exact (V.smul_mem_iff (inv_ne_zero hc.ne')).mp h

theorem spatial_commutator_central_projection
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hpN : p ∈ generatedVonNeumannAlgebra S)
    (hc : ∀ a ∈ generatedVonNeumannAlgebra S, Commute p a) : Commute T p := by
  let D : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    { toFun := fun x => T * x - x * T
      map_add' := by intro x y; noncomm_ring
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub]
      cont := (continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const) }
  have hD : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    change T * (x * y) - (x * y) * T =
      (T * x - x * T) * y + x * (T * y - y * T)
    noncomm_ring
  have hmem := spatial_commutator_mem_generated_contraction S T hS p hpN (hp.norm_le _)
  have hzero := derivation_central_idempotent_eq_zero D hD p
    hp.isIdempotentElem.eq (hc _ hmem)
  exact sub_eq_zero.mp hzero

end

end KadisonKastler

end OAI
