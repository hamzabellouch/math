import OAI.Analysis.KadisonKastler.TracialSpectralAveraging

namespace OAI

/-! # Scalar norm averaging in diffuse finite factors -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

variable (τ : TracialRepresentation M)
  (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
    ∃ z : ℂ, c = z • (1 : Algebra M))
  (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

include τ hfactor hdiff in
/-- Round a finite spectral partition, then average all rounded pieces and
their common small remainder in one full matrix algebra. -/
theorem exists_tracial_spectral_scalar_average
    (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply (∑ i, c i • (Q.piece i).val.val) - z • (1 : H →L[ℂ] H)‖ < ε := by
  classical
  let C : ℝ := ∑ i, ‖c i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let D := C * (Q.size : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hε hD)
  let n := k + 1
  have hn : 0 < n := Nat.succ_pos k
  have hsmall : C * ((Q.size : ℝ) * (n : ℝ)⁻¹) < ε := by
    have hk' : (n : ℝ)⁻¹ * D < ε :=
      (lt_div_iff₀ hD).mp (by simpa only [n, Nat.cast_add, Nat.cast_one, one_div] using hk)
    have hn0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    dsimp [D] at hk'
    nlinarith
  obtain ⟨R, hsize, ht, J, _, hsub, herr⟩ :=
    exists_uniform_trace_approximation τ hdiff Q n hn
  have hR : 0 < R.size := by omega
  let : Nonempty (Fin R.size) := ⟨⟨0, hR⟩⟩
  obtain ⟨E, hdiag, _⟩ := exists_matrixAlgebra_for_unit_partition τ hfactor R hR
    (fun i j => (ht i).trans (ht j).symm)
  let q (i : Fin Q.size) := matrixDiagonalCut E (J i)
  have hqval (i : Fin Q.size) : (q i).val = ∑ j ∈ J i, (R.piece j).val := by
    simp only [q, matrixDiagonalCut, hdiag]
  have hq (i : Fin Q.size) : q i ≤ Q.piece i := by
    change (Q.piece i).val * (q i).val = (q i).val
    rw [hqval]
    exact hsub i
  have hr : (τ.trace (partitionRemainder Q q hq).val).re ≤ Q.size * (n : ℝ)⁻¹ := by
    apply partitionRemainder_trace_le
    intro i
    rw [hqval]
    exact (herr i).le
  obtain ⟨A, z, hA⟩ := exists_scalar_average_of_rounded_partition τ Q q hq E
    (fun i => matrixDiagonalCut_mem E (J i)) c ((Q.size : ℝ) * (n : ℝ)⁻¹) hr
  exact ⟨A, z, hA.trans_lt hsmall⟩

include τ hfactor hdiff in
/-- Normal elements of a represented diffuse finite factor have scalar
finite averages converging in operator norm. -/
theorem exists_tracial_normal_scalar_average (x : Algebra M) [IsStarNormal x]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply x.val - z • (1 : H →L[ℂ] H)‖ < ε := by
  obtain ⟨Q, c, hxc⟩ := exists_normal_spectral_approximation x (ε / 2) (by positivity)
  obtain ⟨A, z, hA⟩ := exists_tracial_spectral_scalar_average τ hfactor hdiff Q c
    (ε / 2) (by positivity)
  have hxc' : ‖x.val - ∑ i, c i • (Q.piece i).val.val‖ < ε / 2 := by
    let L : Algebra M →ₗ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
    have he : (∑ i, c i • (Q.piece i).val : Algebra M).val =
        ∑ i, c i • (Q.piece i).val.val := by
      change L (∑ i, c i • (Q.piece i).val) = _
      rw [map_sum]
      simp only [L.map_smul]
      rfl
    change ‖x.val - (∑ i, c i • (Q.piece i).val : Algebra M).val‖ < ε / 2 at hxc
    rwa [he] at hxc
  refine ⟨A, z, ?_⟩
  have h := norm_sub_le_norm_sub_add_norm_sub (A.apply x.val)
    (A.apply (∑ i, c i • (Q.piece i).val.val)) (z • (1 : H →L[ℂ] H))
  have hdiff := A.norm_apply_sub_le x.val (∑ i, c i • (Q.piece i).val.val)
  linarith

end

end KadisonKastler

end OAI
