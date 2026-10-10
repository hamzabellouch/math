import OAI.AlgebraicGeometry.PlaneCurves.ThetaMatrices

namespace OAI

/-!
# Scaled theta jet matrices and noncancellation
-/

section

/-! Parameter choices for the three-branch scalar jet matrix. The nine point
exponents x_i are converted to offsets 1/2−x_i in the theta products. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Nagata.W29

theorem exists_scaled_thetaJetMatrix_source_data
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < delta ∧ delta < 1 / 2 ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, sourceOffsets x i) = delta ∧
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        Nagata.FiniteExponents.firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
          j (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) ∧
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        Nagata.FiniteExponents.secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) ∧
      (Nagata.FiniteExponents.exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty ∧
      ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective
        (Nagata.Workers.W11.thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
          (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec := by
  obtain ⟨n, D, M, q, rho, a, h, lam, delta, eta, x,
    hn, hD, hM, hq, hDpos, hMpos, hqpos, hindex, hratio, hrhodef, hadef,
    hhdef, hhrho, hrhopos, hrhogap, hapos, hhpos, hcoef, hlam0, hlam1,
    hgap, hmargin, hdelta0, hdeltaHalf, hslack, hnonint1, hnonint2,
    hxinj, hxbounds, hxsum, hxsum2, heta, heta2⟩ :=
    Nagata.Workers.W05.exists_scaled_parameters r d m hr hm hlow hupp
  subst D
  subst M
  subst q
  subst a
  have hfirst := Nagata.Workers.W05.firstLower_nonintegral_of_fin
    (n * d) (n * m) (3 * (Real.sqrt r - 3)) delta
    (by simpa only [hhdef] using hnonint1)
  have hsecond := Nagata.Workers.W05.secondLower_nonintegral_of_fin
    (n * d) (n * m) (3 * (Real.sqrt r - 3)) delta
    (by simpa only [hhdef] using hnonint2)
  have hdegreeR : 3 * ((n * m : ℕ) : ℝ) < ((n * d : ℕ) : ℝ) := by
    linarith [hhdef, hhpos]
  have hdegreeZ : 3 * ((n * m : ℕ) : ℤ) < ((n * d : ℕ) : ℤ) := by
    exact_mod_cast hdegreeR
  have hnonempty := Nagata.FiniteExponents.exponentSet_nonempty
    (by positivity : (0 : ℤ) ≤ ((n * m : ℕ) : ℤ)) hdegreeZ
    (hfirst 0 le_rfl (by positivity))
  refine ⟨n, delta, x, hn, hdelta0, hdeltaHalf, hxinj, hxbounds,
    sourceOffsets_sum x delta hxsum, hfirst, hsecond, hnonempty, ?_⟩
  exact Nagata.Workers.W11.eventually_injective_thetaJetMatrix
    ((n * d : ℕ) : ℤ) (r - 9) (n * m) rho (3 * (Real.sqrt r - 3)) delta lam
    hapos hMpos hrhopos.le hdelta0.le hlam0 hlam1
    (by simpa only [Int.cast_natCast] using hhdef.symm.trans hhrho)
    hslack hcoef hmargin (sourceOffsets x)
    (fun i => (sourceOffsets_bounds x hxbounds i).1)
    (fun i => lt_trans (sourceOffsets_bounds x hxbounds i).2 (by norm_num))

/-- A shorter consequence of the full simultaneous source-data package. -/
theorem exists_scaled_thetaJetMatrix_injective
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < delta ∧ delta < 1 / 2 ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, sourceOffsets x i) = delta ∧
      ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective
        (Nagata.Workers.W11.thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
          (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec := by
  obtain ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum,
    hfirst, hsecond, hnonempty, hinj⟩ :=
    exists_scaled_thetaJetMatrix_source_data r d m hr hm hlow hupp
  exact ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum, hinj⟩

/-- An eventual nonzero kernel contradicts injectivity for the selected scalar matrix. -/
theorem exists_scaled_thetaJetMatrix_kernel_obstruction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < delta ∧ delta < 1 / 2 ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, sourceOffsets x i) = delta ∧
      ¬ (∀ᶠ τ in 𝓝[>] (0 : ℝ), ∃ v :
        Nagata.FiniteExponents.Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
          (3 * (Real.sqrt r - 3)) delta → ℂ,
        v ≠ 0 ∧
          (Nagata.Workers.W11.thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
            (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec v = 0) := by
  obtain ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum, hinj⟩ :=
    exists_scaled_thetaJetMatrix_injective r d m hr hm hlow hupp
  refine ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum, ?_⟩
  intro hkernel
  obtain ⟨τ, ht, v, hv, hzero⟩ := (hinj.and hkernel).exists
  exact hv (ht (by simpa only [Matrix.mulVec_zero] using hzero))

end Nagata.W29

end
end

end OAI
