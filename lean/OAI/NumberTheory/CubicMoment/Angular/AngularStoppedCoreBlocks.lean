import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedLowCoreMass
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLowCoreMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCoreHybrid
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeCutoffMass

namespace OAI

/-! Pointwise noncube mass for the actual stopped coefficient. The small
core uses its proved prime cancellation and every other core uses the
ordinary/cubic sieve with the literal squarefree coefficient row. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_noncube_core_blocks
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 65536 ≤ b →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ X^2 → 8*B ≤ b^(3/4:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
        K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        K₁*((largeCoreDyadicIndices ((Real.log X)^a) B).card:ℝ)*B^(1/3:ℝ)*
          (b*(((Real.log X)^a)/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
  obtain ⟨K₀,hK₀,hlow⟩ := angular_stopped_low_core_mass (ι := ι) (d := 1)
    hpnt hEF ℓ hℓ hξ hξz hκ hH hF hJ a k ha
  obtain ⟨M,hM,henergy⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨K₀,18*K*M^2,hK₀,by positivity,?_⟩
  filter_upwards [hlow,henergy,eventually_ge_atTop (Real.exp 1)]
    with X hlow henergy hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let U := (Real.log X)^a
  let I := largeCoreDyadicIndices U B
  let T := stoppedIntervalSupport ι X l b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected
  let f := fun v => ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e‖^2
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hlog : 0 < Real.log X := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (by simpa using Real.log_le_log (Real.exp_pos 1) hX)
  have hbpos : 0 < b := by linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hU : 0 < U := pow_pos hlog a
  have hroot : B^(1/3:ℝ) ≤ X^(1:ℝ) := by
    simpa using cube_cutoff_le_length hB0 hX1 hBX
  have hsmall : (∑ v ∈ S.filter (fun v => v ∈ lowNoncubeSupport U (B^(1/3:ℝ))), f v) ≤
      K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k := by
    exact hlow δ l b u V (B^(1/3:ℝ)) hδ hδone hwidth hl hb hbX hV hu hVF
      (Real.rpow_nonneg hB0 _) hroot W hW hWi hWd _
      (fun v hv => (Finset.mem_filter.mp hv).2) e he hNe j₀ k₀ h Z Q early
  have henergy' : (∑ n ∈ T, ‖β n‖^2) ≤ 18*b*M^2 :=
    (henergy W hW selected u l b e hbpos.le hbX).2
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      (∑ v ∈ coreDyadicBlock B z.1 z.2, f v) ≤
        (18*K*M^2)*B^(1/3:ℝ)*(b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
    have hz' := (Finset.mem_filter.mp hz).2
    have hm := hcore T (coreDyadicBlock B z.1 z.2) β b B U z.1 z.2
      hbmin hB0 hU (fun n hn => stoppedIntervalSupport_spec X l b e hn) hz'.1.le
      ((mul_le_mul_of_nonneg_left hz'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    have heq (v : Eisenstein) : (∑ n ∈ T, β n*cubicSymbol n v) =
        angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e :=
      rfl
    simp_rw [heq] at hm
    apply hm.trans
    have hnonneg : 0 ≤ K*B^(1/3:ℝ)*(b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ)) := by
      positivity
    exact (mul_le_mul_of_nonneg_left henergy' hnonneg).trans_eq (by ring)
  have hlarge : (∑ z ∈ I, ∑ v ∈ coreDyadicBlock B z.1 z.2, f v) ≤
      (18*K*M^2)*(I.card:ℝ)*B^(1/3:ℝ)*
        (b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
    apply (Finset.sum_le_sum hrow).trans_eq
    rw [Finset.sum_const,nsmul_eq_mul]
    ring
  exact (noncube_frequency_mass_split S hS f (fun _ => sq_nonneg _)).trans
    (add_le_add hsmall hlarge)

end CubicFirstMoment

end

end OAI
