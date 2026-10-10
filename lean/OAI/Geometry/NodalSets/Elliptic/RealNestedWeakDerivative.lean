import OAI.Geometry.NodalSets.Elliptic.RealHilbertWeakLimit
import OAI.Geometry.NodalSets.Elliptic.RealInteriorDifferencePairingLemmas

namespace OAI

namespace Yau
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

theorem real_nested_weak_derivative_of_difference_bound
    (R r e : ℝ) (hr : r ≤ R) (he : 0 < e) (hem : e ≤ R-r)
    (u : Jets.Coord → ℝ) (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (i : Fin 4) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ h : ℝ, |h| ≤ e → MemLp (realDifferenceQuotient i h u) 2
      (volume.restrict (realCenteredCube 4 r)))
    (hb : ∀ h : ℝ, |h| ≤ e →
      (∫ x in realCenteredCube 4 r, (realDifferenceQuotient i h u x)^2) ≤ C) :
    ∃ H : Lp ℝ 2 (volume.restrict (realCenteredCube 4 r)), ‖H‖^2 ≤ C ∧
      ∀ psi : Jets.Coord → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
        tsupport psi ⊆ realCenteredCube 4 r →
        IntegrableOn (fun x ↦ u x*coordPartial psi x i) (realCenteredCube 4 r) ∧
        IntegrableOn (fun x ↦ H x*psi x) (realCenteredCube 4 r) ∧
        (∫ x in realCenteredCube 4 r, u x*coordPartial psi x i) =
          -(∫ x in realCenteredCube 4 r, H x*psi x) := by
  let h : ℕ → ℝ := fun n ↦ (e)*(1/((n:ℝ)+1))
  have hpos (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hh (n : ℕ) : |h n| ≤ e := by
    rw [abs_of_pos (hpos n)]
    dsimp [h]
    have hn : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    nlinarith
  have ht : Tendsto h atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (e:ℝ)
  have hneg : Tendsto (fun n ↦ -h n) atTop (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [neg_zero] using ht.neg,Filter.Eventually.of_forall (fun n ↦ ?_)⟩
    simpa using (neg_ne_zero.mpr (hpos n).ne')
  let W (n : ℕ) : Lp ℝ 2 (volume.restrict (realCenteredCube 4 r)) :=
    (hM (h n) (hh n)).toLp (realDifferenceQuotient i (h n) u)
  have hW (n : ℕ) : ‖W n‖ ≤ Real.sqrt C := by
    have hnorm : ‖W n‖^2 = ∫ x in realCenteredCube 4 r, (realDifferenceQuotient i (h n) u x)^2 :=
      real_toLp_norm_sq _ (hM (h n) (hh n))
    have hsq := hb (h n) (hh n)
    rw [← hnorm] at hsq
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (W n)]
  obtain ⟨H,hH,hpair⟩ := real_hilbert_bounded_pairing_limit W (Real.sqrt C) hW
  refine ⟨H,by nlinarith [Real.sq_sqrt hC,norm_nonneg H],?_⟩
  intro psi hp hc hs
  have hpsi : MemLp psi 2 (volume.restrict (realCenteredCube 4 r)) :=
    (real_compact_continuous_memLp psi hp.continuous hc).mono_measure Measure.restrict_le_self
  let test := hpsi.toLp psi
  have hlim := real_nested_difference_pairing_tendsto R r e hr hem u psi hu hp hc hs i h hh hneg
  have hinner (n : ℕ) : inner ℝ (W n) test =
      ∫ x in realCenteredCube 4 r, realDifferenceQuotient i (h n) u x*psi x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hM (h n) (hh n)).coeFn_toLp,hpsi.coeFn_toLp] with x hx hy
    change test x*W n x=_
    rw [hx,hy,mul_comm]
  have hid := hpair test (-(∫ x in realCenteredCube 4 r, u x*coordPartial psi x i))
    (by simpa only [hinner] using hlim)
  have hHrep : inner ℝ H test = ∫ x in realCenteredCube 4 r, H x*psi x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpsi.coeFn_toLp] with x hx
    change test x*H x=_
    rw [hx,mul_comm]
  rw [hHrep] at hid
  have hu' : MemLp u 2 (volume.restrict (realCenteredCube 4 r)) :=
    hu.mono_measure (Measure.restrict_mono (realCenteredCube_mono hr) le_rfl)
  have hdpsi : MemLp (fun x ↦ coordPartial psi x i) 2 (volume.restrict (realCenteredCube 4 r)) :=
    (real_compact_continuous_memLp _ (real_coordPartial_smooth psi hp i).continuous
      (hc.fderiv_apply ℝ (Pi.single i 1))).mono_measure Measure.restrict_le_self
  exact ⟨hu'.integrable_mul hdpsi,(Lp.memLp H).integrable_mul hpsi,by linarith only [hid]⟩

end
end Yau

end OAI
