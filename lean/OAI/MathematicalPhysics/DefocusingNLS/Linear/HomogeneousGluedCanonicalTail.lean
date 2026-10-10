import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedTail
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHolomorphicSingularLimit

namespace OAI

/-! All physical derivatives of a canonical outgoing linear combination. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ
local notation "E₄" => V × V

theorem homogeneousGlued_canonical_tail_bound
    (ν eta b : ℂ) (m : ℕ) (L : ℝ) (hX : HasRadialExterior ν m b L)
    (lam : ℂ) (Yp Ym : ℂ → ℝ → E₄)
    (hp : IsCanonicalHolomorphicColumn ν eta b m L (1, 0) Yp)
    (hm : IsCanonicalHolomorphicColumn ν eta b m L (0, 1) Ym)
    (U : ℝ → E₄) (hU : ContDiffOn ℝ ∞ U (Ioi 0))
    (R : ℝ) (hR : 0 < R) (c d : ℂ)
    (ho : ∀ r, R ≤ r → U r =
      c • spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Yp lam) r +
        d • spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Ym lam) r)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop,
      ‖iteratedDeriv N (fun r => ((U r).1.1, (U r).2.1)) r‖ ≤
        C * r ^ ((ν - 2 * lam).re - (N : ℝ)) := by
  obtain ⟨hpp, hpm⟩ := homogeneous_canonical_circular_value_logJets
    ν (ν - 2 * lam) (star ν - 2 * lam) eta b m L hX (Yp lam) (1, 0)
    (hp.1 lam) (hp.2.1 lam) (hp.2.2.2 lam)
  obtain ⟨hmp, hmm⟩ := homogeneous_canonical_circular_value_logJets
    ν (ν - 2 * lam) (star ν - 2 * lam) eta b m L hX (Ym lam) (0, 1)
    (hm.1 lam) (hm.2.1 lam) (hm.2.2.2 lam)
  let f := fun t => c * (Yp lam t).1.1 + d * (Ym lam t).1.1
  let g := fun t => c * (Yp lam t).2.1 + d * (Ym lam t).2.1
  apply homogeneousGlued_physical_derivative_bound (ν - 2 * lam) (star ν - 2 * lam)
    (ν - 2 * lam).re rfl (by simp only [Complex.sub_re,
      Complex.star_def, Complex.conj_re])
    (fun r => ((U r).1.1, (U r).2.1)) (hU.fst.fst.prodMk hU.snd.fst)
    f g ((hpp.const_mul c).add (hmp.const_mul d))
    ((hpm.const_mul c).add (hmm.const_mul d)) (Real.log R) _ N
  intro t ht
  have hr : R ≤ Real.exp t := by
    rw [← Real.exp_log hR]
    exact (Real.exp_lt_exp.mpr ht).le
  have hh := ho (Real.exp t) hr
  apply Prod.ext
  · have he := congrArg (fun W : E₄ => W.1.1) hh
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul,
      spectralPhysicalPair, spectralPhysicalJet, Real.log_exp] at he
    rw [he]
    dsimp only [f]
    ring
  · have he := congrArg (fun W : E₄ => W.2.1) hh
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, smul_eq_mul,
      spectralPhysicalPair, spectralPhysicalJet, Real.log_exp] at he
    rw [he]
    dsimp only [g]
    ring

theorem homogeneousGlued_coordinate_derivatives (F : ℝ → V)
    (hF : ContDiffOn ℝ ∞ F (Ioi 0)) (N : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖iteratedDeriv N (fun r => (F r).1) r‖ ≤ ‖iteratedDeriv N F r‖ ∧
      ‖iteratedDeriv N (fun r => (F r).2) r‖ ≤ ‖iteratedDeriv N F r‖ := by
  have hs := (hF r hr).contDiffAt (Ioi_mem_nhds hr)
  have hp := (ContinuousLinearMap.fst ℝ ℂ ℂ).norm_iteratedFDeriv_comp_left hs
    (by simp : (N : ℕ∞ω) ≤ ∞)
  have hm := (ContinuousLinearMap.snd ℝ ℂ ℂ).norm_iteratedFDeriv_comp_left hs
    (by simp : (N : ℕ∞ω) ≤ ∞)
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Function.comp_def,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.norm_fst, ContinuousLinearMap.norm_snd, one_mul] using And.intro hp hm

end DefocusingNLS

end OAI
