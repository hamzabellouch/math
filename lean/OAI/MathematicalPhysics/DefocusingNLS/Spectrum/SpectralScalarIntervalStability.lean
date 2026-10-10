import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarCoefficientStability

namespace OAI

/-! Continuous dependence on any compact interval, in the coordinates used by
the turning-point rescaling. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_interval_stability
    (a b B delta M : ℝ) (hB : 0 ≤ B) (hd : 0 ≤ delta) (hM : 0 ≤ M)
    (V W : ℝ → ℂ) (q p : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hqD : ∀ t ∈ Icc a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hpD : ∀ t ∈ Icc a b, HasDerivAt p (spectralScalarField (W t) (p t)) t)
    (hV : ∀ t ∈ Icc a b, ‖V t‖ ≤ B)
    (hVW : ∀ t ∈ Icc a b, ‖W t - V t‖ ≤ delta)
    (hpb : ∀ t ∈ Icc a b, ‖p t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖q t - p t‖ ≤ (‖q a - p a‖ + delta * M / (1 + B)) *
      Real.exp ((1 + B) * (b - a)) := by
  have hmem (s : ℝ) (hs : s ∈ Icc 0 (b - a)) : a + s ∈ Icc a b := by
    constructor <;> linarith [hs.1,hs.2]
  have hc : ContinuousOn (fun s => a + s) (Icc 0 (b - a)) :=
    (continuous_const.add continuous_id).continuousOn
  have hqd (s : ℝ) (hs : s ∈ Icc 0 (b - a)) :
      HasDerivAt (fun z => q (a + z))
        (spectralScalarField (V (a + s)) (q (a + s))) s := by
    simpa only [Function.comp_def,one_smul,id_eq] using
      (hqD (a + s) (hmem s hs)).scomp s ((hasDerivAt_id s).const_add a)
  have hpd (s : ℝ) (hs : s ∈ Icc 0 (b - a)) :
      HasDerivAt (fun z => p (a + z))
        (spectralScalarField (W (a + s)) (p (a + s))) s := by
    simpa only [Function.comp_def,one_smul,id_eq] using
      (hpD (a + s) (hmem s hs)).scomp s ((hasDerivAt_id s).const_add a)
  have h := spectralScalar_coefficient_stability (b - a) B delta M hB hd hM
    (fun s => V (a + s)) (fun s => W (a + s))
    (fun s => q (a + s)) (fun s => p (a + s))
    (hq.comp hc hmem) (hp.comp hc hmem) hqd hpd
    (fun s hs => hV (a + s) (hmem s hs))
    (fun s hs => hVW (a + s) (hmem s hs))
    (fun s hs => hpb (a + s) (hmem s hs))
    (t - a) ⟨sub_nonneg.mpr ht.1,sub_le_sub_right ht.2 a⟩
  simpa only [add_zero,add_sub_cancel] using h

end DefocusingNLS

end OAI
