import OAI.MeasureTheory.Falconer.Shells.NormalizedHighShellError
import OAI.MeasureTheory.Falconer.Fourier.WeightedDistanceFourier

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def normalizedHighShellF (d : PositiveDistanceData) (n : ℕ) (v r : ℝ) : ℂ :=
  (d.levelMass^(-2:ℤ):ℝ) • ∫ z, d.normalizedHighShellKernel n v r
    (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))) z ∂d.cellPair

 theorem normalizedHighShellF_error_of_pointwise (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (n : ℕ) (v r ε : ℝ)
    (herr : ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
      ‖(d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
        d.normalizedHighShellKernel n v r
          (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))) (x,y)‖ ≤ ε) :
    Integrable (d.normalizedHighShellKernel n v r
      (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y)))) d.cellPair ∧
    ‖charFun d.weightedDistance r - d.normalizedHighShellF n v r‖ ≤
      d.levelMass^(-2:ℤ) * d.cellPair.real univ * ε := by
  let ψ := sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))
  let K := d.normalizedHighShellKernel n v r ψ
  let f : Plane × Plane → ℂ := fun z =>
    (d.spatialWeight z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ))
  have hfm : Measurable f := by
    apply Measurable.mul (Complex.measurable_ofReal.comp d.measurable_spatialWeight)
    fun_prop
  have hfb : ∀ᵐ z ∂d.cellPair, ‖f z‖ ≤ 1 := by
    filter_upwards [d.ae_cellPair_mem] with z hz
    have hw₀ := d.spatialWeight_nonneg hQ z
    have hw₁ := d.spatialWeight_le_one hQ hs hz.1 hz.2
    simpa [f,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw₀] using hw₁
  have hfi : Integrable f d.cellPair := Integrable.of_bound hfm.aestronglyMeasurable 1 hfb
  have hkm : Measurable K := (d.normalizedHighShellKernel_measurable n v ψ
    (measurable_sourceConeCircle _)).comp (f := fun z : Plane × Plane => (r,z))
      (measurable_const.prodMk measurable_id)
  have he : ∀ᵐ z ∂d.cellPair, ‖f z-K z‖ ≤ ε := by
    filter_upwards [d.ae_cellPair_mem] with z hz
    exact herr z.1 hz.1 z.2 hz.2
  have hki : Integrable K d.cellPair := by
    refine Integrable.of_bound hkm.aestronglyMeasurable (ε+1) ?_
    filter_upwards [he,hfb] with z hz hb
    calc
      ‖K z‖ = ‖(K z-f z)+f z‖ := by rw [sub_add_cancel]
      _ ≤ ‖K z-f z‖+‖f z‖ := norm_add_le _ _
      _ ≤ ε+1 := add_le_add (by simpa only [norm_sub_rev] using hz) hb
  refine ⟨hki,?_⟩
  have hfour : charFun d.weightedDistance r = (d.levelMass^(-2:ℤ):ℝ) • ∫ z, f z ∂d.cellPair := by
    rw [d.weightedDistance_fourier hQ]
    simp only [f,mul_comm Complex.I]
  rw [hfour,normalizedHighShellF,← smul_sub]
  change ‖(d.levelMass^(-2:ℤ):ℝ) • ((∫ z, f z ∂d.cellPair)-(∫ z, K z ∂d.cellPair))‖ ≤ _
  rw [← integral_sub hfi hki,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ d.levelMass^(-2:ℤ))]
  have hb := norm_integral_le_of_norm_le_const he
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ d.levelMass^(-2:ℤ))
  exact hh.trans_eq (by ring)

 theorem uniform_high_shell_fourier_error {sig T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ [IsFiniteMeasure d.ρ],
    N₀ ≤ d.N → d.sig = sig → 0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ‖charFun d.weightedDistance r - d.normalizedHighShellF n v r‖ ≤
      d.levelMass^(-2:ℤ) * d.cellPair.real univ * ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_normalized_high_shell_error (T := T) hsig
  refine ⟨n,N₀,?_⟩
  intro d inst hN hd hQ hs hq hqs hw ht v r hv hr
  exact (d.normalizedHighShellF_error_of_pointwise hQ hs n v r _
    (h₀ d hN hd hQ hs hq hqs hw ht v r hv hr)).2

end PositiveDistanceData

end PlanarFalconer

end OAI
