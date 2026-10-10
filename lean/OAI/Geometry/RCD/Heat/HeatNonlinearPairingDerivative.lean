import OAI.Geometry.RCD.Harmonic.NonlinearPairingVariation
import OAI.Geometry.RCD.Heat.HeatScalarLaplacianPairing

namespace OAI

/-! # Nonlinear forward/backward heat pairing

The two generator terms cancel by the actual weak Laplacian chain rule.
Only the second scalar derivative times the gradient square remains.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_nonlinear_pairing_hasDerivAt
    {Φ φ ψ : ℝ → ℝ} {C D : ℝ≥0} (hΦ : LipschitzWith C Φ) (hΦ0 : Φ 0=0)
    (hφ : LipschitzWith D φ) (hφ0 : φ 0=0) (hψ : Continuous ψ)
    (hdΦ : ∀ a, HasDerivAt Φ (φ a) a) (hdφ : ∀ a, HasDerivAt φ (ψ a) a)
    (B E : ℝ≥0) (hB : ∀ a, |φ a| ≤ B) (hE : ∀ a, |ψ a| ≤ E)
    (f w : Lp ℝ 2 μ) (M : ℝ≥0) (hw : ∀ᵐ x ∂μ, |w x| ≤ M)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ
      (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x ≤ L) :
    HasDerivAt (fun s => inner ℝ (heatAt μ hQ s w)
      (hΦ.compLp hΦ0 (heatAt μ hQ (T-s) f)))
      (∫ x, heatAt μ hQ t w x * (ψ (heatAt μ hQ (T-t) f x) *
        localGamma μ hQ (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f)
          (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x) ∂μ) t := by
  let U := heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f
  let F := heatAt μ hQ (T-t) f
  let W := heatAt μ hQ t w
  let d := heatGeneratorAt μ hQ (T-t) f
  have hWb : ∀ᵐ x ∂μ, |W x| ≤ M := heatAt_abs_le_const μ hQ t M w hw
  have hW : MemLp W ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable W) M
    (by simpa only [Real.norm_eq_abs] using hWb)
  let θ := hW.toLp W
  have hθ : θ =ᵐ[μ] W := hW.coeFn_toLp
  have hθb : ∀ᵐ x ∂μ, |θ x| ≤ M := by
    filter_upwards [hθ,hWb] with x hx hb
    simpa only [hx] using hb
  have hback : HasDerivAt (fun s => heatAt μ hQ (T-s) f) d t := by
    have hh := (heatAt_hasDerivAt μ hQ (T-t) (sub_pos.mpr htT) f).scomp t
      ((hasDerivAt_const t T).sub (hasDerivAt_id t))
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hh
  have hder := nonlinear_pairing_hasDerivAt μ hback (heatAt_hasDerivAt μ hQ t ht w)
    θ M hθb hθ hΦ hΦ0 hdΦ hφ hφ0
  have hUd : IsWeakLaplacian μ hQ U (-d) := by
    simpa only [U,d,heatGeneratorAt_of_pos μ hQ (T-t) (sub_pos.mpr htT)] using
      heatSobolev_weak_laplacian μ hQ (T-t) (sub_pos.mpr htT) f
  have hfirst := heat_scalar_inner_laplacian μ hQ U (-d) hUd L hL
    hΦ hΦ0 hφ hφ0 hψ hdΦ hdφ B E hB hE w ht
  simp only [U,heatSobolev_toLp] at hfirst
  have hi : Integrable (fun x => W x*(φ (F x)*d x)) μ := by
    have hbase := (Lp.memLp (hφ.compLp hφ0 F)).integrable_mul (Lp.memLp d)
    have heq : (fun x => φ (F x)*d x) =ᵐ[μ] fun x => hφ.compLp hφ0 F x*d x := by
      filter_upwards [hφ.coeFn_compLp hφ0 F] with x hx
      exact congrArg (fun z : ℝ => z*d x) hx.symm
    exact (hbase.congr heq.symm).bdd_mul (Lp.aestronglyMeasurable W)
      (by simpa only [Real.norm_eq_abs] using hWb)
  have hj : Integrable (fun x => W x*(ψ (F x)*localGamma μ hQ U U x)) μ :=
    ((localGamma_memL1 μ hQ U U).bdd_mul
      (hψ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hE (F x))).bdd_mul
      (Lp.aestronglyMeasurable W) (by simpa only [Real.norm_eq_abs] using hWb)
  have hsum : (∫ x, W x*(φ (F x)*(-d) x+ψ (F x)*localGamma μ hQ U U x) ∂μ) =
      -(∫ x, W x*(φ (F x)*d x) ∂μ)+(∫ x, W x*(ψ (F x)*localGamma μ hQ U U x) ∂μ) := by
    calc
      _ = ∫ x, -(W x*(φ (F x)*d x))+W x*(ψ (F x)*localGamma μ hQ U U x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_neg d] with x hx
        simp only [hx,Pi.neg_apply]
        ring
      _ = (∫ x, -(W x*(φ (F x)*d x)) ∂μ)+
          (∫ x, W x*(ψ (F x)*localGamma μ hQ U U x) ∂μ) := by
        simpa only [Pi.neg_apply] using integral_add hi.neg hj
      _ = _ := by rw [integral_neg]
  have hsecond : inner ℝ d (lpMultiplier μ θ (hφ.compLp hφ0 F)) =
      ∫ x, W x*(φ (F x)*d x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ θ (hφ.compLp hφ0 F),hθ,hφ.coeFn_compLp hφ0 F] with x hp hx hf
    simp only [Real.inner_apply,hp,hx,hf,Function.comp_apply]
    ring
  rw [hfirst] at hder
  change HasDerivAt _ ((∫ x, W x*(φ (F x)*(-d) x+ψ (F x)*localGamma μ hQ U U x) ∂μ)+
    inner ℝ d (lpMultiplier μ θ (hφ.compLp hφ0 F))) t at hder
  rw [hsum,hsecond] at hder
  convert hder using 1; ring

end RegularPointCoordinates

end

end OAI
