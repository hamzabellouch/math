import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolevPointwise

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile211
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_lipschitz {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f : X → ℝ} {Lf : ℝ≥0} (hLf : LipschitzWith Lf f)
    (hf : Sobolev (exponentialMeasure m (fun x => a*F x)) f)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : X → ℝ,
      LipschitzWith ⟨Real.exp (-(K-a*CG)*T)*(Lf:ℝ),by positivity⟩ g ∧
      g =ᵐ[exponentialMeasure m (fun x => a*F x)] cheegerHeat h T (hf.1.toLp f) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let u := hf.1.toLp f
  have hu : Sobolev ν (u : X → ℝ) := (sobolev_congr_ae hf.1.coeFn_toLp).mpr hf
  have hD : ∀ᵐ x ∂ν,|weakGradient ν f x| ≤ (Lf:ℝ) := by
    filter_upwards [weakGradient_le_lipschitz hnfin hLf,weakGradient_nonneg (m := ν) f] with x hx hn
    rwa [abs_of_nonneg hn]
  have hΓf : MemLp (gamma ν f f) 2 ν :=
    (memLp_mul_bounded hf.2.2 hf.2.2.aestronglyMeasurable hD).ae_eq (by
      filter_upwards [gamma_self (m := ν) f] with x hx
      simp only [hx,pow_two]
      rfl)
  have hge := gamma_congr_ae (m := ν) hf.1.coeFn_toLp hf.1.coeFn_toLp
  have hΓ : MemLp (gamma ν (u : X → ℝ) u) 2 ν := hΓf.ae_eq hge.symm
  have hΓb : ∀ᵐ x ∂ν, |hΓ.toLp _ x| ≤ (Lf:ℝ)^2 := by
    filter_upwards [hΓ.coeFn_toLp,hge,gamma_self (m := ν) f,hD] with x hx he hs hb
    rw [hx,he,hs,abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Lf.coe_nonneg).mpr hb
  have H := hHess.rcd_weighted_heat_gradient_sobolev_pointwise hN hrcd hfull hfin o hF hFb hGb hGc ha h hu hΓ hT
  have hHB := cheegerHeat_bounded h hT (sq_nonneg (Lf:ℝ)) (hΓ.toLp _) hΓb
  have hID := fun g hg => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := g) hg
  have hfd := (identified_sobolev_iff_energy hnfin hID).mp hu
  have hheatf : Sobolev ν (cheegerHeat h T u) := (identified_sobolev_iff_energy hnfin hID).mpr
    (((cheeger_closedQuadraticEnergy h).heat_energy_le ν hT u).trans_lt hfd)
  apply hrcd.weighted_sobolev_to_lipschitz hN hfull hfin hVB hheatf.2.1.1
    (weakGradient_isMinimal hheatf.2.1.2).1
  filter_upwards [H,hHB,gamma_self (m := ν) (cheegerHeat h T u : X → ℝ),
    weakGradient_nonneg (m := ν) (cheegerHeat h T u : X → ℝ)] with x hx hb he hn
  change weakGradient ν (cheegerHeat h T u : X → ℝ) x ≤ Real.exp (-(K-a*CG)*T)*(Lf:ℝ)
  rw [he] at hx
  have hb' := (le_abs_self _).trans hb
  have hs : (weakGradient ν (cheegerHeat h T u : X → ℝ) x)^2 ≤
      (Real.exp (-(K-a*CG)*T)*(Lf:ℝ))^2 := by
    calc
      _ ≤ Real.exp (-(2*(K-a*CG))*T)*(Lf:ℝ)^2 :=
        hx.trans (mul_le_mul_of_nonneg_left hb' (Real.exp_pos _).le)
      _ = _ := by
        rw [mul_pow,pow_two (Real.exp _),← Real.exp_add]
        congr 2
        ring
  exact (sq_le_sq₀ hn (by positivity)).mp hs
end WeakHessian

end
end InlinedFile211

end OAI
