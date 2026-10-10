import OAI.Geometry.RCD.Transport.SobolevHamiltonJacobiPlan

namespace OAI

/-! # The correctly scaled action bound between two prescribed times

Rescaling both time and the potential preserves the Hamilton--Jacobi
inequality and yields the inverse-time factor in the endpoint cost.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem sobolev_hamilton_jacobi_endpoint_comparison
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {a b : ℝ} (hab : a < b) {S : Set X} (hS : MeasurableSet S)
    (hs : ∀ t : Time, ∀ᵐ γ ∂π, γ t ∈ S)
    (u : ℝ → SobolevSpace μ Q) (hu : ContinuousOn u (Icc a b))
    (D : ℝ → Lp ℝ 2 μ)
    (hder : ∀ t ∈ Icc a b, HasDerivAt (fun s => SobolevSpace.toLp μ Q (u s)) (D t) t)
    (hgrad : ∀ t ∈ Icc a b, ∀ᵐ x ∂μ.restrict S,
      (SobolevSpace.minimalSlope μ Q (u t) x)^2 ≤ 2*D t x) :
    (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u a) (γ 0) ∂π) -
      (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u b) (γ 1) ∂π) ≤
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/(2*(b-a)) := by
  let c := b-a
  have hc : 0 < c := sub_pos.mpr hab
  let τ := fun t : ℝ => a+c*t
  have hτ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : τ t ∈ Icc a b := by
    dsimp only [τ,c]
    constructor <;> nlinarith [ht.1,ht.2]
  let v := fun t => c • u (τ t)
  let d := fun t => c^2 • D (τ t)
  have hv : ContinuousOn v (Icc (0:ℝ) 1) :=
    (hu.comp (by fun_prop : ContinuousOn τ (Icc (0:ℝ) 1)) hτ).const_smul c
  have hd (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      HasDerivAt (fun s => SobolevSpace.toLp μ Q (v s)) (d t) t := by
    have hτd : HasDerivAt τ c t := by
      simpa only [τ,mul_one,id_eq] using ((hasDerivAt_id t).const_mul c).const_add a
    have h := HasDerivAt.const_smul c ((hder (τ t) (hτ t (Ico_subset_Icc_self ht))).scomp t hτd)
    simpa only [v,d,map_smul,smul_smul,pow_two,Function.comp_def,Pi.smul_def] using h
  have hg (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ∀ᵐ x ∂μ.restrict S,
      (SobolevSpace.minimalSlope μ Q (v t) x)^2 ≤ 2*d t x := by
    have hp := hgrad (τ t) (hτ t (Ico_subset_Icc_self ht))
    dsimp only [v,d]
    rw [SobolevSpace.minimalSlope_smul_nonneg μ Q _ hc.le]
    filter_upwards [hp,ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.minimalSlope μ Q (u (τ t)))),
      ae_restrict_of_ae (Lp.coeFn_smul (c^2) (D (τ t)))] with x hx hs hd
    simp only [hs,hd,Pi.smul_apply,smul_eq_mul,mul_pow]
    nlinarith [sq_nonneg c]
  have hplan := sobolev_hamilton_jacobi_plan_comparison μ Q π hgeo hC hcomp hLength
    (a := 0) (b := 1) zero_le_one le_rfl le_rfl hS
    (fun t ht => by
      have htime : t ∈ Icc (0:ℝ) 1 := Ico_subset_Icc_self ht
      filter_upwards [hs ⟨t,htime⟩] with γ hγ
      rw [show geodesicExtension γ t = γ ⟨t,htime⟩ from geodesicExtension_eq γ ⟨t,htime⟩]
      exact hγ)
    v hv d hd hg
  have hv0 : v 0 = c • u a := by simp only [v,τ,mul_zero,add_zero]
  have hτ1 : τ 1 = b := by dsimp only [τ,c]; ring
  have hv1 : v 1 = c • u b := by simp only [v,hτ1]
  have he (w : SobolevSpace μ Q) (t : Time) :
      (∫ γ : C(Time,X), SobolevSpace.toLp μ Q (c • w) (γ t) ∂π) =
        c*(∫ γ : C(Time,X), SobolevSpace.toLp μ Q w (γ t) ∂π) := by
    rw [map_smul]
    have hae := ae_of_ae_map (measurable_path_eval t).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_eq
        (Lp.coeFn_smul c (SobolevSpace.toLp μ Q w)))
    calc
      _ = ∫ γ : C(Time,X), c*SobolevSpace.toLp μ Q w (γ t) ∂π := by
        apply integral_congr_ae
        filter_upwards [hae] with γ hγ
        simpa only [Pi.smul_apply,smul_eq_mul] using hγ
      _ = _ := integral_const_mul _ _
  have hz (γ : C(Time,X)) : geodesicExtension γ (0:ℝ) = γ (0:Time) := geodesicExtension_eq γ 0
  have ho (γ : C(Time,X)) : geodesicExtension γ (1:ℝ) = γ (1:Time) := geodesicExtension_eq γ 1
  simp only [hz,ho,hv0,hv1,he,sub_zero,one_mul] at hplan
  have hh : c*((∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u a) (γ 0) ∂π) -
      ∫ γ : C(Time,X), SobolevSpace.toLp μ Q (u b) (γ 1) ∂π) ≤
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/2 := by simpa only [mul_sub] using hplan
  apply (le_div_iff₀ (by positivity : 0 < 2*(b-a))).mpr
  dsimp only [c] at hh
  nlinarith

end RegularPointCoordinates

end

end OAI
