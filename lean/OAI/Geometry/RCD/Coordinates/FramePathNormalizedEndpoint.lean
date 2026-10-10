import OAI.Geometry.RCD.Coordinates.NormalizedFrameEndpoint

namespace OAI

/-! # Normalized scalar endpoints from the actual spatial frame error -/

open Set Filter MeasureTheory Metric Finset
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem frame_path_normalized_endpoint (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ Q) (g : SobolevSpace μ Q)
    (γ : C(Time,X)) (b : Fin n → ℝ → ℝ) (v : X → Euclidean n) (φ : X → ℝ)
    {r L α : ℝ} (hr : 0<r) (hspeed : dist (γ 0) (γ 1)≤r)
    (hf : AbsolutelyContinuousOnInterval (fun t => φ (geodesicExtension γ t)) 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hc : ∀ i, AbsolutelyContinuousOnInterval (fun t => v (geodesicExtension γ t) i) 0 1)
    (haff : ∀ i (t : Time), |(v (γ t) i-((1-(t:ℝ))*v (γ 0) i+(t:ℝ)*v (γ 1) i))/r|≤α)
    (hbe : ∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun t => localGamma μ Q (u i) g (geodesicExtension γ t))
    (hg : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), localGamma μ Q g g (geodesicExtension γ t)≤L^2)
    (hEI : IntegrableOn (fun t => frameVelocityError μ Q u g (geodesicExtension γ t)) (Icc (0:ℝ) 1))
    (hd : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv (fun s => φ (geodesicExtension γ s)) t-
        ∑ i, localGamma μ Q (u i) g (geodesicExtension γ t)*
          deriv (fun s => v (geodesicExtension γ s) i) t)^2≤
        (dist (γ 0) (γ 1))^2*frameVelocityError μ Q u g (geodesicExtension γ t)) :
    let e := ∫ t in Icc (0:ℝ) 1, frameVelocityError μ Q u g (geodesicExtension γ t)
    |φ (γ 1)-φ (γ 0)|/r≤Real.sqrt (L^2+e)*(dist (v (γ 0)) (v (γ 1))/r)+
      α*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+Real.sqrt e := by
  have he0 : geodesicExtension γ 0=γ 0 := geodesicExtension_eq γ (0:Time)
  have he1 : geodesicExtension γ 1=γ 1 := geodesicExtension_eq γ (1:Time)
  have hnorm := frame_path_coefficient_norm_bound μ Q u g γ b hbe hg
  have hd' : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv (fun s => φ (geodesicExtension γ s)) t-
        ∑ i, b i t*deriv (fun s => v (geodesicExtension γ s) i) t)^2≤
        (dist (γ 0) (γ 1))^2*frameVelocityError μ Q u g (geodesicExtension γ t) := by
    have he := (ae_restrict_iff' measurableSet_Icc).mp (ae_all_iff.mpr hbe)
    filter_upwards [hd,he] with t ht he htI
    simpa only [fun i => he (Ioo_subset_Icc_self htI) i] using ht htI
  have haff' (i : Fin n) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |(v (geodesicExtension γ t) i-((1-t)*v (geodesicExtension γ 0) i+
        t*v (geodesicExtension γ 1) i))/r|≤α := by
    have het : geodesicExtension γ t=γ (⟨t,ht⟩ : Time) := geodesicExtension_eq γ ⟨t,ht⟩
    simpa only [het,he0,he1] using haff i ⟨t,ht⟩
  have hh := normalized_frame_endpoint hr dist_nonneg hspeed hf hb hc haff'
    (fun t => frameVelocityError μ Q u g (geodesicExtension γ t))
    (fun _ => frameVelocityError_nonneg μ Q u g _) hEI hnorm hd'
  have hn : ‖(WithLp.toLp 2 (fun i => (v (γ 1) i-v (γ 0) i)/r) : Euclidean n)‖=
      dist (v (γ 0)) (v (γ 1))/r := by
    have hvect : (WithLp.toLp 2 (fun i => (v (γ 1) i-v (γ 0) i)/r) : Euclidean n)=
        r⁻¹ • (v (γ 1)-v (γ 0)) := by
      apply PiLp.ext
      intro i
      simp only [PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,div_eq_inv_mul]
    rw [hvect,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),dist_eq_norm_sub']
    ring
  simpa only [he0,he1,hn] using hh

end RegularPointCoordinates

end

end OAI
