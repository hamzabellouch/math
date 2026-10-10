import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MaximumTemplateBound
import OAI.Analysis.BiholderTransport.Calculus.OuterDerivativeBound
import OAI.Analysis.BiholderTransport.Oscillation.NonpowerMaximum

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section ClassPower
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.class_power (hmtw:WeakMTW (n:=n) (M:=M)) (hn:0 < n)
    {lam cap:ℝ} (hlam:0 < lam) (hcap:lam ≤ cap) (x0:M)
    (hc:(densityDualClass (metricVolume n) lam cap x0).Nonempty) :
    HasPowerUpperBound (classOscillation (metricVolume n) lam cap x0) := by
  classical
  by_contra hno
  obtain ⟨B,hB,eps,heps,HB⟩:=hmtw.maximum_template_bound hn hlam hcap
  let M0:ℝ:=12*(Module.finrank ℝ (Model n)+1:ℝ)/(1/4096)
  let μ:ℝ:=(1/4096)/(12*(Module.finrank ℝ (Model n)+1:ℝ))
  have hM:2 ≤ M0:=by dsimp [M0]; have h:=Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (Model n)); linarith
  have hμ:0 < μ:=by dsimp [μ]; positivity
  have hγ:=centerGamma_pos
  let K:ℝ:=1+8*centerGamma^2*(B+1)/μ^(n-1)
  have hK:1 ≤ K:=by dsimp [K]; exact le_add_of_nonneg_right (by positivity)
  let eta:ℝ:=min (1/128) (templateEps/(24*(128*(M0+3)*(K+1))))
  have heta:0 < eta:=by dsimp [eta]; rw [templateEps_eq]; positivity
  have heta1:eta ≤ 1/128:=min_le_left _ _
  have hetasmall:eta ≤ templateEps/(24*(128*(M0+3)*(K+1))):=min_le_right _ _
  obtain ⟨C,hC,hder⟩:=exists_outerTemplate_deriv_bound (M0:=M0) (K:=K) heta heta1
  let θ:ℝ:=eps/centerGamma
  have hθ:0 < θ:=by dsimp [θ]; positivity
  obtain ⟨uv,huv,α,D,bm,bp,hD,hbm,hbp,hsmall,hcent,hout,hosc,herror,⟨F⟩⟩:=
    hmtw.nonpower_maximum hc hno hM hK heta heta1 hetasmall hC hder hθ
  have hclose:bp/D*centerGamma/2 < eps:=by
    have hh:bp/D ≤ θ:=(div_le_iff₀ hD).mpr hsmall
    have HH:=mul_le_mul_of_nonneg_right hh hγ.le
    have he:θ*centerGamma=eps:=by dsimp [θ]; field_simp
    rw [he] at HH
    linarith only [HH,heps]
  have H:=HB K eta hK heta heta1 hetasmall x0 uv huv α D bm bp hD hbm hbp hcent hclose
    C hC hder hout hosc herror F
  change μ^(n-1)*K/(8*centerGamma^2) ≤ B at H
  have he:μ^(n-1)*K/(8*centerGamma^2)=μ^(n-1)/(8*centerGamma^2)+(B+1):=by
    dsimp only [K]
    field_simp
  rw [he] at H
  have hh:0 ≤ μ^(n-1)/(8*centerGamma^2):=by positivity
  linarith only [H,hh]

end ClassPower
end WeakMTWTransport

end
end

end OAI
