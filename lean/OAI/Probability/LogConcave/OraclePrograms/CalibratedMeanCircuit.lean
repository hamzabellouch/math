import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CenteringMeanCircuitFull
import OAI.Probability.LogConcave.Sampling.NumericalScalars

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Set MeasureTheory Quadrature ProbabilityTheory
open scoped Classical BigOperators NNReal

def CalibratedMeanCircuit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h ψ s : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n N : ℕ) (err : ℝ) : Prop :=
  let e := probabilityEndpoint hT0 hT1 hh (n+1)
  let μ := gibbs (centeringPotential F x r T)
  ∃X : StationaryPath μ
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0.le hT1) s)),
    (∀i,Integrable (fun y => ‖stationaryPicard n N
      (centeringVelocityJoint F x r T h ψ s n n N e) y i-X.path y (probabilityNodes n i)‖^2) μ) ∧
    (∀i,(∫y,‖stationaryPicard n N
      (centeringVelocityJoint F x r T h ψ s n n N e) y i-X.path y (probabilityNodes n i)‖^2 ∂μ)≤
      (circuitD F x)^2*err) ∧
    Measurable (stationaryMeanTarget hF x hr hl hT0.le hT1 X) ∧
    μ.map (stationaryMeanTarget hF x hr hl hT0.le hT1 X)=
      (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) ∧
    Integrable (fun y => ‖centeringMeanCircuit F x r T h ψ s n n N n N e y-
      stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2) μ ∧
    (∫y,‖centeringMeanCircuit F x r T h ψ s n n N n N e y-
      stationaryMeanTarget hF x hr hl hT0.le hT1 X y‖^2 ∂μ)≤(s*circuitD F x)^2*err

theorem exists_calibrated_mean_circuit {κ J b t : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (ht : 0<t) (htsmall : t<1/100) :
    ∀{w : ℝ},0<w → w<t → ∃n : ℕ,
      J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
      ∀{S : ℝ},0≤S → ∀ksize : ℕ,∀ᶠ d : ℕ in atTop,
      let T := sourceCorrelation (κ*t) d
      let h := (d:ℝ)^(-(κ*w))
      let ψ := (d:ℝ)^(-(κ*(4*t)))
      ∃hT0 : 0<T,∃hT1 : T<1,∃hh : 0<h,
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,∀x : Point d,
      ∀{r s : ℝ},∀hr : 0<r,r≤1 → 0<lam → (lam:ℝ)*r≤1 → 0<s →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      (lam:ℝ)*r/s≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      ∃hl : (lam:ℝ)*r^2≤1/2,
      CalibratedMeanCircuit (ψ:=ψ) (s:=s) hF x hr hl hT0 hT1 hh n (numericalLayerCount J)
        ((d:ℝ)^(-(2*κ*J))) := by
  intro w hw hwt
  obtain ⟨n,hnw,hnt,hnn⟩ := exists_numerical_order (J:=J) ht hw
  have hn : 0<n := by
    have he : (0:ℝ)<n := by linarith
    exact_mod_cast he
  have hn1 : 1≤n := hn
  obtain ⟨A,B,Ap,Ah,Lp,Lh,C,J₀,D,hC,hJ₀,hD,k,hproducer⟩ := centeringMeanCircuit_full_rms n
  let U := A+B+Ap+Ah+Lp+Lh
  have hU : A≤U ∧ B≤U ∧ Ap≤U ∧ Ah≤U ∧ Lp≤U ∧ Lh≤U := by
    dsimp only [U]
    have ha : (0:ℝ≥0)≤A := bot_le
    have hb : (0:ℝ≥0)≤B := bot_le
    have hc : (0:ℝ≥0)≤Ap := bot_le
    have hd : (0:ℝ≥0)≤Ah := bot_le
    have he : (0:ℝ≥0)≤Lp := bot_le
    have hf : (0:ℝ≥0)≤Lh := bot_le
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> first | nlinarith | skip
    constructor <;> nlinarith
  refine ⟨n,hnw,hnt,hnn,?_⟩
  intro S hS ksize
  have hc := centeringScalarCalibration_uniform k n (numericalLayerCount J) ksize A Ap Ah Lp U C J₀ D
    hS hκ hJ hb ht htsmall hw hwt hnw hnt hnn (numericalLayerCount_bound J)
  have hT := sourceCorrelation_eventually (mul_pos hκ ht)
  have hmesh := sourceMesh_eventually (mul_pos hκ ht) (mul_pos hκ hw)
  have hangle := sourceAngle_eventually (show 0<κ*(4*t) by positivity) n
  filter_upwards [hc,hT,hmesh,hangle,eventually_ge_atTop (1:ℕ)] with d hdc hdT hdmesh hdangle hd
  intro T h ψ
  let R := (d:ℝ)^(-(κ*t))
  have hd0 : (0:ℝ)<d := by exact_mod_cast hd
  have hh : 0<h := Real.rpow_pos_of_pos hd0 _
  have hR : 0<R := Real.rpow_pos_of_pos hd0 _
  have hψ : 0<ψ := Real.rpow_pos_of_pos hd0 _
  refine ⟨hdT.1,hdT.2.1,hh,?_⟩
  intro F lam hF x r s hr hr1 hlam hL hs hl₀ hα
  have hgood := hdc ⟨lam,r,s⟩ ⟨hr,hs,hl₀,hα⟩
  rcases hgood with ⟨hl,hcontr,hq,hz,hm⟩
  have bound {K : ℝ≥0} (hK : K≤U) : K*probabilityMeanLipschitz lam r≤1/2 :=
    (mul_le_mul_of_nonneg_right hK bot_le).trans hcontr
  refine ⟨hl,?_⟩
  obtain ⟨X,hsi,hsb,hmeas,hlaw,hmi,hmb⟩ := hproducer hF x hr hr1 hlam hl hL hd
    hdT.1 hdT.2.1 hh hdmesh.1 hdmesh.2
    (bound hU.2.2.1) (bound hU.2.2.2.1) (bound hU.2.2.2.2.1) (bound hU.2.2.2.2.2)
    (bound hU.1) (bound hU.2.1) (numericalLayerCount J) R hR hdT.2.2.le n hn1 ψ hψ hdangle
    s hs n (numericalLayerCount J) hn hq
  refine ⟨X,hsi,?_,hmeas,hlaw,hmi,?_⟩
  · intro i
    exact (hsb i).trans (mul_le_mul_of_nonneg_left hz (sq_nonneg _))
  · exact hmb.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
end LogConcaveSampling

end

end

end OAI
