import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorSynthesis
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorNeighborhood
import OAI.Analysis.LipschitzHilbert.Estimates.ErrorSynthesisVariation
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketContinuity
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightedPair
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightedInterval

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_synthesis_global_neighborhood_of_supported
    (P : LabeledAngularErrorFamily N Λ κ ι)
    (B C a b r R : ℝ) (hB : 0 ≤ B) (hC : 0 < C) (hr : 0 < r) (hR : 0 < R)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (hshort : ∀ j l (_u : ι j l), P.length j ≤ r) (hwidth : P.width ≤ R)
    (hx : ∀ j l u, |P.originX j l+P.length j*(P.site j l u).1-a| ≤ r)
    (hy : ∀ j l u, |P.originY j l+P.width*(P.site j l u).2-b| ≤ R)
    (raw : Fin 2 → ∀ j, (Σ l : Λ j, ι j l) → κ → ℝ → SchwartzMap ℝ ℂ)
    (frequency : κ → ℝ) (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hraw : ∀ i j l u k y x, ‖raw i j ⟨l,u⟩ k y x‖ ≤ C*
      (lineEnvelope (P.originX j l+P.length j*(P.site j l u).1) (P.length j) (6+2*q) x*
        lineEnvelope (P.originY j l+P.width*(P.site j l u).2) P.width (6+2*q) y))
    (hcov : ∀ j p k x y, (4*R:ℂ)*(deriv (fun yy => raw 0 j p k yy x) y-
      (frequency k:ℂ)*Complex.I*raw 0 j p k y x) = raw 1 j p k y x)
    (hcont : ∀ i j p k, Continuous (fun z : ℝ×ℝ => raw i j p k z.1 z.2))
    (hdiff : ∀ j p k x y, DifferentiableAt ℝ (fun yy => raw 0 j p k yy x) y) :
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal r*ENNReal.ofReal (2*R))*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ lower upper x z v, |v| ≤ R → (x,z) ∉ bad →
        ‖planarPacketInterval (fun j p => P.coefficient j p.1 p.2)
          (fun j p k y x => raw 0 j p k y x) lower upper x (z+v)‖ ≤
          256^q*(16*topPairConstant C q*selectorErrorMomentBase B*(n:ℝ))*
            boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  let coeff := fun j (p : Σ l : Λ j, ι j l) => P.coefficient j p.1 p.2
  let synth := fun i j p k y => topWeightedPair (fun e => raw e j p k y) a r b R y q i
  let wave := fun j p k y x => synth 0 j p k y x
  let A := ℕ×ℕ
  let f : A → κ → ℝ → ℝ → ℂ := fun ab k x y =>
    planarPacketInterval coeff wave ab.1 ab.2 x y k
  let F : A → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval coeff (fun j p k y x => raw 0 j p k y x) ab.1 ab.2 x y
  have hCpair := topPairConstant_pos C q hC
  have hbound i j l u k y x : ‖synth i j ⟨l,u⟩ k y x‖ ≤ topPairConstant C q*
      tileEnvelope (P.originX j l+P.length j*(P.site j l u).1)
        (P.originY j l+P.width*(P.site j l u).2) (P.length j) P.width 6 (x,y) := by
    exact topWeightedPair_bound (fun e => raw e j ⟨l,u⟩ k y) a r b R y _ _ _ _ C q 6 6
      (div_pos P.topLength_pos (pow_pos (by norm_num) _)) hr P.width_pos hR
      (hshort j l u)
      hwidth (hx j l u) (hy j l u) hC.le (fun e => hraw e j l u k y) i x
  have hc j p k x y : (4*R:ℂ)*(deriv (fun yy => wave j p k yy x) y-
      (frequency k:ℂ)*Complex.I*wave j p k y x) = synth 1 j p k y x := by
    simpa [wave,synth,topWeightedPair] using topWeightedWave_covariant
      (raw 0 j p k) (raw 1 j p k) a r b R y (frequency k) x q
      (hdiff j p k x y) (hcov j p k x y)
  have hdiffw j p k x y : DifferentiableAt ℝ (fun yy => wave j p k yy x) y := by
    simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
      topWeightedWave_vertical_differentiable (raw 0 j p k) a r b R x y q (hdiff j p k x y)
  have hDw j p k : Continuous (fun z : ℝ×ℝ =>
      deriv (fun yy => wave j p k yy z.2) z.1-
        (frequency k:ℂ)*Complex.I*wave j p k z.1 z.2) := by
    simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
      topWeightedWave_covariant_continuous (raw 0 j p k) (raw 1 j p k)
        a r b R (frequency k) q hR (hcont 0 j p k) (hcont 1 j p k)
        (hdiff j p k) (hcov j p k)
  have hnorm ab x y : ‖(WithLp.toLp 2 (fun k => f ab k x y) : EuclideanSpace ℂ κ)‖ ≤
      (2*topPairConstant C q)*P.error y x := by
    change ‖planarPacketInterval coeff wave ab.1 ab.2 x y‖ ≤ _
    exact P.error_interval_norm_le wave _ hCpair.le (hbound 0) _ _ x y
  have hDnorm ab x y : 4*R*‖covariantSignal frequency (fun k => f ab k x) y‖ ≤
      (2*topPairConstant C q)*P.error y x := by
    have heq : (4*R) • covariantSignal frequency (fun k => f ab k x) y =
        planarPacketInterval coeff (fun j p k y x => synth 1 j p k y x) ab.1 ab.2 x y := by
      rw [show covariantSignal frequency (fun k => f ab k x) y =
        planarPacketInterval coeff (fun j p k y x => deriv (fun yy => wave j p k yy x) y-
          (frequency k:ℂ)*Complex.I*wave j p k y x) ab.1 ab.2 x y from
            planarPacketInterval_covariant coeff wave frequency _ _ _ _ (fun j p k => hdiffw j p k x)]
      rw [← planarPacketInterval_smul]
      congr 1
      funext j p k y x
      simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using hc j p k x y
    have hn := congrArg norm heq
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 4*R)] at hn
    rw [hn]
    exact P.error_interval_norm_le _ _ hCpair.le (hbound 1) _ _ x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := P.error_global_neighborhood B (2*topPairConstant C q)
    a b r R hB (by positivity) hr hR hs ht
    hshort
    frequency f F q n hq hn
    (fun ab k x y => planarPacketInterval_component_differentiable coeff wave _ _ x y k
      (fun j p => hdiffw j p k x y))
    (fun p ab x => planarPacketInterval_covariant_memLp coeff wave frequency hdiffw hDw
      _ _ x _ _) hnorm hDnorm (by
        intro ab x y
        change ‖planarPacketInterval coeff wave ab.1 ab.2 x y‖ = _
        simpa only [wave,synth,topWeightedPair,ite_eq_left rfl] using
          planarPacketInterval_topWeighted_norm coeff (fun j p k y => raw 0 j p k y)
            a r b R q ab.1 ab.2 x y)
  refine ⟨bad,hbad,harea,?_⟩
  intro lower upper x z v hv hout
  have h := hpoint (lower,upper) x z v hv hout
  convert h using 1
  ring

end LipschitzHilbert.LabeledAngularErrorFamily

end

end OAI
