import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalJoinedH1
import OAI.Analysis.Conductivity.Variational.WholeBallJet

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Classical

lemma ballWholePiJetCLM_ae_of_ae (z : JetSpace) (f : (Fin 3 → ℝ) → JetFiber)
    (he : z=ᵐ[ballMeasure] (fun x => f (WithLp.ofLp x))) :
    ballWholePiJetCLM z=ᵐ[volume]
      (fun y => if WithLp.toLp 2 y∈ball then f y else 0) := by
  have hz := lpZeroExtensionCLM_ae_of_ae (D:=ball) Metric.isOpen_ball.measurableSet z he
  apply (Lp.coeFn_compMeasurePreserving _ (PiLp.volume_preserving_toLp (Fin 3))).trans
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp hz
  filter_upwards [hp] with y hy
  change (lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet z) (WithLp.toLp 2 y)=_
  rw [show (lpZeroExtensionCLM (D:=ball) Metric.isOpen_ball.measurableSet z) (WithLp.toLp 2 y)=
    ball.indicator (fun x => f (WithLp.ofLp x)) (WithLp.toLp 2 y) from hy]
  by_cases hb : WithLp.toLp 2 y∈ball <;> simp [hb]

lemma ballWholePiComponentCLM_ae_of_ae (i : Fin 4) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber)
    (he : z=ᵐ[ballMeasure] (fun x => f (WithLp.ofLp x))) :
    ballWholePiComponentCLM i z=ᵐ[volume]
      (fun y => if WithLp.toLp 2 y∈ball then f y i else 0) := by
  filter_upwards [ballWholePiComponentCLM_ae i z,ballWholePiJetCLM_ae_of_ae z f he] with y hi hy
  rw [hi,hy]
  split_ifs <;> rfl

lemma sourceBand_mem_ball {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) : WithLp.toLp 2 y∈ball := by
  have hn := sourceBand_euclidean_bound hy
  simpa only [ball,Metric.mem_ball,dist_zero_right] using hn.trans_lt (by norm_num : (5:ℝ)/2<3)

lemma localJoinedJet_zero_outside_ball {τ χ q p : (Fin 3 → ℝ) → ℝ}
    (hs : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) {y : Fin 3 → ℝ}
    (hy : WithLp.toLp 2 y∉ball) :
    WithLp.toLp 2 (Fin.cases (localJoinedValue τ χ q p y)
      (fun i => localJoinedGradient τ χ q p i y))=(0:JetFiber) := by
  have ht : y∉tsupport χ := fun h => hy (hs y h)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [localJoinedValue,image_eq_zero_of_notMem_tsupport ht]
  · simp [localJoinedGradient,image_eq_zero_of_notMem_tsupport ht,fderiv_of_notMem_tsupport ℝ ht]

lemma ballWholePiJetCLM_localJoined_ae {z : JetSpace} {τ χ q p : (Fin 3 → ℝ) → ℝ}
    (hs : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball)
    (he : z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2
      (Fin.cases (localJoinedValue τ χ q p (WithLp.ofLp x))
        (fun i => localJoinedGradient τ χ q p i (WithLp.ofLp x))))) :
    ballWholePiJetCLM z=ᵐ[volume] (fun y => WithLp.toLp 2
      (Fin.cases (localJoinedValue τ χ q p y) (fun i => localJoinedGradient τ χ q p i y))) := by
  apply (ballWholePiJetCLM_ae_of_ae z (fun y => WithLp.toLp 2
    (Fin.cases (localJoinedValue τ χ q p y) (fun i => localJoinedGradient τ χ q p i y))) he).trans
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    split_ifs with hb
    · rfl
    · exact (localJoinedJet_zero_outside_ball hs hb).symm)

end ScalarConductivity

end

end OAI
