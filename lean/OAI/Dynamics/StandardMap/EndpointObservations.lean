import OAI.Dynamics.StandardMap.LimitBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def shortfallObservationFunction (x : Fin 1 → ℝ) : ℝ := unitClip (x 0)
lemma shortfallObservationFunction_lipschitz : LipschitzWith 6 shortfallObservationFunction := by
  exact (unitClip_lipschitz.comp (LipschitzWith.eval (0 : Fin 1))).weaken (by norm_num)
lemma testObservation_zero : testObservation 0=0 := by norm_num [testObservation,unitClip]
lemma shortfallObservationFunction_zero : shortfallObservationFunction 0=0 := by norm_num [shortfallObservationFunction,unitClip]
structure EndpointObservation where
  size : ℕ
  left : Fin size → DyadicTime
  right : Fin size → DyadicTime
  ordered : ∀i,(left i:ℝ)<(right i:ℝ)
  function : (Fin size → ℝ) → ℝ
  lipschitz : LipschitzWith 6 function
  at_zero : function 0=0
  nonneg : ∀d,0≤ arrayObservation left right function d
noncomputable def EndpointObservation.value (O : EndpointObservation) : DistanceArray → ℝ :=
  arrayObservation O.left O.right O.function
noncomputable def testEndpoint (j : ArrayTestIndex) : EndpointObservation where
  size := 3
  left := testLeft j.val.1 j.val.2
  right := testRight j.val.1 j.val.2
  ordered := by
    intro i
    fin_cases i <;> dsimp [testLeft,testRight,dyadicMid,dyadicHalf] <;> linarith [j.property]
  function := testObservation
  lipschitz := testObservation_lipschitz
  at_zero := testObservation_zero
  nonneg := clippedTest_nonneg j
noncomputable def shortfallEndpoint (j : ArrayTestIndex) : EndpointObservation where
  size := 1
  left := fun _ => j.val.1
  right := fun _ => j.val.2
  ordered := fun _ => j.property
  function := shortfallObservationFunction
  lipschitz := shortfallObservationFunction_lipschitz
  at_zero := shortfallObservationFunction_zero
  nonneg := clippedShortfall_nonneg _ _
@[simp] lemma testEndpoint_value (j : ArrayTestIndex) (d : DistanceArray) : (testEndpoint j).value d=clippedTest j d := rfl
@[simp] lemma shortfallEndpoint_value (j : ArrayTestIndex) (d : DistanceArray) :
    (shortfallEndpoint j).value d=clippedShortfall j.val.1 j.val.2 d := rfl
def EndpointObservation.inWindow (O : EndpointObservation) (u : DyadicTime) (q : ℕ) : Prop :=
  (∀i,-((1:ℝ)/(2:ℝ)^q)≤(O.left i:ℝ)-(u:ℝ)) ∧
  (∀i,(O.right i:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q)
def intervalInWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ) : Prop :=
  -((1:ℝ)/(2:ℝ)^q)≤(j.val.1:ℝ)-(u:ℝ) ∧ (j.val.2:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q
lemma testEndpoint_inWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ)
    (hj : intervalInWindow j u q) : (testEndpoint j).inWindow u q := by
  constructor <;> intro i <;> fin_cases i <;>
    dsimp [testEndpoint,testLeft,testRight,dyadicMid,dyadicHalf] <;>
    have hp := j.property <;> have h1 := hj.1 <;> have h2 := hj.2 <;> linarith
lemma shortfallEndpoint_inWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ)
    (hj : intervalInWindow j u q) : (shortfallEndpoint j).inWindow u q := ⟨fun _ => hj.1,fun _ => hj.2⟩
noncomputable def endpointBridgeEvent (u v : DyadicTime) (W H : EndpointObservation) (ηw ηh : ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ ηw< W.value d ∧ ηh< H.value d}
namespace CriticalScaleSequence
noncomputable def LimitLaws.selected (S : CriticalScaleSequence) (K : S.LimitLaws) (b : Bool) : Measure NonAffineArray :=
  if b then K.multi else K.terminal
lemma endpoint_bridge_null (S : CriticalScaleSequence) (K : S.LimitLaws) (select : Bool)
    (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) (W H : EndpointObservation)
    (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.selected S select {d | d.val∈endpointBridgeEvent u v W H ηw ηh}=0 := by
  obtain ⟨B,hu,hv,hsw,htw,hsh,hth⟩ := exists_bridgeGrid u v huv W.left W.right H.left H.right W.ordered H.ordered
    q hq hW.1 hW.2 hH.1 hH.2
  have hW0 : ∀d,0≤ arrayObservation B.sw B.tw W.function d := by simpa only [hsw,htw] using W.nonneg
  have hH0 : ∀d,0≤ arrayObservation B.sh B.th H.function d := by simpa only [hsh,hth] using H.nonneg
  have htest' : (∀d,arrayObservation B.sw B.tw W.function d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th H.function d=clippedTest j d) := by
    simpa only [hsw,htw,hsh,hth,EndpointObservation.value] using htest
  have he : {d : NonAffineArray | d.val∈arrayBridgeEvent B W.function H.function ηw ηh}=
      {d : NonAffineArray | d.val∈endpointBridgeEvent u v W H ηw ηh} := by
    simp only [arrayBridgeEvent,endpointBridgeEvent,hu,hv,hsw,htw,hsh,hth,EndpointObservation.value]
  cases select
  · exact he ▸ S.bridge_null_terminal K B W.function H.function 6 W.lipschitz H.lipschitz W.at_zero H.at_zero hW0 hH0 j htest' ηw ηh hηw hηh
  · exact he ▸ S.bridge_null_multi K B W.function H.function 6 W.lipschitz H.lipschitz W.at_zero H.at_zero hW0 hH0 j htest' ηw ηh hηw hηh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
