import OAI.Probability.SLE.Angle.TargetFlowInjectivity

namespace OAI

/-! A measurable inverse of the raw surviving flow. The inverse is the
prescribed `inverseFlow`, including its value zero outside its range. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

local instance inverseDriverPolish : PolishSpace Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace

def survivingState (κ : ℝ) : Set (ℝ≥0 × (Driver × ℂ)) :=
  {q | Surviving κ q.2.1 q.2.2 q.1}

def survivingStateMap (κ : ℝ) (q : survivingState κ) : ℝ≥0 × (Driver × ℂ) :=
  (q.1.1,(q.1.2.1,flow κ q.1.2.1 q.1.2.2 q.1.1))

lemma measurable_survivingStateMap (κ : ℝ) : Measurable (survivingStateMap κ) :=
  measurable_subtype_coe.fst.prodMk (measurable_subtype_coe.snd.fst.prodMk
    ((measurable_flow κ).comp measurable_subtype_coe))

lemma survivingStateMap_injective (κ : ℝ) : Function.Injective (survivingStateMap κ) := by
  rintro ⟨⟨t,b,z⟩,hz⟩ ⟨⟨s,c,w⟩,hw⟩ he
  change (t,(b,flow κ b z t))=(s,(c,flow κ c w s)) at he
  rcases Prod.mk.inj he with ⟨rfl,he⟩
  rcases Prod.mk.inj he with ⟨rfl,he⟩
  have hzw := flow_injOn_surviving κ b t t.coe_nonneg hz hw he
  change z=w at hzw
  subst w
  rfl

lemma measurableEmbedding_survivingStateMap (κ : ℝ) :
    MeasurableEmbedding (survivingStateMap κ) := by
  let : StandardBorelSpace (survivingState κ) := (measurableSet_surviving κ).standardBorel
  exact (measurable_survivingStateMap κ).measurableEmbedding (survivingStateMap_injective κ)

lemma inverseFlow_eq_extend (κ : ℝ) (q : ℝ≥0 × (Driver × ℂ)) :
    inverseFlow κ q.2.1 q.1 q.2.2 =
      Function.extend (survivingStateMap κ) (fun p => p.1.2.2) (fun _ => (0:ℂ)) q := by
  classical
  by_cases h : ∃ z, Surviving κ q.2.1 z q.1 ∧ flow κ q.2.1 z q.1=q.2.2
  · let z := Classical.epsilon (fun z => Surviving κ q.2.1 z q.1 ∧ flow κ q.2.1 z q.1=q.2.2)
    have hz : Surviving κ q.2.1 z q.1 ∧ flow κ q.2.1 z q.1=q.2.2 := Classical.epsilon_spec h
    let p : survivingState κ := ⟨(q.1,(q.2.1,z)),hz.1⟩
    have hp : survivingStateMap κ p=q := by
      rcases q with ⟨t,b,w⟩
      change (t,(b,flow κ b z t))=(t,(b,w))
      rw [hz.2]
    rw [inverseFlow,ite_eq_left h]
    change z = _
    calc
      z = p.1.2.2 := rfl
      _ = Function.extend (survivingStateMap κ) (fun p => p.1.2.2) (fun _ => (0:ℂ))
          (survivingStateMap κ p) := ((survivingStateMap_injective κ).extend_apply
            (fun p => p.1.2.2) (fun _ => (0:ℂ)) p).symm
      _ = _ := by rw [hp]
  · have hn : ¬∃ p, survivingStateMap κ p=q := by
      rintro ⟨p,hp⟩
      apply h
      have ht := congrArg Prod.fst hp
      have hb := congrArg (fun x : ℝ≥0 × (Driver × ℂ) => x.2.1) hp
      have hf := congrArg (fun x : ℝ≥0 × (Driver × ℂ) => x.2.2) hp
      change p.1.1=q.1 at ht
      change p.1.2.1=q.2.1 at hb
      change flow κ p.1.2.1 p.1.2.2 p.1.1=q.2.2 at hf
      refine ⟨p.1.2.2,?_,?_⟩
      · simpa only [ht,hb] using (show Surviving κ p.1.2.1 p.1.2.2 p.1.1 from p.2)
      · simpa only [ht,hb] using hf
    rw [inverseFlow,ite_eq_right h,Function.extend_apply' _ _ _ hn]

lemma measurable_inverseFlow (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => inverseFlow κ q.2.1 q.1 q.2.2) := by
  have hm := (measurableEmbedding_survivingStateMap κ).measurable_extend
    measurable_subtype_coe.snd.snd (measurable_const (a := (0:ℂ)))
  convert hm using 1
  funext q
  exact inverseFlow_eq_extend κ q

end SLEExactGauge.Target

end

end OAI
