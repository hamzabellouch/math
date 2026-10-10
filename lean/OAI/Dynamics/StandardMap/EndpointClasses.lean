import OAI.Dynamics.StandardMap.EndpointCovariance

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def endpointLeft (d:DistanceArray) : ℝ := (leftEndpoint d).toReal
noncomputable def endpointRight (d:DistanceArray) : ℝ := (rightEndpoint d).toReal
def leftRayClass : Set DistanceArray := {d | leftEndpoint d≠⊥ ∧ leftEndpoint d≠⊤ ∧ rightEndpoint d=⊤}
def rightRayClass : Set DistanceArray := {d | leftEndpoint d=⊥ ∧ rightEndpoint d≠⊥ ∧ rightEndpoint d≠⊤}
def twoRayClass : Set DistanceArray := {d | leftEndpoint d≠⊥ ∧ leftEndpoint d≠⊤ ∧ rightEndpoint d≠⊥ ∧ rightEndpoint d≠⊤}
lemma measurable_endpointLeft : Measurable endpointLeft := measurable_ereal_toReal.comp measurable_leftEndpoint
lemma measurable_endpointRight : Measurable endpointRight := measurable_ereal_toReal.comp measurable_rightEndpoint
lemma measurableSet_leftRayClass : MeasurableSet leftRayClass :=
  ((measurable_leftEndpoint (measurableSet_singleton ⊥)).compl).inter
    (((measurable_leftEndpoint (measurableSet_singleton ⊤)).compl).inter (measurable_rightEndpoint (measurableSet_singleton ⊤)))
lemma measurableSet_rightRayClass : MeasurableSet rightRayClass :=
  (measurable_leftEndpoint (measurableSet_singleton ⊥)).inter
    (((measurable_rightEndpoint (measurableSet_singleton ⊥)).compl).inter ((measurable_rightEndpoint (measurableSet_singleton ⊤)).compl))
lemma measurableSet_twoRayClass : MeasurableSet twoRayClass :=
  ((measurable_leftEndpoint (measurableSet_singleton ⊥)).compl).inter
    (((measurable_leftEndpoint (measurableSet_singleton ⊤)).compl).inter
      (((measurable_rightEndpoint (measurableSet_singleton ⊥)).compl).inter ((measurable_rightEndpoint (measurableSet_singleton ⊤)).compl)))
lemma slowShape_dyadic {d : DistanceArray} {c:ℝ} (hu:UnitArray d) (h:SlowShape (realArray d) c) :
    (∀s t:DyadicTime,d.val s t≤c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
lemma leftRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈leftRayClass) :
    (∀s t:DyadicTime,(s:ℝ)≤endpointLeft d → (t:ℝ)≤endpointLeft d → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,endpointLeft d≤(s:ℝ) → endpointLeft d≤(t:ℝ) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.1 (endpoints_slow hc hs).1).elim
  · have he := (endpoints_left_ray hc hl hs).1
    have ha : endpointLeft d=a := by simp only [endpointLeft,he,EReal.toReal_coe]
    simpa only [ha] using And.intro hl hs
  · exact (hd.1 (endpoints_right_ray hc hr hs).1).elim
  · have he := (endpoints_two_rays hab hc hl hr hs).2
    exact (EReal.coe_ne_top b (he.symm.trans hd.2.2)).elim
lemma rightRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈rightRayClass) :
    (∀s t:DyadicTime,endpointRight d≤(s:ℝ) → endpointRight d≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,(s:ℝ)≤endpointRight d → (t:ℝ)≤endpointRight d → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.2.2 (endpoints_slow hc hs).2).elim
  · exact (hd.2.2 (endpoints_left_ray hc hl hs).2).elim
  · have he := (endpoints_right_ray hc hr hs).2
    have hb : endpointRight d=b := by simp only [endpointRight,he,EReal.toReal_coe]
    simpa only [hb] using And.intro hr hs
  · have he := (endpoints_two_rays hab hc hl hr hs).1
    exact (EReal.coe_ne_bot a (he.symm.trans hd.1)).elim
lemma twoRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈twoRayClass) : endpointLeft d<endpointRight d ∧
    (∀s t:DyadicTime,(s:ℝ)≤endpointLeft d → (t:ℝ)≤endpointLeft d → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,endpointRight d≤(s:ℝ) → endpointRight d≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,(s:ℝ)∈Icc (endpointLeft d) (endpointRight d) → (t:ℝ)∈Icc (endpointLeft d) (endpointRight d) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.1 (endpoints_slow hc hs).1).elim
  · exact (hd.2.2.2 (endpoints_left_ray hc hl hs).2).elim
  · exact (hd.1 (endpoints_right_ray hc hr hs).1).elim
  · have he := endpoints_two_rays hab hc hl hr hs
    have ha : endpointLeft d=a := by simp only [endpointLeft,he.1,EReal.toReal_coe]
    have hb : endpointRight d=b := by simp only [endpointRight,he.2,EReal.toReal_coe]
    simpa only [ha,hb] using And.intro hab (And.intro hl (And.intro hr hs))
end StandardMapEntropy

end OAI
