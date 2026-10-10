import OAI.Analysis.BernoulliCone.UpperLeaves

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_continuousAt {p:Space 7×ℝ} (hp:U p.1<p.2) :
    ContinuousAt (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  rw [ContinuousAt,tendsto_order]
  constructor
  · intro a ha
    by_cases hapos:0<a
    · have hat:upperFamily a p.1<p.2:=(lt_upperParameter_iff hp hapos).mp ha
      have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,upperFamily a z.1<z.2 :=
        ((upperFamily_continuous a).continuousAt.comp continuous_fst.continuousAt).eventually_lt
          continuous_snd.continuousAt hat
      filter_upwards [hdom,hnear] with z hz hz1
      exact (lt_upperParameter_iff hz hapos).mpr hz1
    · filter_upwards [hdom] with z hz
      exact (le_of_not_gt hapos).trans_lt (upperParameter_spec hz).1
  · intro b hb
    have hbpos:0<b := (upperParameter_spec hp).1.trans hb
    have hbt:p.2<upperFamily b p.1:=(upperParameter_lt_iff hp hbpos).mp hb
    have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,z.2<upperFamily b z.1 :=
      continuous_snd.continuousAt.eventually_lt
        ((upperFamily_continuous b).continuousAt.comp continuous_fst.continuousAt) hbt
    filter_upwards [hdom,hnear] with z hz hz1
    exact (upperParameter_lt_iff hz hbpos).mpr hz1
lemma upperParameter_continuousOn : ContinuousOn (fun z:Space 7×ℝ=>upperParameter z.1 z.2)
    {z|U z.1<z.2} := fun _ hp=>(upperParameter_continuousAt hp).continuousWithinAt
end Bernoulli.DeSilvaJerison

end
end

end OAI
