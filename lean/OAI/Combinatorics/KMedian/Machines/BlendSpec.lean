import Mathlib
import OAI.Combinatorics.KMedian.Expanders.GraphMix

namespace OAI

section Inline_PCPBlendSpec
namespace MetricKMedian.PCP.PortGraph
variable {V W D S : Type} (G : PortGraph V D) (H : PortGraph V S) (code : V → W)
lemma blend_coded (v : V) (d : BlendPort (D := D) (S := S)) :
    (code ((G.blend H).step v d),(G.blend H).back v d)=
      if d.1=0 then (code (G.step v d.2.1),(d.1,(G.back v d.2.1,d.2.2)))
      else (code (H.step v d.2.2),(d.1,(d.2.1,H.back v d.2.2))) := by
  change (code (blendRotate G H (v,d)).1,(blendRotate G H (v,d)).2)=_
  by_cases hd : d.1=0 <;> simp only [blendRotate,hd,ite_true,ite_false]
end MetricKMedian.PCP.PortGraph

end Inline_PCPBlendSpec

end OAI
