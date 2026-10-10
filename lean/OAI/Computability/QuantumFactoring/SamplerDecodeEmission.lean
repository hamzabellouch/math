import Mathlib
import OAI.Computability.QuantumFactoring.OrderSamplerEmission

namespace OAI



section
namespace ExactQuantumFactoring.SamplerDecodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k u b : α→ℕ}
lemma sampleY (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.sampleYNet (u x) (b x)):=
  selectSlice (OrderSamplerEmission.width hu hb) hb (hu.unaryAdd hu).unaryNat _ (by intros;rfl)
lemma sampleU (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderTrial.sampleUNet (u x) (b x)):=
  selectSlice (OrderSamplerEmission.width hu hb) hu (OrderSamplerEmission.inputWidth hu hb).unaryNat _ (by intros;rfl)
lemma triangular {y : ∀x,BooleanNetwork (k x) (b x)}
    (hk : Emits ea unaryCode k) (hb : Emits ea unaryCode b) (hy : NetEmits ea y) :
    NetEmits ea (fun x=>OrderTrial.triangularSelectedNet (y x)):=
  (hy.pair (zeros hk hb)).packNet (zeros hk (hb.unaryAdd hb)) hk (TriangularEmission.work hb)
lemma selected {a m : ∀x,BooleanNetwork (k x) (u x)} {z : ∀x,BooleanNetwork (k x) (OrderSample.width (u x) (b x))}
    (hk : Emits ea unaryCode k) (hu : Emits ea unaryCode u) (hb : Emits ea unaryCode b)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hz : NetEmits ea z) :
    NetEmits ea (fun x=>OrderTrial.samplerSelectedNet (a x) (m x) (z x)):=
  hz.equalOn ((((ha.pair hm).pair (triangular hk hb (hz.comp (sampleY hu hb)))).packNet
    (hz.comp (sampleU hu hb)) hk (OrderSamplerEmission.scratch hu hb))) (OrderSamplerEmission.width hu hb)
end ExactQuantumFactoring.SamplerDecodeEmission

end



end OAI
