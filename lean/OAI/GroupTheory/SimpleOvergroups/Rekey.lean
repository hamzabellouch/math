import Mathlib
import OAI.GroupTheory.SimpleOvergroups.TruncatedAction

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
namespace KeyBall
variable {X K K' : Type*} (C : KeyBall X K)

def mapKey (f : K → K') : KeyBall X K' where
  ball := C.ball
  mono := C.mono
  key := f ∘ C.key

end KeyBall
namespace ActionCalculus
variable {V X K L K' L' : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

def rekey (g : K → K') (x : L → L') (hg : Function.Injective g)
    (hx : Function.Injective x) : ActionCalculus V X K' L' m where
  group := C.group.mapKey g
  point := C.point.mapKey x
  one_mem := C.one_mem
  inv_mem := C.inv_mem
  mul_mem := C.mul_mem
  smul_mem := C.smul_mem
  inv_congr := fun h => congrArg g (C.inv_congr (hg h))
  mul_congr := fun hu hv hu' hv' hb hb' he hf =>
    congrArg g (C.mul_congr hu hv hu' hv' hb hb' (hg he) (hg hf))
  smul_congr := fun hu hv hu' hv' hb hb' he hf =>
    congrArg x (C.smul_congr hu hv hu' hv' hb hb' (hg he) (hx hf))

end ActionCalculus
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
