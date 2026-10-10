import OAI.MathematicalPhysics.Transonic.Exterior.BarrierTrace
import OAI.MathematicalPhysics.Transonic.Exterior.Weight

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open FixedInterval

def exteriorWeights (Q : ℤ) (sig kap root : Box) : BarrierWeights :=
  let h := scale (-1) 256 root
  let hs := mul Q h h
  let h3 := mul Q hs h
  {p0 := sub (oneBox Q) sig
   p1 := mul Q h (sub (scale 3 1 sig) (oneBox Q))
   p2 := mul Q hs (scale (-3) 1 sig)
   p3 := mul Q h3 sig
   a10 := mul Q (mul Q h (sub (oneBox Q) (rationalWide Q 3 5)))
     (sub (scale (-2) 1 kap) (natBox Q 3))
   a11 := mul Q hs (add (scale 4 5 kap) (rationalWide Q 18 5))
   a20 := mul Q h (sub (scale (-2) 1 kap) (rationalWide Q 18 5))
   a21 := mul Q hs (sub (scale 2 1 kap) (rationalWide Q 9 5))
   a30 := mul Q h (add (scale 12 5 kap) (rationalWide Q 9 5))
   a31 := mul Q hs (scale (-12) 5 kap)
   a40 := mul Q h (scale (-3) 5 kap)
   a41 := mul Q hs (scale 3 5 kap)}

lemma exteriorWeights_hold {Q : ℤ} (hQ : 0<Q) {sig kap root : Box} {sigma kappa d : ℝ}
    (hsi : Holds Q sig sigma) (hk : Holds Q kap kappa) (hr : Holds Q root d) :
    BarrierWeightsHold Q (exteriorWeights Q sig kap root) (-d/256) sigma kappa (3/5) := by
  have hh := holds_scale (a:= -1) (b:=256) (by norm_num) hr
  have hs := holds_mul hQ hh hh
  have h3 := holds_mul hQ hs hh
  have h18 := holds_rationalWide (a:=18) (b:=5) hQ (by norm_num)
  have h9 := holds_rationalWide (a:=9) (b:=5) hQ (by norm_num)
  have hc := holds_rationalWide (a:=3) (b:=5) hQ (by norm_num)
  constructor
  · exact holds_sub (holds_oneBox Q) hsi
  · convert holds_mul hQ hh (holds_sub (holds_scale (a:=3) (b:=1) (by norm_num) hsi) (holds_oneBox Q)) using 1 <;>
      norm_num [exteriorWeights,p1] ; ring
  · convert holds_mul hQ hs (holds_scale (a:= -3) (b:=1) (by norm_num) hsi) using 1 <;>
      norm_num [exteriorWeights,p2] ; ring_nf ; simp
  · convert holds_mul hQ h3 hsi using 1 <;> norm_num [exteriorWeights,p3] ; ring
  · convert holds_mul hQ (holds_mul hQ hh (holds_sub (holds_oneBox Q) hc))
      (holds_sub (holds_scale (a:= -2) (b:=1) (by norm_num) hk) (holds_natBox Q 3)) using 1 <;>
      norm_num [exteriorWeights,i10] ; ring
  · convert holds_mul hQ hs (holds_add (holds_scale (a:=4) (b:=5) (by norm_num) hk) h18) using 1 <;>
      norm_num [exteriorWeights,i11] ; ring_nf ; simp
  · convert holds_mul hQ hh (holds_sub (holds_scale (a:= -2) (b:=1) (by norm_num) hk) h18) using 1 <;>
      norm_num [exteriorWeights,i20] ; ring
  · convert holds_mul hQ hs (holds_sub (holds_scale (a:=2) (b:=1) (by norm_num) hk) h9) using 1 <;>
      norm_num [exteriorWeights,i21] ; ring
  · convert holds_mul hQ hh (holds_add (holds_scale (a:=12) (b:=5) (by norm_num) hk) h9) using 1 <;>
      norm_num [exteriorWeights,i30] ; ring
  · convert holds_mul hQ hs (holds_scale (a:= -12) (b:=5) (by norm_num) hk) using 1 <;>
      norm_num [exteriorWeights,i31] ; ring_nf ; simp
  · convert holds_mul hQ hh (holds_scale (a:= -3) (b:=5) (by norm_num) hk) using 1 <;>
      norm_num [exteriorWeights,i40] ; ring
  · convert holds_mul hQ hs (holds_scale (a:=3) (b:=5) (by norm_num) hk) using 1 <;>
      norm_num [exteriorWeights,i41] ; ring_nf ; simp
end SepticProfile.ExteriorJet

end
end

end OAI
