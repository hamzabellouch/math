import OAI.MathematicalPhysics.Transonic.Exterior.Polynomial
import OAI.MathematicalPhysics.Transonic.Exterior.Range
import OAI.MathematicalPhysics.Transonic.Exterior.Step

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open FixedInterval PowerSeries
structure BarrierWeights where
  (p0 p1 p2 p3 a10 a11 a20 a21 a30 a31 a40 a41 : Box)
structure BarrierWeightsHold (Q : ℤ) (a : BarrierWeights) (h sigma kappa c : ℝ) : Prop where
  p0 : Holds Q a.p0 (p0 sigma)
  p1 : Holds Q a.p1 (h*p1 sigma)
  p2 : Holds Q a.p2 (h^2*p2 sigma)
  p3 : Holds Q a.p3 (h^3*p3 sigma)
  a10 : Holds Q a.a10 (h*i10 kappa c)
  a11 : Holds Q a.a11 (h^2*i11 kappa c)
  a20 : Holds Q a.a20 (h*i20 kappa c)
  a21 : Holds Q a.a21 (h^2*i21 kappa c)
  a30 : Holds Q a.a30 (h*i30 kappa c)
  a31 : Holds Q a.a31 (h^2*i31 kappa c)
  a40 : Holds Q a.a40 (h*i40 kappa c)
  a41 : Holds Q a.a41 (h^2*i41 kappa c)
def barrierResidualBox (Q : ℤ) (a : BarrierWeights) (t : BarrierTrace.Trace) (n : ℕ) : Box :=
  neg (add (add (add (add (add (add (add (add (add (add (add
    (termBox Q ((n:ℤ)+3) a.p0 (t.b (n+3)) (t.c (n+3)))
    (termBox Q ((n:ℤ)+2) a.p1 (t.b (n+2)) (t.c (n+2))))
    (termBox Q ((n:ℤ)+1) a.p2 (t.b (n+1)) (t.c (n+1))))
    (termBox Q (n:ℤ) a.p3 (t.b n) (t.c n)))
    (mul Q a.a10 (t.u (n+2))))
    (mul Q a.a11 (t.u (n+1))))
    (mul Q a.a20 (t.b (n+2))))
    (mul Q a.a21 (t.b (n+1))))
    (mul Q a.a30 (t.c (n+2))))
    (mul Q a.a31 (t.c (n+1))))
    (mul Q a.a40 (t.d (n+2))))
    (mul Q a.a41 (t.d (n+1))))

lemma barrierResidual_enclosed {Q : ℤ} (hQ : 0<Q) (a : BarrierWeights)
    (h sigma kappa c : ℝ) (ha : BarrierWeightsHold Q a h sigma kappa c)
    (t : BarrierTrace.Trace) (w : Series) (n : ℕ)
    (hu : ∀ j, Holds Q (t.u j) (coeff j w))
    (hb : ∀ j, Holds Q (t.b j) (coeff j (w^2)))
    (hc : ∀ j, Holds Q (t.c j) (coeff j (w^3)))
    (hd : ∀ j, Holds Q (t.d j) (coeff j (w^4))) :
    Holds Q (barrierResidualBox Q a t n) (-coeff (n+2) (scaledResidual h sigma kappa c w)) := by
  rw [scaledResidual_coeff]
  have t0 := termBox_enclosed hQ ((n:ℤ)+3) ha.p0 (hb (n+3)) (hc (n+3))
  have t1 := termBox_enclosed hQ ((n:ℤ)+2) ha.p1 (hb (n+2)) (hc (n+2))
  have t2 := termBox_enclosed hQ ((n:ℤ)+1) ha.p2 (hb (n+1)) (hc (n+1))
  have t3 := termBox_enclosed hQ ((n:ℤ)) ha.p3 (hb (n)) (hc (n))
  have t10 := holds_mul hQ ha.a10 (hu (n+2))
  have t11 := holds_mul hQ ha.a11 (hu (n+1))
  have t20 := holds_mul hQ ha.a20 (hb (n+2))
  have t21 := holds_mul hQ ha.a21 (hb (n+1))
  have t30 := holds_mul hQ ha.a30 (hc (n+2))
  have t31 := holds_mul hQ ha.a31 (hc (n+1))
  have t40 := holds_mul hQ ha.a40 (hd (n+2))
  have t41 := holds_mul hQ ha.a41 (hd (n+1))
  have r1 := holds_add t0 t1
  have r2 := holds_add r1 t2
  have r3 := holds_add r2 t3
  have r4 := holds_add r3 t10
  have r5 := holds_add r4 t11
  have r6 := holds_add r5 t20
  have r7 := holds_add r6 t21
  have r8 := holds_add r7 t30
  have r9 := holds_add r8 t31
  have r10 := holds_add r9 t40
  have r11 := holds_add r10 t41
  have hh := holds_neg r11
  simpa only [barrierResidualBox,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_ofNat] using hh
end SepticProfile.ExteriorJet

end
end

end OAI
