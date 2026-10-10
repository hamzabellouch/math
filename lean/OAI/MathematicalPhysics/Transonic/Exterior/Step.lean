import OAI.MathematicalPhysics.Transonic.Exterior.Scaled
import OAI.MathematicalPhysics.Transonic.Exterior.Trace

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open PowerSeries Finset FixedInterval

structure Weights where
  (p0 p1 p2 p3 a11 a20 a21 a30 a31 a40 a41 : Box)

structure WeightsHold (Q : ℤ) (a : Weights) (h sigma kappa c : ℝ) : Prop where
  p0 : Holds Q a.p0 (p0 sigma)
  p1 : Holds Q a.p1 (h*p1 sigma)
  p2 : Holds Q a.p2 (h^2*p2 sigma)
  p3 : Holds Q a.p3 (h^3*p3 sigma)
  a11 : Holds Q a.a11 (h^2*i11 kappa c)
  a20 : Holds Q a.a20 (h*i20 kappa c)
  a21 : Holds Q a.a21 (h^2*i21 kappa c)
  a30 : Holds Q a.a30 (h*i30 kappa c)
  a31 : Holds Q a.a31 (h^2*i31 kappa c)
  a40 : Holds Q a.a40 (h*i40 kappa c)
  a41 : Holds Q a.a41 (h^2*i41 kappa c)

def termBox (Q n : ℤ) (a b c : Box) : Box :=
  scale n 1 (mul Q a (sub b (scale 1 3 c)))

def stepBox (Q : ℤ) (a : Weights) (n : ℕ) (sq cu qu : ℕ → Box) (sr : Box) : Box :=
  add (add (add (add (add (add (add (add (add (add
    (termBox Q (n+1) a.p0 sr (cu (n+1)))
    (termBox Q n a.p1 (sq n) (cu n)))
    (termBox Q (n-1) a.p2 (sq (n-1)) (cu (n-1))))
    (termBox Q (n-2) a.p3 (sq (n-2)) (cu (n-2))))
    a.a11)
    (mul Q a.a20 (sq n)))
    (mul Q a.a21 (sq (n-1))))
    (mul Q a.a30 (cu n)))
    (mul Q a.a31 (cu (n-1))))
    (mul Q a.a40 (qu n)))
    (mul Q a.a41 (qu (n-1)))

lemma termBox_enclosed {Q : ℤ} (hQ : 0<Q) (n : ℤ) {a b c : Box} {x y z : ℝ}
    (ha : Holds Q a x) (hb : Holds Q b y) (hc : Holds Q c z) :
    Holds Q (termBox Q n a b c) (x*n*(y-z/3)) := by
  have hh := holds_scale (a:=n) (b:=1) (by norm_num) (holds_mul hQ ha
    (holds_sub hb (holds_scale (a:=1) (b:=3) (by norm_num) hc)))
  unfold termBox
  convert hh using 1 ; push_cast ; ring

lemma stepBox_enclosed {Q : ℤ} (hQ : 0<Q) (a : Weights) (h sigma kappa c : ℝ)
    (ha : WeightsHold Q a h sigma kappa c) (n : ℕ) (sq cu qu : ℕ → Box) (sr : Box)
    (S C B : ℕ → ℝ) (R : ℝ)
    (hsq : ∀ j, n-2≤j → j≤n → Holds Q (sq j) (S j))
    (hcu : ∀ j, n-2≤j → j≤n+1 → Holds Q (cu j) (C j))
    (hqu : ∀ j, n-1≤j → j≤n → Holds Q (qu j) (B j))
    (hsr : Holds Q sr R) :
    Holds Q (stepBox Q a n sq cu qu sr) (scaledRatioStep h sigma kappa c n S C B R) := by
  have t0 := termBox_enclosed hQ ((n:ℤ)+1) ha.p0 hsr (hcu (n+1) (by omega) (by omega))
  have t1 := termBox_enclosed hQ (n:ℤ) ha.p1 (hsq n (by omega) le_rfl) (hcu n (by omega) (by omega))
  have t2 := termBox_enclosed hQ ((n:ℤ)-1) ha.p2 (hsq (n-1) (by omega) (by omega)) (hcu (n-1) (by omega) (by omega))
  have t3 := termBox_enclosed hQ ((n:ℤ)-2) ha.p3 (hsq (n-2) le_rfl (by omega)) (hcu (n-2) le_rfl (by omega))
  have t20 := holds_mul hQ ha.a20 (hsq n (by omega) le_rfl)
  have t21 := holds_mul hQ ha.a21 (hsq (n-1) (by omega) (by omega))
  have t30 := holds_mul hQ ha.a30 (hcu n (by omega) (by omega))
  have t31 := holds_mul hQ ha.a31 (hcu (n-1) (by omega) (by omega))
  have t40 := holds_mul hQ ha.a40 (hqu n (by omega) le_rfl)
  have t41 := holds_mul hQ ha.a41 (hqu (n-1) le_rfl (by omega))
  have hh := holds_add (holds_add (holds_add (holds_add (holds_add (holds_add
    (holds_add (holds_add (holds_add (holds_add t0 t1) t2) t3) ha.a11) t20) t21) t30) t31) t40) t41
  simpa only [stepBox,scaledRatioStep,Int.cast_add,Int.cast_natCast,Int.cast_one,
    Int.cast_sub,Int.cast_ofNat] using hh

end SepticProfile.ExteriorJet

end
end

end OAI
