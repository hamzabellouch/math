import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyEulerSeed
import OAI.MathematicalPhysics.Transonic.Shooting.RegularGlobalControl

namespace OAI

noncomputable section

namespace SepticProfile.SonicShooting
open Set SourceFamily RegularContinuation

structure Family where
  germ : UniformGerm
  e : ℝ
  e_pos : 0<e
  e_lt : e<1/3
  e_radius : |SourceEuler.changeOfVariable (1/500) e|<germ.radius
  germ_window : ∀ p x, |x|≤|SourceEuler.changeOfVariable (1/500) e| →
    0<germ.realFunction p x ∧ 1/2<(germ.V p (x:ℂ)).re
  u : Parameter → ℝ → ℝ
  v : Parameter → ℝ → ℝ
  u_cont : Continuous (fun p : Parameter × ↥(Icc e (5/6)) => u p.1 p.2)
  v_cont : Continuous (fun p : Parameter × ↥(Icc (0:ℝ) (9/100)) => v p.1 p.2)
  u_start : ∀ p, u p e=germ.eulerFunction p e
  v_start : ∀ p, v p 0=u p (5/6)
  u_der : ∀ p x, x ∈ Icc e (5/6) → HasDerivWithinAt (u p)
    (EulerContinuation.N (kap p) x (clamp 0 (1-e/1000) (u p x))/
      EulerContinuation.D (sig p) x (clamp 0 (1-e/1000) (u p x))) (Icc e (5/6)) x
  v_der : ∀ p x, x ∈ Icc (0:ℝ) (9/100) → HasDerivWithinAt (v p)
    (IntegerPolynomial.globalField (sig p) (kap p) x (v p x)) (Icc 0 (9/100)) x
  left_bound : v leftParameter (9/100)<673/1000
  right_bound : 858/1000<v rightParameter (9/100)

end SepticProfile.SonicShooting

end

end OAI
