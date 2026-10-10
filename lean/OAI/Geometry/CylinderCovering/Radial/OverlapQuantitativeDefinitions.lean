import OAI.Geometry.CylinderCovering.Radial.OverlapDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialOverlapQuantitative

open RadialOverlap

def CanonicalStatement : Prop :=
  ∀ eps x y t p q : ℝ, 0 < eps → |x| ≤ 2 → |y| ≤ 2 →
    |p| ≤ 1 → |q| ≤ 1 → RootEquations eps x y t p q →
    1 ≤ rho eps x t q → 1 ≤ sigma eps y t p →
    |t| ≤ 2 * eps ∧ |x - p| ≤ 3 * eps ∧ |y - q| ≤ 3 * eps ∧
    rho eps x t q + sigma eps y t p - 2 =
      eps * ((x - p) * q - (y - q) * p) ∧
    0 ≤ rho eps x t q - 1 ∧
    rho eps x t q - 1 ≤ rho eps x t q + sigma eps y t p - 2 ∧
    0 ≤ sigma eps y t p - 1 ∧
    sigma eps y t p - 1 ≤ rho eps x t q + sigma eps y t p - 2 ∧
    rho eps x t q + sigma eps y t p - 2 ≤ 6 * eps ^ 2 ∧
    |rho eps x t q - sigma eps y t p| ≤ 6 * eps ^ 2 ∧
    |t - eps * p * q| ≤ 3 * eps ^ 2 ∧
    eps * (x * q - y * p) ≤
      eps ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * eps ^ 3 ∧
    eps * (x * q - y * p) <
      (RadialCaps.cubicCap 12 eps p - 1) + (RadialCaps.cubicCap 12 eps q - 1)

def PhysicalStatement : Prop :=
  ∀ tau x y z p q : ℝ, 0 < tau →
    |x| ≤ 1 - (1 / Real.sqrt 2) * z →
    |y| ≤ 1 + (1 / Real.sqrt 2) * z → |p| ≤ 1 → |q| ≤ 1 →
    x = (1 - (1 / Real.sqrt 2) * z) * q -
      ((1 / Real.sqrt 2) * tau) * y * (1 - q ^ 2) / 2 →
    y = (1 + (1 / Real.sqrt 2) * z) * p +
      ((1 / Real.sqrt 2) * tau) * x * (1 - p ^ 2) / 2 →
    tau * x * p ≤ z → z ≤ tau * y * q →
    (tau * (y * q - x * p) ≤
      (1 / Real.sqrt 2) * tau ^ 2 * (RadialCaps.H p + RadialCaps.H q) +
        9 * (1 / Real.sqrt 2) ^ 2 * tau ^ 3) ∧
    (tau * (y * q - x * p) <
      (tau ^ 2 * (1 / Real.sqrt 2) * RadialCaps.H p + 10 * tau ^ 3) +
      (tau ^ 2 * (1 / Real.sqrt 2) * RadialCaps.H q + 10 * tau ^ 3))

def Statement : Prop := CanonicalStatement ∧ PhysicalStatement

end CylinderCovering.RadialOverlapQuantitative

end

end OAI
