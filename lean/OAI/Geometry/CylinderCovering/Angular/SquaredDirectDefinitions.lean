import OAI.Geometry.CylinderCovering.Angular.CapsDefinitions

namespace OAI

namespace AngularEstimates

structure SquaredDirectStatement : Prop where

  selected_square_remainder_identity
      {k x q M B s S y : ℝ}
      (hsec : 2 * B - M ^ 2 = 1 - k ^ 4)
      (hS : S = s - k * x * M) (hy : y = q * S + k * x * B) :
      S ^ 2 - (s ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2) =
        2 * k * x * S * (q - M) - k ^ 6 * x ^ 2

  selected_square_remainder_bound
      {k x q M B s S y : ℝ}
      (hk : 0 ≤ k) (hk1 : k ≤ 1) (hx : |x| ≤ 1) (hS2 : |S| ≤ 2)
      (hqM : |q - M| ≤ k ^ 2)
      (hsec : 2 * B - M ^ 2 = 1 - k ^ 4)
      (hS : S = s - k * x * M) (hy : y = q * S + k * x * B) :
      |S ^ 2 - (s ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)| ≤ 5 * k ^ 3

  squared_profile_replacement
      {k q y : ℝ} (hk : 0 ≤ k) (hq : |q| ≤ 1) (hy : |y| ≤ 1)
      (hclose : |q - 2 * y| ≤ 6 * k) :
      |(q ^ 2 + q ^ 4) / 4 - (y ^ 2 + 4 * y ^ 4)| ≤ 27 * k

  squared_failure_balance
      {k x y u S T : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1)
      (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hu : |u| ≤ k)
      (hfirst : |S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)|
        ≤ 5 * k ^ 3)
      (hsecond : |T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2)|
        ≤ 5 * k ^ 3)
      (hS : 1 / 4 < S ^ 2) (hT : 1 / 4 < T ^ 2) :
      |u - 2 * k * x * y| ≤ 7 * k ^ 2

  squared_sum_remainder
      {k x y u S T : ℝ} (hk : 0 ≤ k)
      (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hu : |u| ≤ k)
      (hbalance : |u - 2 * k * x * y| ≤ 7 * k ^ 2)
      (hfirst : |S ^ 2 - (1 / 4 + u + u ^ 2 - 2 * k * x * y + k ^ 2 * x ^ 2)|
        ≤ 5 * k ^ 3)
      (hsecond : |T ^ 2 - (1 / 4 - u + u ^ 2 + 2 * k * x * y + k ^ 2 * y ^ 2)|
        ≤ 5 * k ^ 3) :
      |S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2))|
        ≤ 52 * k ^ 3

  selected_slope_replacement
      {k x q M B u S y : ℝ} (hk : 0 ≤ k)
      (hx : |x| ≤ 1) (hq : |q| ≤ 1) (hM : |M| ≤ 1) (hB : |B| ≤ 1)
      (hu : |u| ≤ k)
      (hS : S = 1 / 2 + u - k * x * M) (hy : y = q * S + k * x * B) :
      |q - 2 * y| ≤ 6 * k

  squared_sector_data
      {k l r q : ℝ} (hl : -1 ≤ l) (hr : r ≤ 1)
      (hlq : l ≤ q) (hqr : q ≤ r) (hwidth : r - l = 2 * k ^ 2) :
      |(l + r) / 2| ≤ 1 ∧ |(1 + l * r) / 2| ≤ 1 ∧ |q| ≤ 1 ∧
        |q - (l + r) / 2| ≤ k ^ 2 ∧
        2 * ((1 + l * r) / 2) - ((l + r) / 2) ^ 2 = 1 - k ^ 4

  squared_sum_quotient_remainder
      {k x y S T : ℝ} (hk : 0 < k)
      (herror : |S ^ 2 + T ^ 2 - (1 / 2 + k ^ 2 * (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2))|
        ≤ 52 * k ^ 3) :
      |(S ^ 2 + T ^ 2 - 1 / 2) / k ^ 2 - (x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2)|
        ≤ 52 * k

  squared_profiles_sum_replacement
      {k x y p q : ℝ} (hk : 0 ≤ k)
      (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hp : |p| ≤ 1) (hq : |q| ≤ 1)
      (hpclose : |p - 2 * x| ≤ 6 * k) (hqclose : |q - 2 * y| ≤ 6 * k) :
      |(q ^ 2 + q ^ 4) / 4 + (p ^ 2 + p ^ 4) / 4 -
        (x ^ 2 + y ^ 2 + 4 * (x ^ 4 + y ^ 4))| ≤ 54 * k

  selected_sectors_squared_cap
      {k x y s l r l' r' q p S T : ℝ}
      (hk : 0 < k) (hkSmall : k ≤ 1 / 20000)
      (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
      (hl : -1 ≤ l) (hr : r ≤ 1) (hlq : l ≤ q) (hqr : q ≤ r)
      (hwidth : r - l = 2 * k ^ 2)
      (hl' : -1 ≤ l') (hr' : r' ≤ 1) (hlp : l' ≤ p) (hpr : p ≤ r')
      (hwidth' : r' - l' = 2 * k ^ 2)
      (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
      (hS : S = s - k * x * ((l + r) / 2))
      (hyEq : y = q * S + k * x * ((1 + l * r) / 2))
      (hT : T = 1 - s + k * y * ((l' + r') / 2))
      (hxEq : x = p * T - k * y * ((1 + l' * r') / 2)) :
      S ^ 2 ≤ 1 / 4 + k ^ 2 * ((q ^ 2 + q ^ 4) / 4 + 1 / 240) ∨
        T ^ 2 ≤ 1 / 4 + k ^ 2 * ((p ^ 2 + p ^ 4) / 4 + 1 / 240)

  squared_radius_source_formula (k q : ℝ) :
      AngularCaps.squaredRadius (2 * k) (1 / 960) q =
        Real.sqrt (1 / 4 + k ^ 2 * ((q ^ 2 + q ^ 4) / 4 + 1 / 240))

  selected_sectors_cap_alternative
      {k x y s l r l' r' q p S T : ℝ}
      (hk : 0 < k) (hkSmall : k ≤ 1 / 20000)
      (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
      (hl : -1 ≤ l) (hr : r ≤ 1) (hlq : l ≤ q) (hqr : q ≤ r)
      (hwidth : r - l = 2 * k ^ 2)
      (hl' : -1 ≤ l') (hr' : r' ≤ 1) (hlp : l' ≤ p) (hpr : p ≤ r')
      (hwidth' : r' - l' = 2 * k ^ 2)
      (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
      (hS : S = s - k * x * ((l + r) / 2))
      (hyEq : y = q * S + k * x * ((1 + l * r) / 2))
      (hT : T = 1 - s + k * y * ((l' + r') / 2))
      (hxEq : x = p * T - k * y * ((1 + l' * r') / 2)) :
      S ∈ Set.Icc 0 (AngularCaps.squaredRadius (2 * k) (1 / 960) q) ∨
        T ∈ Set.Icc 0 (AngularCaps.squaredRadius (2 * k) (1 / 960) p)

end AngularEstimates

end OAI
