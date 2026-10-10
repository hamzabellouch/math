import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
namespace SepticProfile.FixedInterval
lemma lower_of_integer {Q : ℤ} (hQ : 0<Q) {d q : ℤ} (hd : 0<d)
    {b : Box} {a : ℝ} (ha : Holds Q b a)
    (hh : q*Q≤d*(b.center-b.radius)) : (q : ℝ)/d≤a := by
  have hQ' : 0<(Q : ℝ) := by exact_mod_cast hQ
  have hd' : 0<(d : ℝ) := by exact_mod_cast hd
  have hb := (bounds ha).1
  have hh' : (q : ℝ)*Q≤(d : ℝ)*((b.center : ℝ)-b.radius) := by exact_mod_cast hh
  have hlo : (q : ℝ)*Q≤(a*d)*Q := by
    calc
      _ ≤ (d : ℝ)*((b.center : ℝ)-b.radius) := hh'
      _ ≤ (d : ℝ)*((Q : ℝ)*a) := mul_le_mul_of_nonneg_left hb hd'.le
      _ = _ := by ring
  exact (div_le_iff₀ hd').mpr ((mul_le_mul_iff_left₀ hQ').mp hlo)
end SepticProfile.FixedInterval



end

end OAI
