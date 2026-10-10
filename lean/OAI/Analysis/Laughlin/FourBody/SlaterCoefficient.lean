import OAI.Analysis.Laughlin.FourBody.SlaterRadical

namespace OAI

namespace Laughlin.Spin

noncomputable def limitSlaterCoefficient (D r a b c d : ℕ) : ℝ :=
  limitSlaterTerm D r a b c d - limitSlaterTerm D r a c b d +
  limitSlaterTerm D r a d b c + limitSlaterTerm D r b c a d -
  limitSlaterTerm D r b d a c + limitSlaterTerm D r c d a b

theorem source_fourBody_Slater_coefficient (D r a b c d : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hT : a+b+c+d=D+1) :
    limitSlaterCoefficient D r a b c d =
      Real.sqrt (sourceCopyWeight D r / ((a.factorial : ℝ)*b.factorial*c.factorial*d.factorial)) *
        (Certificate.L D r (a,b,c,d) : ℝ) := by
  unfold limitSlaterCoefficient
  rw [limitSlaterTerm_rational D r a b c d hr hor hab hT,
    limitSlaterTerm_rational D r a c b d hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r a d b c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r b c a d hr hor hbc (by omega),
    limitSlaterTerm_rational D r b d a c hr hor (by omega) (by omega),
    limitSlaterTerm_rational D r c d a b hr hor hcd (by omega)]
  have h1 : (a.factorial : ℝ)*c.factorial*b.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h2 : (a.factorial : ℝ)*d.factorial*b.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h3 : (b.factorial : ℝ)*c.factorial*a.factorial*d.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h4 : (b.factorial : ℝ)*d.factorial*a.factorial*c.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  have h5 : (c.factorial : ℝ)*d.factorial*a.factorial*b.factorial =
      (a.factorial : ℝ)*b.factorial*c.factorial*d.factorial := by ring
  rw [h1,h2,h3,h4,h5]
  simp only [Certificate.L]
  push_cast
  ring

end Laughlin.Spin

end OAI
