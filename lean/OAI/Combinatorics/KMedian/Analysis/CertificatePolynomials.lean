import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Certificates
noncomputable def p (X : ℝ) : ℝ := (1651507 / 6250000) + (8026757 / 50000000) * X + (1150379 / 20000000) * X ^ 2 + (262741 / 20000000) * X ^ 3 + (228387 / 50000000) * X ^ 4

noncomputable def v (X : ℝ) : ℝ := (10848493 / 6250000) + (-52832269 / 100000000) * X + (-16191093 / 100000000) * X ^ 2 + (-1721469 / 50000000) * X ^ 3 + (-277397 / 25000000) * X ^ 4

noncomputable def k (X : ℝ) : ℝ := (767 / 10000) + (141 / 2500) * X + (71 / 5000) * X ^ 2 + (123 / 5000) * X ^ 3

noncomputable def h (X : ℝ) : ℝ := (197 / 500) + (-21 / 50) * X ^ 2 + (1 / 25) * X ^ 3

noncomputable def pSeries (X : ℝ) : ℝ := (23036089103 / 87178291200) + (1750134643 / 10897286400) * X + (413838773 / 7264857600) * X ^ 2 + (319059131 / 21794572800) * X ^ 3 + (5755571 / 1937295360) * X ^ 4 + (7559 / 15135120) * X ^ 5 + (18619 / 259459200) * X ^ 6 + (32639 / 3632428800) * X ^ 7 + (9829 / 9686476800) * X ^ 8 + (41 / 435891456) * X ^ 9 + (23 / 1981324800) * X ^ 10 + (1 / 7264857600) * X ^ 11 + (1 / 6706022400) * X ^ 12

noncomputable def aSeries (X : ℝ) : ℝ := (150119537 / 86486400) + (-329086987 / 622702080) * X + (-20001539 / 124540416) * X ^ 2 + (-118239629 / 3113510400) * X ^ 3 + (-2532221 / 345945600) * X ^ 4 + (-7613 / 6406400) * X ^ 5 + (-9601 / 57657600) * X ^ 6 + (-1517 / 74131200) * X ^ 7 + (-1181 / 518918400) * X ^ 8 + (-31 / 148262400) * X ^ 9 + (-79 / 3113510400) * X ^ 10 + (-1 / 3113510400) * X ^ 11 + (-1 / 3113510400) * X ^ 12

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0
noncomputable def d (s : Bool) : ℝ := if s then 2 / 5 else 13 / 25
noncomputable def H (s : Bool) (X : ℝ) : ℝ := if s then 1 / 4 else h X
noncomputable def c (s : Bool) (X : ℝ) : ℝ := 1 - bit s * p X
noncomputable def N (s : Bool) (X : ℝ) : ℝ := c s X - (1 - bit s) * k X
noncomputable def l (s : Bool) (X : ℝ) : ℝ := c s X + 1 - v X + bit s * p X * (1 - X)
noncomputable def hh (s : Bool) : ℝ := 8 / 5 + (2 / 5) * d s
noncomputable def uZero (s : Bool) : ℝ := d s / hh s
noncomputable def uOne (s : Bool) : ℝ := (2 - bit s) * (1 + d s) / (2 * hh s)
noncomputable def Tk (X : ℝ) : ℝ := 4 * k X - (p X + 3 / 400000) * (1 + k X) ^ 2
noncomputable def T1 (X : ℝ) : ℝ := 1 - p X - (28 / 25) * p X * (2 - X) + (2 / 5) * (p X) ^ 2 * X * (2 - X)
noncomputable def T2 (X : ℝ) : ℝ := ((1 - p X)^2 - (19 / 50) * p X * X + p X * (1 - X)) * (2 - X) - 2 * (1-X) * (1-p X)
noncomputable def Q0 (s : Bool) (W X : ℝ) : ℝ := N s X - d s * v X + p X * W * (hh s * W - 2 * d s)
noncomputable def Q1 (s : Bool) (X : ℝ) : ℝ := N s X - (2-bit s) * p X * (1-X) - d s * (c s X * p X - l s X) - hh s * p X * (uOne s)^2
noncomputable def Y (s : Bool) (X : ℝ) : ℝ := N s X - p X * ((2-bit s) * (1-X) + (2-bit s)^2 / (32/5))
noncomputable def Yprime (X : ℝ) : ℝ := N false X + p X * ((8/5) * X^2 - 2)

noncomputable def B0 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  p X * X^2 * (((8/5) * v X + (2/5) * N s X) * ((i:ℝ)*(i-1)/6) +
    (8/5) * (2*p X*X) * (if i = 3 then 1 else 0)) - (1/5000) * X^2 * ((i:ℝ)*(i-1)/6)
noncomputable def B1 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  (c s X * H s X - (2-bit s)*p X*(1-X))*v X + N s X*l s X +
  ((c s X*H s X-(2-bit s)*p X*(1-X))*(2*p X*X) -
    (2-bit s)*p X*X*v X - N s X*(2-bit s)*p X*X) * ((i:ℝ)/3) -
  (2-bit s)*p X*X*(2*p X*X)*((i:ℝ)*(i-1)/6) -
  p X*X^2*(((8/5)*(v X-c s X*p X)+(2/5)*c s X*H s X)*((i:ℝ)*(i-1)/6) +
    (8/5)*(2*p X*X)*(if i = 3 then 1 else 0)) - 1/5000
noncomputable def B2 (s : Bool) (i : ℕ) (X : ℝ) : ℝ :=
  ((2-bit s)*p X*(1-X)-c s X*H s X)*(v X-c s X*p X) - c s X*H s X*l s X +
  (((2-bit s)*p X*(1-X)-c s X*H s X)*(2*p X*X) +
    (2-bit s)*p X*X*(v X-c s X*p X) + c s X*H s X*(2-bit s)*p X*X)*((i:ℝ)/3) +
  (2-bit s)*p X*X*(2*p X*X)*((i:ℝ)*(i-1)/6)
noncomputable def discr (s : Bool) (i : ℕ) (X : ℝ) : ℝ := 4 * B0 s i X * B2 s i X - (B1 s i X)^2
noncomputable def total (s : Bool) (i : ℕ) (X : ℝ) : ℝ := B0 s i X + B1 s i X + B2 s i X


end MetricKMedian.Certificates
end
end

end OAI
