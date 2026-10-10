import OAI.Analysis.Laughlin.FourBody.RadicalCancellation
import OAI.Analysis.Laughlin.Pair.Conjugation

namespace OAI

namespace Laughlin.Spin

theorem source_L_radical_cancellation (D r p x y j k : ℕ) (hor : Odd r)
    (hT : p+j+k=D) :
    Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) * fourBodyRadical r D D p j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((p.factorial : ℝ)*j.factorial*k.factorial) := by
  let e : ℤ := ((1 : ℤ)-2*D+r)/2
  have he : e*2=(1 : ℤ)-2*D+r := by
    rcases hor with ⟨a,ha⟩
    dsimp [e]; omega
  have hTr : (p : ℤ)+j+k=D := by exact_mod_cast hT
  have hpow : (2 : ℝ)^((1 : ℤ)-j-k-D+r) / (2 : ℝ)^p = ((2 : ℝ)^e)^2 := by
    rw [← zpow_natCast,← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [show (1 : ℤ)-j-k-D+r-(p : ℤ)=e*2 by omega,zpow_mul]
    norm_num
  have hsq : (Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k)^2 =
      (Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial))^2 := by
    simp only [fourBodyRadical,mul_pow]
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by unfold sourceCopyWeight; positivity)]
    simp only [Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one]
    calc
      _ = ((2 : ℝ)^((1 : ℤ)-j-k-D+r)/(2 : ℝ)^p) *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by
        field_simp
      _ = ((2 : ℝ)^e)^2 *
        (((p.factorial : ℝ)*j.factorial*k.factorial)^2 /
          ((r.factorial : ℝ)*(D-r).factorial*x.factorial*y.factorial*j.factorial*k.factorial)) := by rw [hpow]
      _ = _ := by unfold sourceCopyWeight; field_simp
  have hl : 0 ≤ Real.sqrt ((p.factorial : ℝ)/((2 : ℝ)^p*x.factorial*y.factorial)) *
      fourBodyRadical r D D p j k := by unfold fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
      (2 : ℝ)^e * ((p.factorial : ℝ)*j.factorial*k.factorial) := by positivity
  nlinarith only [hsq,hl,hr]

noncomputable def limitSlaterTerm (D r x y j k : ℕ) : ℝ :=
  (Real.sqrt 2 * pairLimitCoefficient (x+y-1) x y) *
    fourBodyLimitCoefficient r D D (x+y-1) j k

theorem limitSlaterTerm_rational (D r x y j k : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hxy : x < y) (hT : x+y+j+k=D+1) :
    limitSlaterTerm D r x y j k =
      Real.sqrt (sourceCopyWeight D r / ((x.factorial : ℝ)*y.factorial*j.factorial*k.factorial)) *
        (2 : ℝ)^(((1 : ℤ)-2*D+r)/2) *
        ((x : ℝ)-y) * ((x+y-1).factorial : ℝ)*j.factorial*k.factorial *
        (Certificate.V r D D (x+y-1) j k : ℝ) := by
  have hp : x+y-1+j+k=D := by omega
  rw [limitSlaterTerm,source_fourBody_radical_coefficient r D D (x+y-1) j k hr (le_refl _) hp]
  rw [pairLimitCoefficient,ite_eq_left (by omega : x+y=x+y-1+1)]
  have hc := source_L_radical_cancellation D r (x+y-1) x y j k hor hp
  calc
    _ = ((x : ℝ)-y)*(Certificate.V r D D (x+y-1) j k : ℝ) *
      (Real.sqrt (((x+y-1).factorial : ℝ)/((2 : ℝ)^(x+y-1)*x.factorial*y.factorial)) *
        fourBodyRadical r D D (x+y-1) j k) := by
      simp only [Nat.cast_ofNat]
      field_simp
    _ = _ := by rw [hc]; ring

end Laughlin.Spin

end OAI
