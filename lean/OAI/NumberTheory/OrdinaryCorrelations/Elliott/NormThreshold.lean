import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgAdd
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.WeightMean
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AmplitudeSecondSum
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.TraceMean

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.Localization
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h ℓ L D₀ : ℕ}

lemma norm_threshold {u q t : ℝ} {m : ℕ} (hu : 0≤u) (ht : 0<t)
    (hm : 0 < m) (hq : u^(2*m)≤q) : u ≤ t+Real.sqrt q/t^(m-1) := by
  have hq0 : 0≤q := (pow_nonneg hu _).trans hq
  have htp : 0<t^(m-1) := pow_pos ht _
  by_cases hut : u≤t
  · exact hut.trans (le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg q) htp.le))
  · have htu : t ≤ u := (lt_of_not_ge hut).le
    have hp : t^(m-1)*u ≤ u^m := by
      have he : m=(m-1)+1 := by omega
      calc
        _ ≤ u^(m-1)*u := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htu _) hu
        _ = u^m := by nth_rw 2 [he]; rw [pow_succ]
    have hs : u^m ≤ Real.sqrt q := by
      apply Real.le_sqrt_of_sq_le
      simpa only [←pow_mul,Nat.mul_comm m 2] using hq
    have hb : u ≤ Real.sqrt q/t^(m-1) := (le_div_iff₀ htp).mpr (by nlinarith)
    linarith

def windowWeight (S : PrimeSystem) (D₀ : ℕ) (r : S.Residues) : ℝ :=
  ∑ x : Fin D₀,S.vertexWeight r (x.val:ℤ)

def windowSquare (S : PrimeSystem) (D₀ : ℕ) (r : S.Residues) : ℝ :=
  (D₀:ℝ)*∑ x : Fin D₀,S.vertexWeight r (x.val:ℤ)^2

lemma windowWeight_nonneg (r : S.Residues) : 0≤windowWeight S D₀ r :=
  sum_nonneg (fun _ _ => (S.vertexWeight_pos r _).le)
lemma windowSquare_nonneg (r : S.Residues) : 0≤windowSquare S D₀ r :=
  mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))

lemma windowWeight_sq_le (r : S.Residues) :
    (windowWeight S D₀ r)^2 ≤ windowSquare S D₀ r := by
  simpa only [windowWeight,windowSquare,one_mul,one_pow,sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] using
    sum_mul_sq_le_sq_mul_sq (R:=ℝ) (univ:Finset (Fin D₀)) (fun _=>1)
      (fun x=>S.vertexWeight r (x.val:ℤ))

lemma windowWeight_mean (S : PrimeSystem) (D₀ : ℕ) :
    avg (windowWeight S D₀) = (D₀:ℝ)*S.weightMean := by
  unfold windowWeight
  rw [OrdinaryCorrelations.SourceCylinder.avg_sum']
  simp only [vertexWeight_mean,sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma windowSquare_mean (S : PrimeSystem) (D₀ : ℕ) :
    avg (windowSquare S D₀) = (D₀:ℝ)^2*avg (fun r=>S.vertexWeight r 0^2) := by
  unfold windowSquare
  rw [avg_mul_left,OrdinaryCorrelations.SourceCylinder.avg_sum']
  simp only [vertexWeight_moment,sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma weighted_norm_average_le (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    (L D₀ m : ℕ) (hD : 0<D₀) (hm : 0 < m) (cut : S.Cutoffs T) (a : ℕ→ℂ)
    (t : ℝ) (ht : 0<t) (X : ℝ) (hX : 0<X) (z : ℤ) :
    (∑ n∈range ⌊X⌋₊, ‖symMatrix D h L cut a D₀ ((n:ℤ)+z)‖ *
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+z)))/X ≤
    t*((∑ n∈range ⌊X⌋₊,windowWeight S D₀ (S.integerResidues ((n:ℤ)+z)))/X) +
    Real.sqrt (((∑ n∈range ⌊X⌋₊,
      ((symMatrix D h L cut a D₀ ((n:ℤ)+z))^(2*m)).trace.re)/X)*
      ((∑ n∈range ⌊X⌋₊,windowSquare S D₀ (S.integerResidues ((n:ℤ)+z)))/X))/t^(m-1) := by
  let Q : ℕ→ℝ := fun n=>((symMatrix D h L cut a D₀ ((n:ℤ)+z))^(2*m)).trace.re
  let V : ℕ→ℝ := fun n=>windowWeight S D₀ (S.integerResidues ((n:ℤ)+z))
  let U : ℕ→ℝ := fun n=>windowSquare S D₀ (S.integerResidues ((n:ℤ)+z))
  have hQ (n : ℕ) : 0≤Q n :=
    (pow_nonneg (norm_nonneg _) _).trans (matrix_norm_moment D hh L cut a _ hD m)
  have hV (n : ℕ) : 0≤V n := windowWeight_nonneg _
  have hU (n : ℕ) : 0≤U n := windowSquare_nonneg _
  have hpoint (n : ℕ) := mul_le_mul_of_nonneg_right
    (norm_threshold (norm_nonneg _) ht hm (matrix_norm_moment D hh L cut a ((n:ℤ)+z) hD m)) (hV n)
  have hCS : ∑ n∈range ⌊X⌋₊,Real.sqrt (Q n)*V n ≤
      Real.sqrt ((∑ n∈range ⌊X⌋₊,Q n)*(∑ n∈range ⌊X⌋₊,U n)) := by
    apply Real.le_sqrt_of_sq_le
    apply (sum_mul_sq_le_sq_mul_sq (R:=ℝ) (range ⌊X⌋₊) (fun n=>Real.sqrt (Q n)) V).trans
    simp only [Real.sq_sqrt (hQ _)]
    apply mul_le_mul_of_nonneg_left _ (sum_nonneg (fun n hn=>hQ n))
    exact sum_le_sum (fun n hn=>windowWeight_sq_le _)
  have he : Real.sqrt ((∑ n∈range ⌊X⌋₊,Q n)*(∑ n∈range ⌊X⌋₊,U n))/X =
      Real.sqrt (((∑ n∈range ⌊X⌋₊,Q n)/X)*((∑ n∈range ⌊X⌋₊,U n)/X)) := by
    rw [_root_.div_mul_div_comm,Real.sqrt_div (mul_nonneg
      (sum_nonneg (fun n hn=>hQ n)) (sum_nonneg (fun n hn=>hU n))),Real.sqrt_mul_self hX.le]
  calc
    _ ≤ (∑ n∈range ⌊X⌋₊,(t+Real.sqrt (Q n)/t^(m-1))*V n)/X :=
      div_le_div_of_nonneg_right (sum_le_sum (fun n hn=>hpoint n)) hX.le
    _ = t*((∑ n∈range ⌊X⌋₊,V n)/X)+
      ((∑ n∈range ⌊X⌋₊,Real.sqrt (Q n)*V n)/X)/t^(m-1) := by
      simp_rw [add_mul,div_mul_eq_mul_div,sum_add_distrib,←mul_sum,←sum_div]
      ring
    _ ≤ t*((∑ n∈range ⌊X⌋₊,V n)/X)+
      (Real.sqrt ((∑ n∈range ⌊X⌋₊,Q n)*(∑ n∈range ⌊X⌋₊,U n))/X)/t^(m-1) := by
      apply _root_.add_le_add le_rfl
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hCS hX.le) (pow_nonneg ht.le _)
    _ = _ := by rw [he]

lemma weighted_norm_eventual (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    (L D₀ m : ℕ) (hD : 0<D₀) (hm : 0 < m) (cut : S.Cutoffs T) (a : ℕ→ℂ)
    (ha : ∀ d∈D.members,‖a d‖≤1) (t : ℝ) (ht : 0<t) (z : ℝ→ℤ)
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop,
    (∑ n∈range ⌊X⌋₊, ‖symMatrix D h L cut a D₀ ((n:ℤ)+z X)‖ *
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+z X)))/X ≤
    t*(D₀:ℝ)*S.weightMean + Real.sqrt ((D₀:ℝ)^3*
      NumericalLine.fullTraceSum D h (2*m) L cut*
      Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))/t^(m-1)+δ := by
  have htQ := trace_tendsto D hh (by omega : 0<2*m) L D₀ cut a z
  have htV := S.real_origin_tendsto (windowWeight S D₀) z
  have htU := S.real_origin_tendsto (windowSquare S D₀) z
  rw [windowWeight_mean] at htV
  rw [windowSquare_mean] at htU
  have htR := (tendsto_const_nhds (x:=t)).mul htV |>.add
    (((htQ.mul htU).sqrt).div_const (t^(m-1)))
  have hb := htR.eventually (eventually_le_nhds (by linarith :
    t*((D₀:ℝ)*S.weightMean)+Real.sqrt (traceMean D hh L (2*m) D₀ cut a*
      ((D₀:ℝ)^2*avg (fun r=>S.vertexWeight r 0^2))) / t^(m-1) <
    t*((D₀:ℝ)*S.weightMean)+Real.sqrt (traceMean D hh L (2*m) D₀ cut a*
      ((D₀:ℝ)^2*avg (fun r=>S.vertexWeight r 0^2))) / t^(m-1)+δ))
  have htrace0 := traceMean_nonneg D hh L D₀ m hD hm cut a
  have hfull0 : 0≤NumericalLine.fullTraceSum D h (2*m) L cut := sum_nonneg (fun _ _=>abs_nonneg _)
  have hlimit : traceMean D hh L (2*m) D₀ cut a *
      ((D₀:ℝ)^2*avg (fun r=>S.vertexWeight r 0^2)) ≤ (D₀:ℝ)^3*
        NumericalLine.fullTraceSum D h (2*m) L cut*
        Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter) := by
    calc
      _ ≤ ((D₀:ℝ)*NumericalLine.fullTraceSum D h (2*m) L cut)*
          ((D₀:ℝ)^2*Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter)) := by
        apply mul_le_mul (traceMean_le D hh L (2*m) D₀ cut a ha)
        · exact mul_le_mul_of_nonneg_left (S.vertexWeight_second_moment_source 0) (sq_nonneg _)
        · exact mul_nonneg (sq_nonneg _) (avg_nonneg (fun r=>sq_nonneg _))
        · exact mul_nonneg (Nat.cast_nonneg _) hfull0
      _ = _ := by ring
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with X hb hX
  exact (weighted_norm_average_le D hh L D₀ m hD hm cut a t ht X hX (z X)).trans
    (hb.trans (by
      rw [mul_assoc t]
      exact _root_.add_le_add (_root_.add_le_add le_rfl (div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt hlimit) (pow_nonneg ht.le _))) le_rfl))

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
