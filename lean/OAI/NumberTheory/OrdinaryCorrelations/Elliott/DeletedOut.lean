import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalIndicator
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DeletedWeightMean
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.DivisorForm

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
variable {S : PrimeSystem} {B τ C₀ T : ℝ}

def deletedOut (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (d : ℕ) (r : S.Residues) : ℝ :=
  |S.divisorEdgeWeight cut r d 0 ((h:ℤ)*d)| *deletedIndicator D h L r

def deletedIn (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (d : ℕ) (r : S.Residues) : ℝ :=
  |S.divisorEdgeWeight cut r d (-((h:ℤ)*d)) 0| *deletedIndicator D h L r

lemma deleted_mean_le (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T) :
    (∑ d∈D.members,avg (deletedOut D h L cut d))+
      (∑ d∈D.members,avg (deletedIn D h L cut d)) ≤
    2*Real.exp (theta*S.harmonicCenter)*deletedWeightMean D h L := by
  have hdel (r : S.Residues) : 0≤deletedIndicator D h L r := by
    unfold deletedIndicator; split_ifs <;> norm_num
  have hO : ∑ d∈D.members,avg (deletedOut D h L cut d) ≤
      Real.exp (theta*S.harmonicCenter)*deletedWeightMean D h L := by
    rw [←OrdinaryCorrelations.SourceCylinder.avg_sum']
    unfold deletedWeightMean
    rw [←avg_mul_left]
    apply avg_mono
    intro r
    unfold deletedOut
    rw [←sum_mul]
    have := mul_le_mul_of_nonneg_right (divisor_absolute_degree D cut r 0
        (fun d=>(h:ℤ)*d)) (hdel r)
    nlinarith only [this]
  have hI : ∑ d∈D.members,avg (deletedIn D h L cut d) ≤
      Real.exp (theta*S.harmonicCenter)*deletedWeightMean D h L := by
    rw [←OrdinaryCorrelations.SourceCylinder.avg_sum']
    unfold deletedWeightMean
    rw [←avg_mul_left]
    apply avg_mono
    intro r
    unfold deletedIn
    rw [←sum_mul]
    have := mul_le_mul_of_nonneg_right (incoming_divisor_absolute_degree D cut r 0
        (fun d=>-((h:ℤ)*d)) (fun d hd=>by simp)) (hdel r)
    nlinarith only [this]
  linarith

lemma deleted_edge_pointwise (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (F G : ℤ→ℂ) (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1)
    (d : ℕ) (n : ℤ) :
    ‖F n*G (n+(h:ℤ)*d)*(S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d):ℝ)-
      retainedEdge D h L cut F G n d‖ ≤
    deletedOut D h L cut d (S.integerResidues n)+
      deletedIn D h L cut d (S.integerResidues (n+(h:ℤ)*d)) := by
  have he : S.divisorEdgeWeight cut (S.integerResidues (n+(h:ℤ)*d)) d (-((h:ℤ)*d)) 0 =
      S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d) := by
    simpa only [zero_sub,sub_self] using (integer_edge_shift cut n ((h:ℤ)*d) d 0 ((h:ℤ)*d)).symm
  have hb : ‖F n*G (n+(h:ℤ)*d)*(S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d):ℝ)‖ ≤
      |S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d)| := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hF n)).trans (hG _)) (abs_nonneg (S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d)))
  unfold deletedOut deletedIn retainedEdge
  rw [he,deletedIndicator_integer,deletedIndicator_integer]
  by_cases hn : VertexAllowed D h L n <;> by_cases hm : VertexAllowed D h L (n+(h:ℤ)*d) <;>
    simp only [hn,hm,and_self,and_false,false_and,ite_true,ite_false,sub_self,norm_zero,sub_zero,mul_zero,mul_one,add_zero,zero_add] <;>
    nlinarith only [hb,abs_nonneg (S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d))]

theorem removedForm_eventual (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (ha : ∀ d∈D.members,‖a d‖≤1)
    (F G : ℤ→ℂ) (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1)
    (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, ‖divisorForm D h cut a F G X-retainedForm D h L cut a F G X‖/X ≤
      2*Real.exp (theta*S.harmonicCenter)*deletedWeightMean D h L+δ := by
  let U (X : ℝ) := ∑ d∈D.members,((∑ n∈range ⌊X⌋₊,
      deletedOut D h L cut d (S.integerResidues ((n:ℤ)+1)))/X+
    (∑ n∈range ⌊X⌋₊,deletedIn D h L cut d (S.integerResidues ((n:ℤ)+1+(h:ℤ)*d)))/X)
  have hlim : Tendsto U atTop (nhds (∑ d∈D.members,
      (avg (deletedOut D h L cut d)+avg (deletedIn D h L cut d)))) := by
    apply tendsto_finsetSum
    intro d hd
    exact (S.real_origin_tendsto (deletedOut D h L cut d) (fun _=>1)).add
      (by simpa only [←add_assoc] using S.real_origin_tendsto (deletedIn D h L cut d) (fun _=>1+(h:ℤ)*d))
  have hlim' := hlim.eventually (eventually_le_nhds (lt_add_of_pos_right _ hδ))
  filter_upwards [hlim',eventually_gt_atTop (0:ℝ)] with X hlim' hX
  have hb : ‖divisorForm D h cut a F G X-retainedForm D h L cut a F G X‖/X ≤ U X := by
    dsimp [U]
    simp_rw [←add_div]
    rw [←sum_div]
    apply div_le_div_of_nonneg_right _ hX.le
    unfold divisorForm retainedForm
    rw [←sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro d hd
    rw [←mul_sub,←sum_sub_distrib,norm_mul]
    calc
      _ ≤ ‖∑ n∈Icc 1 ⌊X⌋₊,
          (F n*G ((n:ℤ)+(h:ℤ)*d)*(S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d):ℝ)-
          retainedEdge D h L cut F G n d)‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha d hd) (norm_nonneg _)
      _ ≤ ∑ n∈Icc 1 ⌊X⌋₊,(deletedOut D h L cut d (S.integerResidues n)+
          deletedIn D h L cut d (S.integerResidues ((n:ℤ)+(h:ℤ)*d))) := by
        exact (norm_sum_le _ _).trans (sum_le_sum (fun n hn=>deleted_edge_pointwise D h L cut F G hF hG d n))
      _ = _ := by
        rw [SourceRoughFourier.sum_Icc_one_eq_range,sum_add_distrib]
        simp only [Nat.cast_add,Nat.cast_one]
  exact hb.trans (hlim'.trans (by
    simpa only [sum_add_distrib] using add_le_add (deleted_mean_le D h L cut) (le_refl δ)))

theorem divisorForm_eventual (D : S.DivisorFamily B τ C₀) {h : ℕ} (hh : 0<h)
    (L D₀ m : ℕ) (hD : 0<D₀) (hm : 0 < m) (hspan : ∀ d∈D.members,2*(h*d)≤D₀)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (ha : ∀ d∈D.members,‖a d‖≤1)
    (F G : ℤ→ℂ) (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1)
    (t : ℝ) (ht : 0<t) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, ‖divisorForm D h cut a F G X‖/X ≤
      2*t*S.weightMean+2*Real.sqrt ((D₀:ℝ)^3*NumericalLine.fullTraceSum D h (2*m) L cut*
        Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))/((D₀:ℝ)*t^(m-1))+
      2*Real.exp (theta*S.harmonicCenter)*deletedWeightMean D h L+δ := by
  have hδ2 : 0<δ/2 := by positivity
  filter_upwards [retainedForm_eventual D hh L D₀ m hD hm hspan cut a ha F G hF hG t ht (δ/2) hδ2,
      removedForm_eventual D h L cut a ha F G hF hG (δ/2) hδ2,
      eventually_gt_atTop (0:ℝ)] with X h1 h2 hX
  have hn := div_le_div_of_nonneg_right (norm_le_norm_add_norm_sub
    (retainedForm D h L cut a F G X) (divisorForm D h cut a F G X)) hX.le
  rw [add_div,norm_sub_rev (retainedForm D h L cut a F G X)] at hn
  linarith

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
