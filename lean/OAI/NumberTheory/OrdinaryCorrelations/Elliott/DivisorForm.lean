import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.DirMatrix

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
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h L D₀ : ℕ}

def divisorForm (D : S.DivisorFamily B τ C₀) (h : ℕ) (cut : S.Cutoffs T)
    (a : ℕ→ℂ) (F G : ℤ→ℂ) (X : ℝ) : ℂ :=
  ∑ d∈D.members,a d*∑ n∈Icc 1 ⌊X⌋₊,
    F n*G ((n:ℤ)+(h:ℤ)*d)*(S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d):ℝ)

def retainedForm (D : S.DivisorFamily B τ C₀) (h L : ℕ) (cut : S.Cutoffs T)
    (a : ℕ→ℂ) (F G : ℤ→ℂ) (X : ℝ) : ℂ :=
  ∑ d∈D.members,a d*∑ n∈Icc 1 ⌊X⌋₊,retainedEdge D h L cut F G n d

lemma retainedEdge_bounded (D : S.DivisorFamily B τ C₀) (h L : ℕ)
    (cut : S.Cutoffs T) (F G : ℤ→ℂ) (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1)
    (d : ℕ) : ∃ C : ℝ, ∀ n:ℤ,‖retainedEdge D h L cut F G n d‖≤C := by
  refine ⟨∑ r:S.Residues,|S.divisorEdgeWeight cut r d 0 ((h:ℤ)*d)|,?_⟩
  intro n
  have hb : |S.divisorEdgeWeight cut (S.integerResidues n) d 0 ((h:ℤ)*d)| ≤
      ∑ r:S.Residues,|S.divisorEdgeWeight cut r d 0 ((h:ℤ)*d)| :=
    single_le_sum (f := fun r : S.Residues => |S.divisorEdgeWeight cut r d 0 ((h:ℤ)*d)|) (fun r hr=>abs_nonneg _) (mem_univ _)
  unfold retainedEdge
  split_ifs
  · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (norm_nonneg _) (hF n)).trans (hG _))
      (abs_nonneg _)).trans (by simpa using hb)
  · rw [norm_zero]
    exact sum_nonneg (fun r hr=>abs_nonneg _)

lemma sliding_translation_bound (D : S.DivisorFamily B τ C₀) (h L D₀ : ℕ)
    (cut : S.Cutoffs T) (b : ℕ→ℂ) (F G : ℤ→ℂ)
    (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1) :
    ∃ E : ℝ, ∀ X:ℝ,
      ‖(∑ n∈Icc 1 ⌊X⌋₊,∑ d∈D.members,b d*∑ x∈range (D₀-h*d),
          retainedEdge D h L cut F G ((n:ℤ)+x) d) -
        ∑ d∈D.members,(b d*(D₀-h*d:ℕ))*∑ n∈Icc 1 ⌊X⌋₊,
          retainedEdge D h L cut F G n d‖ ≤ E := by
  choose C hC using retainedEdge_bounded D h L cut F G hF hG
  refine ⟨∑ d∈D.members,‖b d‖*∑ x∈range (D₀-h*d),2*(x:ℝ)*C d,?_⟩
  intro X
  have he : (∑ n∈Icc 1 ⌊X⌋₊,∑ d∈D.members,b d*∑ x∈range (D₀-h*d),
          retainedEdge D h L cut F G ((n:ℤ)+x) d) -
        ∑ d∈D.members,(b d*(D₀-h*d:ℕ))*∑ n∈Icc 1 ⌊X⌋₊,
          retainedEdge D h L cut F G n d =
      ∑ d∈D.members,b d*∑ x∈range (D₀-h*d),
        ((∑ n∈Icc 1 ⌊X⌋₊,retainedEdge D h L cut F G ((n:ℤ)+x) d)-
          ∑ n∈Icc 1 ⌊X⌋₊,retainedEdge D h L cut F G n d) := by
    rw [sum_comm,←sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    rw [←mul_sum,sum_comm,sum_sub_distrib,mul_sub]
    simp [mul_assoc]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro d hd
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro x hx
  simpa only [Nat.cast_add] using SourceRoughFourier.prefix_translation_bound
    (fun n=>retainedEdge D h L cut F G n d) ⌊X⌋₊ x (C d) (fun n=>hC d n)

theorem retainedForm_eventual (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    (L D₀ m : ℕ) (hD : 0<D₀) (hm : 0 < m) (hspan : ∀ d∈D.members,2*(h*d)≤D₀)
    (cut : S.Cutoffs T) (a : ℕ→ℂ) (ha : ∀ d∈D.members,‖a d‖≤1)
    (F G : ℤ→ℂ) (hF : ∀ n,‖F n‖≤1) (hG : ∀ n,‖G n‖≤1)
    (t : ℝ) (ht : 0<t) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ X : ℝ in atTop, ‖retainedForm D h L cut a F G X‖/X ≤
      2*t*S.weightMean + 2*Real.sqrt ((D₀:ℝ)^3*
        NumericalLine.fullTraceSum D h (2*m) L cut*
        Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))/((D₀:ℝ)*t^(m-1))+δ := by
  have hDpos : (0:ℝ)<D₀ := by exact_mod_cast hD
  let b : ℕ→ℂ := fun d=>a d*((D₀:ℝ)/(2*(D₀-h*d:ℕ)):ℝ)
  have hk (d : ℕ) (hd : d∈D.members) : 0<D₀-h*d ∧ D₀≤2*(D₀-h*d) := by
    have := hspan d hd
    omega
  have hb : ∀ d∈D.members,‖b d‖≤1 := by
    intro d hd
    have hkR : (0:ℝ)<(D₀-h*d:ℕ) := by exact_mod_cast (hk d hd).1
    have hr : (D₀:ℝ)/(2*(D₀-h*d:ℕ))≤1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (hk d hd).2)
    dsimp [b]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤(D₀:ℝ)/(2*(D₀-h*d:ℕ))) ]
    exact (mul_le_of_le_one_left (by positivity) (ha d hd)).trans hr
  have hbI : ∀ d∈D.members,‖Complex.I*b d‖≤1 := by simpa only [norm_mul,Complex.norm_I,one_mul] using hb
  have hbmul (d : ℕ) (hd : d∈D.members) : b d*(D₀-h*d:ℕ)=(D₀:ℂ)/2*a d := by
    have hkC : ((D₀-h*d:ℕ):ℂ)≠0 := by exact_mod_cast (hk d hd).1.ne'
    dsimp [b]
    push_cast
    field_simp
  obtain ⟨E,hE⟩ := sliding_translation_bound D h L D₀ cut b F G hF hG
  have hδD : 0<δ*(D₀:ℝ)/4 := by positivity
  have hn := weighted_norm_eventual D hh L D₀ m hD hm cut b hb t ht (fun _=>1) _ hδD
  have hnI := weighted_norm_eventual D hh L D₀ m hD hm cut (fun d=>Complex.I*b d) hbI t ht (fun _=>1) _ hδD
  have heT : Tendsto (fun X:ℝ=>E/X) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜:=ℝ)).const_mul E
  filter_upwards [hn,hnI,heT.eventually (eventually_le_nhds hδD),eventually_gt_atTop (0:ℝ)] with X hn hnI he hX
  let W : ℂ := ∑ n∈Icc 1 ⌊X⌋₊,∑ d∈D.members,b d*∑ x∈range (D₀-h*d),
    retainedEdge D h L cut F G ((n:ℤ)+x) d
  have hW : ‖W‖/X ≤ t*(D₀:ℝ)*S.weightMean + Real.sqrt ((D₀:ℝ)^3*
      NumericalLine.fullTraceSum D h (2*m) L cut*
        Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))/t^(m-1)+δ*D₀/4 := by
    have hbW : ‖W‖ ≤ (∑ n∈range ⌊X⌋₊,
        ‖symMatrix D h L cut b D₀ ((n:ℤ)+1)‖*windowWeight S D₀ (S.integerResidues ((n:ℤ)+1))+
        ∑ n∈range ⌊X⌋₊,‖symMatrix D h L cut (fun d=>Complex.I*b d) D₀ ((n:ℤ)+1)‖*
          windowWeight S D₀ (S.integerResidues ((n:ℤ)+1)))/2 := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ n∈Icc 1 ⌊X⌋₊,((‖symMatrix D h L cut b D₀ n‖+
          ‖symMatrix D h L cut (fun d=>Complex.I*b d) D₀ n‖)/2)*
            windowWeight S D₀ (S.integerResidues n) := by
          exact sum_le_sum (fun n hn=>window_bilinear_le D hh L cut b F G hF hG n)
        _ = _ := by
          rw [SourceRoughFourier.sum_Icc_one_eq_range]
          simp only [Nat.cast_add,Nat.cast_one,add_mul,div_mul_eq_mul_div,sum_add_distrib,←sum_div]
    have hq := div_le_div_of_nonneg_right hbW hX.le
    linarith [show ( (∑ n∈range ⌊X⌋₊,‖symMatrix D h L cut b D₀ ((n:ℤ)+1)‖*
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+1))) + ∑ n∈range ⌊X⌋₊,
      ‖symMatrix D h L cut (fun d=>Complex.I*b d) D₀ ((n:ℤ)+1)‖*
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+1)))/2/X =
      ((∑ n∈range ⌊X⌋₊,‖symMatrix D h L cut b D₀ ((n:ℤ)+1)‖*
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+1)))/X+
      (∑ n∈range ⌊X⌋₊,‖symMatrix D h L cut (fun d=>Complex.I*b d) D₀ ((n:ℤ)+1)‖*
      windowWeight S D₀ (S.integerResidues ((n:ℤ)+1)))/X)/2 by ring]
  have he' : ‖W-(D₀:ℂ)/2*retainedForm D h L cut a F G X‖≤E := by
    have heq : (∑ d∈D.members,(b d*(D₀-h*d:ℕ))*∑ n∈Icc 1 ⌊X⌋₊,
        retainedEdge D h L cut F G n d) = (D₀:ℂ)/2*retainedForm D h L cut a F G X := by
      unfold retainedForm
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      rw [hbmul d hd,mul_assoc]
    simpa only [heq] using hE X
  have hc := (norm_le_norm_add_norm_sub W ((D₀:ℂ)/2*retainedForm D h L cut a F G X)).trans
    (add_le_add_right (by simpa only [norm_sub_rev] using he') ‖W‖)
  rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_ofNat] at hc
  have hc' := div_le_div_of_nonneg_right hc hX.le
  have hh' : (D₀:ℝ)/2*(‖retainedForm D h L cut a F G X‖/X)≤
      t*D₀*S.weightMean+Real.sqrt ((D₀:ℝ)^3*NumericalLine.fullTraceSum D h (2*m) L cut*
        Real.exp ((A^2+2*A)*S.harmonicCore+3*S.harmonicCenter))/t^(m-1)+δ*D₀/2 := by
    have heq : ((D₀:ℝ)/2*‖retainedForm D h L cut a F G X‖)/X = (D₀:ℝ)/2*(‖retainedForm D h L cut a F G X‖/X) := by ring
    rw [heq,add_div] at hc'
    linarith
  apply (mul_le_mul_iff_right₀ (show (0:ℝ)<(D₀:ℝ)/2 by positivity)).mp
  calc
    _ ≤ _ := hh'
    _ = _ := by field_simp

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
