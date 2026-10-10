import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgAdd
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResiduesAdd
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SubtreeUnionWeightNonneg
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePolyDivTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalBudget
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinaryTwistWidthBasic
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Cutoff
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.OneAddSumLeProduct

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
open scoped BigOperators ContDiff
open Finset Filter Classical
open scoped BigOperators ContDiff Topology

namespace OrdinaryCorrelations.RawCutoff
open FiniteIntegration SourceCylinder GraphKernel.PrimeSystem

lemma smooth_cutoff_exists (T : ℝ) (hT : 0 < T) :
    ∃ phi : ℝ→ℝ, ContDiff ℝ ∞ phi ∧ HasCompactSupport phi ∧
      (∀ x, 0 ≤ phi x ∧ phi x ≤ 1) ∧
      Function.support phi ⊆ Set.Icc (-T) T ∧
      (∀ x, |x| ≤ T/2 → phi x = 1) := by
  let phi : ContDiffBump (0:ℝ) := ⟨T/2,T,by positivity,by linarith⟩
  refine ⟨phi,phi.contDiff,phi.hasCompactSupport,fun x=>⟨phi.nonneg,phi.le_one⟩,?_,?_⟩
  · rw [phi.support_eq]
    intro x hx
    have hx' : |x| < T := by simpa [Real.dist_eq,phi] using hx
    exact ⟨(abs_lt.mp hx').1.le,(abs_lt.mp hx').2.le⟩
  · intro x hx
    apply phi.one_of_mem_closedBall
    simpa [Real.dist_eq,phi] using hx

lemma avg_instances {α : Type*} (i j : Fintype α) (f g : α→ℝ) (h : f=g) :
    @avg α i f = @avg α j g := by
  subst g
  cases Subsingleton.elim i j
  rfl

lemma avg_product_finset {ι : Type*} [Fintype ι] {Ω : ι→Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (s : Finset ι) (f : ∀ i, Ω i→ℝ) :
    avg (fun x : ∀ i, Ω i=>∏ i∈s,f i (x i)) = ∏ i∈s,avg (f i) := by
  have he := avg_product (fun i r=>if i∈s then f i r else 1)
  have hp (x : ∀ i, Ω i) : (∏ i,if i∈s then f i (x i) else 1) = ∏ i∈s,f i (x i) := by
    rw [←prod_filter]
    simp
  simp only [hp] at he
  rw [he]
  calc
    _ = ∏ i, if i∈s then avg (f i) else 1 := by
      apply prod_congr rfl
      intro i hi
      split_ifs <;> simp only [avg_const]
    _ = _ := by rw [←prod_filter]; simp

lemma avg_coordinate {ι : Type*} [Fintype ι] {Ω : ι→Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (f : ∀ i, Ω i→ℝ) (i : ι) :
    avg (fun x : ∀ i, Ω i=>f i (x i)) = avg (f i) := by
  simpa using avg_product_finset {i} f

lemma avg_two_coordinates {ι : Type*} [Fintype ι] {Ω : ι→Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (f : ∀ i, Ω i→ℝ) (i j : ι) (hij : i≠j) :
    avg (fun x : ∀ i, Ω i=>f i (x i)*f j (x j)) = avg (f i)*avg (f j) := by
  simpa [hij] using avg_product_finset {i,j} f

lemma avg_centered_sum_sq {ι : Type*} [Fintype ι] {Ω : ι→Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (f : ∀ i, Ω i→ℝ) (hf : ∀ i, avg (f i) = 0) :
    avg (fun x : ∀ i, Ω i=>(∑ i,f i (x i))^2) = ∑ i,avg (fun r=>f i r^2) := by
  simp_rw [pow_two,sum_mul,mul_sum]
  rw [avg_sum']
  apply sum_congr rfl
  intro i hi
  rw [avg_sum',sum_eq_single i]
  · exact avg_coordinate (fun i r=>f i r*f i r) i
  · intro j hj hji
    rw [avg_two_coordinates f i j hji.symm,hf,zero_mul]
  · simp

def count (S : GraphKernel.PrimeSystem) (r : S.Residues) : ℝ :=
  ∑ p : S.Index, activity (p:ℕ) (r p) 0

def mean (S : GraphKernel.PrimeSystem) : ℝ := ∑ p : S.Index,(p:ℝ)⁻¹

lemma count_variance (S : GraphKernel.PrimeSystem) :
    avg (fun r=>(count S r-mean S)^2) ≤ mean S := by
  let f : ∀ p : S.Index,ZMod (p:ℕ)→ℝ := fun p r=>activity (p:ℕ) r 0-(p:ℝ)⁻¹
  have hzero (p : S.Index) : avg (f p) = 0 := by
    dsimp only [f]
    rw [avg_sub',activity_mean,avg_const,sub_self]
  have he (r : S.Residues) : count S r-mean S = ∑ p : S.Index,f p (r p) := by
    simp only [count,mean,f,sum_sub_distrib]
  simp_rw [he]
  have hv := avg_centered_sum_sq f hzero
  have hv' : avg (fun r : S.Residues=>(∑ p : S.Index,f p (r p))^2) =
      ∑ p : S.Index,avg (fun r=>f p r^2) := (avg_instances _ _ _ _ rfl).trans hv
  rw [hv']
  apply sum_le_sum
  intro p hp
  have hp0 : 0 ≤ (p:ℝ)⁻¹ := by positivity
  have hpoint (r : ZMod (p:ℕ)) :
      f p r^2 = (1-2*(p:ℝ)⁻¹)*activity (p:ℕ) r 0+((p:ℝ)⁻¹)^2 := by
    unfold f activity
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [avg_add',avg_mul_left,activity_mean,avg_const]
  nlinarith [sq_nonneg ((p:ℝ)⁻¹)]

lemma count_deviation (S : GraphKernel.PrimeSystem) (mu : ℝ) (hmean : mean S ≤ mu)
    (hdef : (mean S-mu)^2 ≤ mu) :
    avg (fun r=>(count S r-mu)^2) ≤ 4*mu := by
  have hp (r : S.Residues) : (count S r-mu)^2 ≤ 2*(count S r-mean S)^2+2*(mean S-mu)^2 := by
    nlinarith [sq_nonneg (count S r-2*mean S+mu)]
  have hb := avg_mono hp
  rw [avg_add',avg_mul_left,avg_const] at hb
  linarith [count_variance S]

lemma cutoff_deficit (T : ℝ) (hT : 0 < T) (phi : ℝ→ℝ)
    (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hone : ∀ x, |x| ≤ T/2 → phi x = 1) (x : ℝ) :
    1-phi x ≤ 4*x^2/T^2 := by
  by_cases hx : |x| ≤ T/2
  · rw [hone x hx,sub_self]; positivity
  · have hj : T/2 < |x| := lt_of_not_ge hx
    have hs : T^2 ≤ 4*x^2 := by nlinarith [sq_abs x,abs_nonneg x]
    have hd : 1 ≤ 4*x^2/T^2 := by rw [le_div_iff₀ (sq_pos_of_pos hT)]; simpa
    linarith [(hb x).1]

lemma cutoff_mean_deficit (S : GraphKernel.PrimeSystem) (mu T : ℝ) (hmu : 0 < mu) (hT : 0 < T)
    (hmean : mean S ≤ mu) (hdef : (mean S-mu)^2 ≤ mu)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hone : ∀ x, |x| ≤ T/2 → phi x = 1) :
    avg (fun r=>1-phi ((count S r-mu)/Real.sqrt mu)) ≤ 16/T^2 := by
  have hsq : (Real.sqrt mu)^2 = mu := Real.sq_sqrt hmu.le
  have hp (r : S.Residues) : 1-phi ((count S r-mu)/Real.sqrt mu) ≤
      (4/(T^2*mu))*(count S r-mu)^2 := by
    convert cutoff_deficit T hT phi hb hone ((count S r-mu)/Real.sqrt mu) using 1
    rw [div_pow,hsq]
    ring
  apply (avg_mono hp).trans
  rw [avg_mul_left]
  calc
    _ ≤ (4/(T^2*mu))*(4*mu) := mul_le_mul_of_nonneg_left (count_deviation S mu hmean hdef) (by positivity)
    _ = _ := by field_simp; ring

def primeSystem (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) : GraphKernel.PrimeSystem where
  primes := P
  prime_mem := hP
  core := P
  core_subset := Finset.Subset.rfl

lemma primeSystem_mean (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) :
    mean (primeSystem P hP) = ∑ p∈P,(p:ℝ)⁻¹ := by
  exact sum_coe_sort P (fun p : ℕ=>(p:ℝ)⁻¹)

lemma count_integer (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (n : ℕ) :
    count (primeSystem P hP) ((primeSystem P hP).integerResidues n) =
      (OrdinaryTwistWidth.primeCount P n : ℝ) := by
  unfold count integerResidues activity
  simp only [Int.cast_zero,add_zero,Int.cast_natCast,ZMod.natCast_eq_zero_iff]
  rw [show (∑ p : (primeSystem P hP).Index, if (p:ℕ)∣n then (1:ℝ) else 0) =
    ∑ p∈P, if p∣n then (1:ℝ) else 0 from sum_coe_sort P (fun p:ℕ=>if p∣n then (1:ℝ) else 0)]
  simp only [sum_boole,OrdinaryTwistWidth.primeCount]

lemma ordinary_deficit_mean (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (mu : ℝ) (phi : ℝ→ℝ) (a : ℕ) :
    Tendsto (fun N : ℕ=>(∑ n∈Icc 1 N, (1-phi
      (((OrdinaryTwistWidth.primeCount P (n+a):ℝ)-mu)/Real.sqrt mu)))/(N:ℝ))
      atTop (nhds (avg (fun r=>(1-phi ((count (primeSystem P hP) r-mu)/Real.sqrt mu))))) := by
  have ht := ((primeSystem P hP).real_origin_tendsto
    (fun r=>1-phi ((count (primeSystem P hP) r-mu)/Real.sqrt mu)) (fun _=>(1+a:ℕ))).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
  convert ht using 1
  funext N
  simp only [Nat.floor_natCast,Function.comp_apply]
  rw [SourceRoughFourier.sum_Icc_one_eq_range]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [show (n:ℤ)+((1+a:ℕ):ℤ)=((n+1+a:ℕ):ℤ) by omega,count_integer]

lemma product_cutoff_error (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (mu T : ℝ) (hmu : 0 < mu) (hT : 0 < T)
    (hmean : (∑ p∈P,(p:ℝ)⁻¹) ≤ mu) (hdef : ((∑ p∈P,(p:ℝ)⁻¹)-mu)^2 ≤ mu)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hone : ∀ x, |x| ≤ T/2 → phi x = 1) (h : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n∈Icc 1 N, ‖OrdinaryAnalyticCutoff.cutoff phi P mu n*
        OrdinaryAnalyticCutoff.cutoff phi P mu (n+h)-1‖) ≤ (32/T^2+δ)*(N:ℝ) := by
  let v : ℕ→ℝ := fun n=>phi (((OrdinaryTwistWidth.primeCount P n:ℝ)-mu)/Real.sqrt mu)
  let M := avg (fun r=>1-phi ((count (primeSystem P hP) r-mu)/Real.sqrt mu))
  have hM : M ≤ 16/T^2 := cutoff_mean_deficit (primeSystem P hP) mu T hmu hT
    (by rwa [primeSystem_mean]) (by rwa [primeSystem_mean]) phi hb hone
  have ht : Tendsto (fun N : ℕ=>(∑ n∈Icc 1 N,((1-v n)+(1-v (n+h))))/(N:ℝ)) atTop (nhds (M+M)) := by
    simpa only [sum_add_distrib,add_div,Nat.add_zero] using
      (ordinary_deficit_mean P hP mu phi 0).add (ordinary_deficit_mean P hP mu phi h)
  have hm : M+M < 32/T^2+δ := by
    have he : 32/T^2 = 16/T^2+16/T^2 := by ring
    rw [he]; linarith
  filter_upwards [ht.eventually (gt_mem_nhds hm),eventually_ge_atTop (1:ℕ)] with N hN hN1
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN1
  apply le_trans (sum_le_sum (g:=fun n=>(1-v n)+(1-v (n+h))) ?_) ((div_lt_iff₀ hN0).mp hN).le
  intro n hn
  have h1 := hb (((OrdinaryTwistWidth.primeCount P n:ℝ)-mu)/Real.sqrt mu)
  have h2 := hb (((OrdinaryTwistWidth.primeCount P (n+h):ℝ)-mu)/Real.sqrt mu)
  change ‖(v n:ℂ)*(v (n+h):ℂ)-1‖ ≤ _
  rw [←Complex.ofReal_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hprod : v n*v (n+h) ≤ 1 := by
    exact (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans (by norm_num)
  rw [abs_of_nonpos (by linarith)]
  change 0 ≤ v n ∧ v n ≤ 1 at h1
  change 0 ≤ v (n+h) ∧ v (n+h) ≤ 1 at h2
  nlinarith [mul_nonneg (sub_nonneg.mpr h1.2) (sub_nonneg.mpr h2.2)]

open OrdinaryAnalyticCentering

lemma cutoff_mean_omission {B C₀ : ℝ} (hB : 1 ≤ B) {d : ℕ} (hd : 0 < d)
    (hcard : d.primeFactors.card ≤ J C₀ B) :
    0 ≤ coreMean B-(∑ p∈(core B).filter (fun p=>¬p∣d),(p:ℝ)⁻¹) ∧
    coreMean B-(∑ p∈(core B).filter (fun p=>¬p∣d),(p:ℝ)⁻¹) ≤ (J C₀ B:ℝ)/P₀ B := by
  have he := sum_filter_add_sum_filter_not (core B) (fun p=>p∣d) (fun p=>(p:ℝ)⁻¹)
  have hs : (core B).filter (fun p=>p∣d) ⊆ d.primeFactors := by
    intro p hp
    obtain ⟨hp,hpd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨core_prime B hp,hpd,hd.ne'⟩
  have hnon : 0 ≤ ∑ p∈(core B).filter (fun p=>p∣d),(p:ℝ)⁻¹ := by positivity
  have hub : (∑ p∈(core B).filter (fun p=>p∣d),(p:ℝ)⁻¹) ≤ (J C₀ B:ℝ)/P₀ B := by
    calc
      _ ≤ ∑ _p∈(core B).filter (fun p=>p∣d),(P₀ B)⁻¹ := by
        apply sum_le_sum
        intro p hp
        exact inv_anti₀ (Real.exp_pos _) (prime_lower B hB (mem_union_left _ (mem_filter.mp hp).1)).le
      _ = (((core B).filter (fun p=>p∣d)).card:ℝ)/P₀ B := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_le_card hs).trans hcard) (Real.exp_pos _).le
  change _+_=coreMean B at he
  constructor <;> linarith

lemma P₀_eq_source (B : ℝ) : P₀ B = sourceMinPrime B := by
  unfold P₀ sourceMinPrime
  norm_num [GraphKernel.PrimeSystem.epsilon]

lemma defect_scale_tendsto (C₀ : ℝ) (hC : 0 ≤ C₀) :
    Tendsto (fun B : ℝ=>(J C₀ B:ℝ)/P₀ B) atTop (nhds 0) ∧
    Tendsto (fun B : ℝ=>B*(J C₀ B:ℝ)/P₀ B) atTop (nhds 0) := by
  have hj : ∀ᶠ B : ℝ in atTop, (J C₀ B:ℝ) ≤ B := by
    simpa only [J,Real.rpow_one] using eventually_log_ceil_le C₀ 1 hC (by norm_num)
  constructor
  · refine squeeze_zero' (g := fun B=>B/P₀ B) (Eventually.of_forall (fun B=>div_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)) ?_ ?_
    · filter_upwards [hj] with B hB
      exact div_le_div_of_nonneg_right hB (Real.exp_pos _).le
    · simpa only [pow_one,←P₀_eq_source] using source_poly_div_tendsto 1
  · refine squeeze_zero' (g := fun B=>B^2/P₀ B) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with B hB
      exact div_nonneg (mul_nonneg hB (Nat.cast_nonneg _)) (Real.exp_pos _).le
    · filter_upwards [hj,eventually_ge_atTop (0:ℝ)] with B hB hB0
      have hh := mul_le_mul_of_nonneg_left hB hB0
      exact div_le_div_of_nonneg_right (by simpa only [pow_two] using hh) (Real.exp_pos _).le
    · simpa only [←P₀_eq_source] using source_poly_div_tendsto 2

theorem source_cutoff_error (C₀ T : ℝ) (hC : 0 ≤ C₀) (hT : 0 < T)
    (phi : ℝ→ℝ) (hb : ∀ x, 0 ≤ phi x ∧ phi x ≤ 1)
    (hone : ∀ x, |x| ≤ T/2 → phi x = 1) (h : ℕ) :
    ∀ᶠ B : ℝ in atTop, ∀ d : ℕ, 0 < d → d.primeFactors.card ≤ J C₀ B →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
      (∑ n∈Icc 1 N, ‖cut phi B d n*cut phi B d (n+h)-1‖) ≤
        (32/T^2+δ)*(N:ℝ) := by
  have hμ : ∀ᶠ B : ℝ in atTop, 1 ≤ coreMean B := by
    simpa only [coreMean,RawDivisorBin.core_eq_source,SourcePrimeBands.coreMass] using
      coreMass_tendsto.eventually_ge_atTop 1
  filter_upwards [hμ,(defect_scale_tendsto C₀ hC).1.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop (1:ℝ)] with B hmu hJ hB
  intro d hd hcard δ hδ
  obtain ⟨ho0,ho1⟩ := cutoff_mean_omission hB hd hcard
  have hs : ((∑ p∈(core B).filter (fun p=>¬p∣d),(p:ℝ)⁻¹)-coreMean B)^2 ≤ coreMean B := by
    nlinarith [sq_nonneg (coreMean B-(∑ p∈(core B).filter (fun p=>¬p∣d),(p:ℝ)⁻¹)),
      mul_nonneg ho0 (show 0 ≤ 1-(coreMean B-(∑ p∈(core B).filter (fun p=>¬p∣d),(p:ℝ)⁻¹)) by linarith)]
  exact product_cutoff_error ((core B).filter (fun p=>¬p∣d))
    (fun p hp=>core_prime B (mem_filter.mp hp).1) (coreMean B) T (by linarith) hT
    (by linarith) hs phi hb hone h δ hδ

end OrdinaryCorrelations.RawCutoff

end

end OAI
