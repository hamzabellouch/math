import Mathlib
import OAI.Probability.JammingConcavity.RowIntegralJets

namespace OAI

/-! Row Parameter Data. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

structure RankFamilyData (I : Set ℝ) (A B : ℝ → ℝ) (F : ℝ → ℝ → ℝ → ℝ) : Prop where
  Acont : ContinuousOn A (Icc 0 1)
  Bcont : ContinuousOn B (Icc 0 1)
  coeff : ∃ D : ℝ,0≤D ∧ (∀ e∈I,∀ t∈Icc (0:ℝ) 1,0≤A t+e*B t ∧ A t+e*B t≤D) ∧
    ∀ t∈Icc (0:ℝ) 1,|B t|≤D
  smooth : ∀ e∈I,JointSpatialSmooth (Icc 0 1) (F e)
  lower : ∃ L : ℝ,0≤L ∧ ∀ e∈I,∀ t∈Icc (0:ℝ) 1,∀ x,
    |F e t x|≤L*(1+x^2) ∧ |deriv (F e t) x|≤L*(1+|x|)
  higher : ∀ n : ℕ,2≤n → ∃ H : ℝ,0≤H ∧ ∀ e∈I,∀ t∈Icc (0:ℝ) 1,∀ x,|iteratedDeriv n (F e t) x|≤H
  time : ∀ e∈I,∀ t∈Ioo (0:ℝ) 1,∀ x,HasDerivAt (fun s => F e s x)
    (-(A t+e*B t)*(iteratedDeriv 2 (F e t) x+t*(iteratedDeriv 1 (F e t) x)^2)) t
  terminal : ∀ e∈I,∀ e'∈I,∀ x,F e 1 x=F e' 1 x

lemma RankFamilyData.poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun e => e∈I) (Icc 0 1) F := by
  refine ⟨hf.smooth,fun n => ?_⟩
  obtain ⟨L,hL,hb⟩ := hf.lower
  rcases n with _|(_|n)
  · exact FamilyGrowth.of_quadratic_bound hL (fun e he t ht x => (hb e he t ht x).1)
  · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      FamilyGrowth.of_linear_bound hL (fun e he t ht x => (hb e he t ht x).2)
  · obtain ⟨H,hH,hh⟩ := hf.higher (n+2) (by omega)
    exact FamilyGrowth.of_bound hH hh

lemma RankFamilyData.diffusion_cont {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (e : ℝ) : ContinuousOn (fun t => A t+e*B t) (Icc 0 1) :=
  hf.Acont.add (continuousOn_const.mul hf.Bcont)

lemma RankFamilyData.endpoint_linear {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) {ι : Type*} (l r : ι → ℝ) (hl : ∀ i,l i∈I) (hr : ∀ i,r i∈I)
    {U H : ι → ℝ → ℝ → ℝ}
    (hs : ∀ i,JointSpatialSmooth (Icc 0 1) (U i))
    (hg : ∀ i,∀ n : ℕ,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv n (U i t)))
    (hH : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) H)
    (ht : ∀ i,∀ t∈Ioo (0:ℝ) 1,∀ x,HasDerivAt (fun s => U i s x)
      (H i t x-(A t+l i*B t)*iteratedDeriv 2 (U i t) x-
        ((A t+l i*B t)*t*(iteratedDeriv 1 (F (l i) t) x+iteratedDeriv 1 (F (r i) t) x))*iteratedDeriv 1 (U i t) x) t)
    (hterm : ∀ i,∀ x,U i 1 x=0) : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) U := by
  obtain ⟨D,hD,hcoef,hB⟩ := hf.coeff
  obtain ⟨L,hL,hlo⟩ := hf.lower
  let a := fun i t => A t+l i*B t
  let b := fun i t x => a i t*t*(iteratedDeriv 1 (F (l i) t) x+iteratedDeriv 1 (F (r i) t) x)
  have hc (i : ι) : ContinuousOn (fun t => a i t*t) (Icc 0 1) := (hf.diffusion_cont (l i)).mul continuousOn_id
  have hfac (i : ι) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : |a i t*t|≤D := by
    rw [abs_mul,abs_of_nonneg (hcoef (l i) (hl i) t ht).1,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right (hcoef (l i) (hl i) t ht).2 ht.1).trans (by nlinarith [ht.2])
  have hb (i : ι) : JointSpatialSmooth (Icc 0 1) (b i) :=
    (((hf.smooth (l i) (hl i)).jet 1).add ((hf.smooth (r i) (hr i)).jet 1)).coeff_mul (hc i)
  have hbb : ∀ n : ℕ,1≤n → ∃ E : ℝ,0≤E ∧ ∀ i,True → ∀ t∈Icc (0:ℝ) 1,∀ x,|iteratedDeriv n (b i t) x|≤E := by
    intro n hn
    obtain ⟨E,hE,he⟩ := hf.higher (n+1) (by omega)
    refine ⟨D*(E+E),by positivity,fun i _ t ht x => ?_⟩
    have hlc := ((hf.smooth (l i) (hl i)).jet 1).1 t ht
    have hrc := ((hf.smooth (r i) (hr i)).jet 1).1 t ht
    have hlc' : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv 1 (F (l i) t)) := hlc.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
    have hrc' : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv 1 (F (r i) t)) := hrc.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
    dsimp [b]
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_fun_add hlc'.contDiffAt hrc'.contDiffAt]
    simp only [iteratedDeriv_iteratedDeriv]
    rw [abs_mul]
    exact mul_le_mul (hfac i ht) ((abs_add_le _ _).trans (add_le_add (he (l i) (hl i) t ht x) (he (r i) (hr i) t ht x))) (abs_nonneg _) hD
  refine ⟨fun i _ => hs i,?_⟩
  apply linear_all_jets_growth (a:=a) (b:=b) (H:=H) (by norm_num : (0:ℝ)<1)
    (show 0≤D*(L+L) by positivity) hD (fun i _ => hs i)
    (fun i _ t ht => hcoef (l i) (hl i) t ht) _ hbb (fun i _ n => hg i n) hH.bounds _ (fun i _ => hterm i)
  · intro i _ t ht x
    dsimp [b]
    rw [abs_mul]
    apply (mul_le_mul (hfac i ht) (le_refl _) (abs_nonneg _) hD).trans
    calc
      D*|iteratedDeriv 1 (F (l i) t) x+iteratedDeriv 1 (F (r i) t) x| ≤
          D*(L*(1+|x|)+L*(1+|x|)) := by
        apply mul_le_mul_of_nonneg_left _ hD
        simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
          (abs_add_le (deriv (F (l i) t) x) (deriv (F (r i) t) x)).trans (add_le_add (hlo (l i) (hl i) t ht x).2 (hlo (r i) (hr i) t ht x).2)
      _ = _ := by ring
  · intro i _
    exact linear_evolution_jets (by norm_num) (hs i) (hb i) (hH.smooth i trivial)
      (hf.diffusion_cont (l i)) (ht i)

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

lemma actual_parameter_family {A B C κ Q : ℝ} {u q η : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hη0 : η 0=0) (hη1 : η 1=0) :
    ∃ r : ℝ,0<r ∧ ∃ F : ℝ → ℝ → ℝ → ℝ,
      (∀ e,|e|<r → RowClassicalRankSolution u (fun s => q s+e*η s) (F e)) ∧
      RankFamilyData (Ioo (-r) r) (fun t => deriv q t/2) (fun t => deriv η t/2) F := by
  classical
  obtain ⟨r,hr,hrq⟩ := rowSmooth_perturbation hq hη hη0 hη1
  have hex : ∀ e,∃ f,|e|<r → RowClassicalRankSolution u (fun s => q s+e*η s) f := by
    intro e
    by_cases he : |e|<r
    · obtain ⟨f,hf,_⟩ := row_rank_existence_unique hQ hu (hrq e he)
      exact ⟨f,fun _ => hf⟩
    · exact ⟨fun _ _ => 0,fun h => (he h).elim⟩
  choose F hF using hex
  have hi (e : ℝ) (he : e∈Ioo (-r) r) : |e|<r := abs_lt.mpr he
  obtain ⟨L,hL,H,hH,hbounds⟩ := row_rank_uniform_bounds hQ hu
  have hqc := (contDiff_infty_iff_deriv.mp hq.1).2.continuous
  have hηc := (contDiff_infty_iff_deriv.mp hη).2.continuous
  obtain ⟨tq,htq,hqmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hqc.abs.continuousOn
  obtain ⟨tη,htη,hηmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hηc.abs.continuousOn
  have heder (e t : ℝ) : deriv (fun s => q s+e*η s) t=deriv q t+e*deriv η t := by
    exact (((hq.1.differentiable (by simp) t).hasDerivAt).add
      ((hη.differentiable (by simp) t).hasDerivAt.const_mul e)).deriv
  refine ⟨r,hr,F,hF,?_⟩
  refine ⟨(hqc.div_const 2).continuousOn,(hηc.div_const 2).continuousOn,?_,?_,?_,?_,?_,?_⟩
  · let D : ℝ := |deriv q tq|/2+r*(|deriv η tη|/2)+|deriv η tη|/2
    refine ⟨D,by dsimp [D]; positivity,?_,?_⟩
    · intro e he t ht
      have hpos := (hrq e (hi e he)).2.2.2 t ht
      rw [heder] at hpos
      refine ⟨by linarith,?_⟩
      have hab : |e|≤r := (hi e he).le
      have hm := mul_le_mul hab ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (hηmax ht)) (by positivity) hr.le
      calc
        deriv q t/2+e*(deriv η t/2) ≤ |deriv q t|/2+|e| *(|deriv η t|/2) := by
          have ht1 := le_abs_self (deriv q t)
          have ht2 := le_abs_self (e*(deriv η t/2))
          rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht2
          linarith
        _ ≤ |deriv q tq|/2+r*(|deriv η tη|/2) := add_le_add (by
          have hqbd : |deriv q t| ≤ |deriv q tq| := hqmax ht
          linarith) hm
        _ ≤ D := by dsimp [D]; linarith [abs_nonneg (deriv η tη)]
    · intro t ht
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh : |deriv η t| ≤ |deriv η tη| := hηmax ht
      dsimp [D]
      nlinarith [abs_nonneg (deriv q tq),abs_nonneg (deriv η tη),mul_nonneg hr.le (abs_nonneg (deriv η tη))]
  · intro e he
    exact row_rank_smooth hQ hu (hrq e (hi e he)) (hF e (hi e he))
  · exact ⟨L,hL,fun e he => (hbounds _ (hrq e (hi e he)) _ (hF e (hi e he))).1⟩
  · intro n hn
    exact ⟨H n,hH n,fun e he => (hbounds _ (hrq e (hi e he)) _ (hF e (hi e he))).2 n hn⟩
  · intro e he t ht x
    have hh := (hF e (hi e he)).2.2.2.2.1 t ht x
    rw [heder] at hh
    convert hh using 1
    simp only [iteratedDeriv_succ,iteratedDeriv_zero]
    ring
  · intro e he e' he' x
    exact ((hF e (hi e he)).2.2.2.2.2.1 x).trans ((hF e' (hi e' he')).2.2.2.2.2.1 x).symm

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter

lemma dd1_add (F G : ℝ → ℝ) (a b : ℝ) : dd1 (fun e => F e+G e) a b=dd1 F a b+dd1 G a b := by unfold dd1; ring
lemma dd2_add (F G : ℝ → ℝ) (a b c : ℝ) : dd2 (fun e => F e+G e) a b c=dd2 F a b c+dd2 G a b c := by unfold dd2; rw [dd1_add,dd1_add]; ring
lemma dd3_add (F G : ℝ → ℝ) (a b c d : ℝ) : dd3 (fun e => F e+G e) a b c d=dd3 F a b c d+dd3 G a b c d := by unfold dd3; rw [dd2_add,dd2_add]; ring
lemma dd1_mul (F : ℝ → ℝ) (k a b : ℝ) : dd1 (fun e => k*F e) a b=k*dd1 F a b := by unfold dd1; ring
lemma dd2_mul (F : ℝ → ℝ) (k a b c : ℝ) : dd2 (fun e => k*F e) a b c=k*dd2 F a b c := by unfold dd2; rw [dd1_mul,dd1_mul]; ring
lemma dd3_mul (F : ℝ → ℝ) (k a b c d : ℝ) : dd3 (fun e => k*F e) a b c d=k*dd3 F a b c d := by unfold dd3; rw [dd2_mul,dd2_mul]; ring

lemma dd1_rhs (X Y : ℝ → ℝ) (A B t : ℝ) {a b : ℝ} (hab : a≠b) :
    dd1 (fun e => -(A+e*B)*(Y e+t*(X e)^2)) a b =
    -B*(Y b+t*(X b)^2)-(A+a*B)*dd1 Y a b-
      ((A+a*B)*t*(X a+X b))*dd1 X a b := by
  have he : (fun e => -(A+e*B)*(Y e+t*(X e)^2)) = fun e => -1*((A+e*B)*(Y e+t*(X e)^2)) := by funext e; ring
  rw [he,dd1_mul,dd1_affine_mul _ _ _ hab,dd1_add,dd1_mul,dd1_square]
  ring

lemma dd2_rhs (X Y : ℝ → ℝ) (A B t : ℝ) {a b c : ℝ}
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    dd2 (fun e => -(A+e*B)*(Y e+t*(X e)^2)) a b c =
    (-(A+a*B)*t*dd1 X a b*dd1 X b c-B*(dd1 Y b c+t*(X b+X c)*dd1 X b c))-
      (A+a*B)*dd2 Y a b c-((A+a*B)*t*(X a+X c))*dd2 X a b c := by
  have he : (fun e => -(A+e*B)*(Y e+t*(X e)^2)) = fun e => -1*((A+e*B)*(Y e+t*(X e)^2)) := by funext e; ring
  rw [he,dd2_mul,dd2_affine_mul _ _ _ hab hac hbc,dd2_add,dd2_mul,dd2_square _ hab hac hbc,
    dd1_add,dd1_mul,dd1_square]
  ring

lemma dd3_rhs (X Y : ℝ → ℝ) (A B t : ℝ) {a b c d : ℝ}
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    dd3 (fun e => -(A+e*B)*(Y e+t*(X e)^2)) a b c d =
    (-(A+a*B)*t*(dd1 X a b*dd2 X b c d+dd2 X a b c*dd1 X c d)-
      B*(dd2 Y b c d+t*((X b+X d)*dd2 X b c d+dd1 X b c*dd1 X c d)))-
      (A+a*B)*dd3 Y a b c d-((A+a*B)*t*(X a+X d))*dd3 X a b c d := by
  have he : (fun e => -(A+e*B)*(Y e+t*(X e)^2)) = fun e => -1*((A+e*B)*(Y e+t*(X e)^2)) := by funext e; ring
  rw [he,dd3_mul,dd3_affine_mul _ _ _ hab hac had hbc hbd hcd,dd3_add,dd3_mul,
    dd3_square _ hab hac had hbc hbd hcd,dd2_add,dd2_mul,dd2_square _ hbc hbd hcd]
  ring

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

lemma field1_time {I : Set ℝ} {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t : ℝ}
    (hf : ∀ e∈I,HasDerivAt (F e) (D e) t) (p : Nodes2 I) :
    HasDerivAt (fun s => dd1 (fun e => F e s) p.a p.b) (dd1 D p.a p.b) t :=
  ((hf p.b p.hb).sub (hf p.a p.ha)).div_const (p.b-p.a)

lemma field2_time {I : Set ℝ} {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t : ℝ}
    (hf : ∀ e∈I,HasDerivAt (F e) (D e) t) (p : Nodes3 I) :
    HasDerivAt (fun s => dd2 (fun e => F e s) p.a p.b p.c) (dd2 D p.a p.b p.c) t :=
  ((field1_time hf p.bc).sub (field1_time hf p.toNodes2)).div_const (p.c-p.a)

lemma field3_time {I : Set ℝ} {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {t : ℝ}
    (hf : ∀ e∈I,HasDerivAt (F e) (D e) t) (p : Nodes4 I) :
    HasDerivAt (fun s => dd3 (fun e => F e s) p.a p.b p.c p.d) (dd3 D p.a p.b p.c p.d) t :=
  ((field2_time hf p.bcd).sub (field2_time hf p.toNodes3)).div_const (p.d-p.a)

def source1 {I : Set ℝ} (F : ℝ → ℝ → ℝ → ℝ) (B : ℝ → ℝ) (p : Nodes2 I) (t x : ℝ) : ℝ :=
  -B t*(iteratedDeriv 2 (F p.b t) x+t*(iteratedDeriv 1 (F p.b t) x)^2)

def source2 {I : Set ℝ} (F : ℝ → ℝ → ℝ → ℝ) (A B : ℝ → ℝ) (p : Nodes3 I) (t x : ℝ) : ℝ :=
  -(A t+p.a*B t)*t*iteratedDeriv 1 (field1 F p.a p.b t) x*iteratedDeriv 1 (field1 F p.b p.c t) x-
  B t*(iteratedDeriv 2 (field1 F p.b p.c t) x+
  t*(iteratedDeriv 1 (F p.b t) x+iteratedDeriv 1 (F p.c t) x)*iteratedDeriv 1 (field1 F p.b p.c t) x)

def source3 {I : Set ℝ} (F : ℝ → ℝ → ℝ → ℝ) (A B : ℝ → ℝ) (p : Nodes4 I) (t x : ℝ) : ℝ :=
  -(A t+p.a*B t)*t*(iteratedDeriv 1 (field1 F p.a p.b t) x*iteratedDeriv 1 (field2 F p.b p.c p.d t) x+
    iteratedDeriv 1 (field2 F p.a p.b p.c t) x*iteratedDeriv 1 (field1 F p.c p.d t) x)-
  B t*(iteratedDeriv 2 (field2 F p.b p.c p.d t) x+t*(
    (iteratedDeriv 1 (F p.b t) x+iteratedDeriv 1 (F p.d t) x)*iteratedDeriv 1 (field2 F p.b p.c p.d t) x+
    iteratedDeriv 1 (field1 F p.b p.c t) x*iteratedDeriv 1 (field1 F p.c p.d t) x))

lemma field1_equation {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (p : Nodes2 I) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (fun s => field1 F p.a p.b s x)
    (source1 F B p t x-(A t+p.a*B t)*iteratedDeriv 2 (field1 F p.a p.b t) x-
      ((A t+p.a*B t)*t*(iteratedDeriv 1 (F p.a t) x+iteratedDeriv 1 (F p.b t) x))*iteratedDeriv 1 (field1 F p.a p.b t) x) t := by
  have hh := field1_time (fun e he => hf.time e he t ht x) p
  have htc : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  rw [dd1_rhs _ _ _ _ _ p.hab] at hh
  simpa only [field1_jet hf.smooth p 2 htc x,field1_jet hf.smooth p 1 htc x,source1,field1] using hh

lemma field2_equation {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (p : Nodes3 I) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (fun s => field2 F p.a p.b p.c s x)
    (source2 F A B p t x-(A t+p.a*B t)*iteratedDeriv 2 (field2 F p.a p.b p.c t) x-
      ((A t+p.a*B t)*t*(iteratedDeriv 1 (F p.a t) x+iteratedDeriv 1 (F p.c t) x))*iteratedDeriv 1 (field2 F p.a p.b p.c t) x) t := by
  have hh := field2_time (fun e he => hf.time e he t ht x) p
  have htc : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  rw [dd2_rhs _ _ _ _ _ p.hab p.hac p.hbc] at hh
  unfold source2
  rw [field2_jet hf.smooth p 2 htc x,field2_jet hf.smooth p 1 htc x,
    field1_jet hf.smooth p.toNodes2 1 htc x]
  have hbc1 := field1_jet hf.smooth p.bc 1 htc x
  have hbc2 := field1_jet hf.smooth p.bc 2 htc x
  dsimp [Nodes3.bc] at hbc1 hbc2
  rw [hbc1,hbc2]
  exact hh

lemma field3_equation {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (p : Nodes4 I) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (fun s => field3 F p.a p.b p.c p.d s x)
    (source3 F A B p t x-(A t+p.a*B t)*iteratedDeriv 2 (field3 F p.a p.b p.c p.d t) x-
      ((A t+p.a*B t)*t*(iteratedDeriv 1 (F p.a t) x+iteratedDeriv 1 (F p.d t) x))*iteratedDeriv 1 (field3 F p.a p.b p.c p.d t) x) t := by
  have hh := field3_time (fun e he => hf.time e he t ht x) p
  have htc : t∈Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  rw [dd3_rhs _ _ _ _ _ p.hab p.hac p.had p.hbc p.hbd p.hcd] at hh
  unfold source3
  rw [field3_jet hf.smooth p 2 htc x,field3_jet hf.smooth p 1 htc x,
    field1_jet hf.smooth p.toNodes3.toNodes2 1 htc x,field2_jet hf.smooth p.toNodes3 1 htc x]
  have hbc1 := field1_jet hf.smooth p.toNodes3.bc 1 htc x
  have hcd1 := field1_jet hf.smooth p.cd 1 htc x
  have hbcd1 := field2_jet hf.smooth p.bcd 1 htc x
  have hbcd2 := field2_jet hf.smooth p.bcd 2 htc x
  dsimp [Nodes3.bc,Nodes4.cd,Nodes4.bcd] at hbc1 hcd1 hbcd1 hbcd2
  rw [hbc1,hcd1,hbcd1,hbcd2]
  exact hh

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

lemma family_mul_time {ι : Type*} {G : ι → ℝ → ℝ → ℝ}
    (hG : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) G) :
    PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) (fun i t x => t*G i t x) :=
  hG.coeff_mul (fun _ _ => continuousOn_id) (by norm_num : (0:ℝ)≤1)
    (fun _ _ _ ht => by rw [abs_of_nonneg ht.1]; exact ht.2)

lemma RankFamilyData.mul_B {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) {ι : Type*} {G : ι → ℝ → ℝ → ℝ}
    (hG : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) G) :
    PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) (fun i t x => B t*G i t x) := by
  obtain ⟨D,hD,_,hB⟩ := hf.coeff
  exact hG.coeff_mul (fun _ _ => hf.Bcont) hD (fun _ _ => hB)

lemma RankFamilyData.mul_at {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) {ι : Type*} (l : ι → ℝ) (hl : ∀ i,l i∈I) {G : ι → ℝ → ℝ → ℝ}
    (hG : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) G) :
    PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) (fun i t x => (A t+l i*B t)*t*G i t x) := by
  obtain ⟨D,hD,ha,_⟩ := hf.coeff
  apply hG.coeff_mul (fun i _ => (hf.diffusion_cont (l i)).mul continuousOn_id) hD
  intro i _ t ht
  change |(A t+l i*B t)*t|≤D
  rw [abs_mul,abs_of_nonneg (ha (l i) (hl i) t ht).1,abs_of_nonneg ht.1]
  exact (mul_le_mul_of_nonneg_right (ha (l i) (hl i) t ht).2 ht.1).trans (by nlinarith [ht.2])

lemma source1_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun _ : Nodes2 I => True) (Icc 0 1) (source1 F B) := by
  have hbase := hf.poly.comp (R:=fun _ => True) (fun p : Nodes2 I => p.b) (fun p _ => p.hb)
  have hh := (hf.mul_B ((hbase.jet 2).add (family_mul_time ((hbase.jet 1).mul (hbase.jet 1))))).const_mul (-1)
  convert hh using 1
  funext p t x
  dsimp only [source1]
  ring

lemma field1_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) :
    PolynomialJetFamily (fun _ : Nodes2 I => True) (Icc 0 1) (fun p => field1 F p.a p.b) := by
  apply hf.endpoint_linear (fun p : Nodes2 I => p.a) (fun p => p.b) (fun p => p.ha) (fun p => p.hb)
    (field1_smooth hf.smooth) (fun p n => ((field1_individual hf.poly p).bounds n).individual (i:=()) trivial)
    (source1_poly hf) (fun p t ht x => field1_equation hf p ht x)
  intro p x
  unfold field1 dd1
  dsimp only
  rw [hf.terminal p.b p.hb p.a p.ha x]
  simp

lemma source2_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun _ : Nodes3 I => True) (Icc 0 1) (source2 F A B) := by
  have hab := (field1_poly hf).comp (R:=fun _ => True) (fun p : Nodes3 I => p.toNodes2) (fun _ _ => trivial)
  have hbc := (field1_poly hf).comp (R:=fun _ => True) (fun p : Nodes3 I => p.bc) (fun _ _ => trivial)
  have hb := hf.poly.comp (R:=fun _ => True) (fun p : Nodes3 I => p.b) (fun p _ => p.hb)
  have hc := hf.poly.comp (R:=fun _ => True) (fun p : Nodes3 I => p.c) (fun p _ => p.hc)
  have hleft := (hf.mul_at (fun p : Nodes3 I => p.a) (fun p => p.ha) ((hab.jet 1).mul (hbc.jet 1))).const_mul (-1)
  have hright := hf.mul_B ((hbc.jet 2).add (family_mul_time (((hb.jet 1).add (hc.jet 1)).mul (hbc.jet 1))))
  convert hleft.sub hright using 1
  funext p t x
  dsimp only [source2,Nodes3.bc]
  ring

lemma field2_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) :
    PolynomialJetFamily (fun _ : Nodes3 I => True) (Icc 0 1) (fun p => field2 F p.a p.b p.c) := by
  apply hf.endpoint_linear (fun p : Nodes3 I => p.a) (fun p => p.c) (fun p => p.ha) (fun p => p.hc)
    (field2_smooth hf.smooth) (fun p n => ((field2_individual hf.poly p).bounds n).individual (i:=()) trivial)
    (source2_poly hf) (fun p t ht x => field2_equation hf p ht x)
  intro p x
  unfold field2 dd2 dd1
  dsimp only
  rw [hf.terminal p.b p.hb p.a p.ha x,hf.terminal p.c p.hc p.a p.ha x]
  simp

lemma source3_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun _ : Nodes4 I => True) (Icc 0 1) (source3 F A B) := by
  have hab := (field1_poly hf).comp (R:=fun _ => True) (fun p : Nodes4 I => p.toNodes3.toNodes2) (fun _ _ => trivial)
  have hbc := (field1_poly hf).comp (R:=fun _ => True) (fun p : Nodes4 I => p.toNodes3.bc) (fun _ _ => trivial)
  have hcd := (field1_poly hf).comp (R:=fun _ => True) (fun p : Nodes4 I => p.cd) (fun _ _ => trivial)
  have habc := (field2_poly hf).comp (R:=fun _ => True) (fun p : Nodes4 I => p.toNodes3) (fun _ _ => trivial)
  have hbcd := (field2_poly hf).comp (R:=fun _ => True) (fun p : Nodes4 I => p.bcd) (fun _ _ => trivial)
  have hb := hf.poly.comp (R:=fun _ => True) (fun p : Nodes4 I => p.b) (fun p _ => p.hb)
  have hd := hf.poly.comp (R:=fun _ => True) (fun p : Nodes4 I => p.d) (fun p _ => p.hd)
  have hleft := (hf.mul_at (fun p : Nodes4 I => p.a) (fun p => p.ha)
    (((hab.jet 1).mul (hbcd.jet 1)).add ((habc.jet 1).mul (hcd.jet 1)))).const_mul (-1)
  have hright := hf.mul_B ((hbcd.jet 2).add (family_mul_time
    ((((hb.jet 1).add (hd.jet 1)).mul (hbcd.jet 1)).add ((hbc.jet 1).mul (hcd.jet 1)))))
  convert hleft.sub hright using 1
  funext p t x
  dsimp only [source3,Nodes3.bc,Nodes4.cd,Nodes4.bcd]
  ring

lemma field3_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) :
    PolynomialJetFamily (fun _ : Nodes4 I => True) (Icc 0 1) (fun p => field3 F p.a p.b p.c p.d) := by
  apply hf.endpoint_linear (fun p : Nodes4 I => p.a) (fun p => p.d) (fun p => p.ha) (fun p => p.hd)
    (field3_smooth hf.smooth) (fun p n => ((field3_individual hf.poly p).bounds n).individual (i:=()) trivial)
    (source3_poly hf) (fun p t ht x => field3_equation hf p ht x)
  intro p x
  unfold field3 dd3 dd2 dd1
  dsimp only
  rw [hf.terminal p.b p.hb p.a p.ha x,hf.terminal p.c p.hc p.a p.ha x,hf.terminal p.d p.hd p.a p.ha x]
  simp

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology NNReal

namespace MicroscopicJamming
namespace Parameter

lemma differentiable_of_dd2_bound {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    {M : ℝ} (hM : 0≤M)
    (hb : ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c → |dd2 F a b c|≤M) :
    ∀ a∈I,DifferentiableAt ℝ F a := by
  intro a ha
  let K : ℝ≥0 := ⟨M,hM⟩
  have hLip : LipschitzOnWith K (dd1 F a) (I\{a}) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro b hb' c hc'
    by_cases hbc : b=c
    · simp [hbc]
    have hab : a≠b := (show b≠a from hb'.2).symm
    have hac : a≠c := (show c≠a from hc'.2).symm
    rw [Real.dist_eq,Real.dist_eq,dd1_sub_slope F hab hac hbc,abs_mul]
    calc
      |b-c| * |dd2 F a b c| ≤ |b-c| * M := mul_le_mul_of_nonneg_left (hb a ha b hb'.1 c hc'.1 hab hac hbc) (abs_nonneg _)
      _ = _ := by change |b-c| * M = M * |b-c|; ring
  obtain ⟨g,hg,he⟩ := hLip.extend_real
  have hd : HasDerivAt F (g a) a := by
    rw [hasDerivAt_iff_tendsto_slope]
    apply (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds ha),self_mem_nhdsWithin] with y hy hya
    rw [slope_def_field]
    exact (he ⟨hy,hya⟩).symm
  exact hd.differentiableAt

lemma tendsto_dd2_left {F : ℝ → ℝ} (hF : DifferentiableAt ℝ F 0) {k : ℝ} (hk : k≠0) :
    Tendsto (fun h => dd2 F 0 h k) (𝓝[≠] 0) (𝓝 ((dd1 F 0 k-deriv F 0)/k)) := by
  have h1 : Tendsto (fun h => dd1 F h k) (𝓝[≠] 0) (𝓝 (dd1 F 0 k)) := by
    unfold dd1
    apply Tendsto.div
    · exact tendsto_const_nhds.sub (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · exact tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    · simpa using hk
  have h2 : Tendsto (fun h => dd1 F 0 h) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
    have he : (fun h => dd1 F 0 h)=slope F 0 := funext (fun h => (slope_def_field F 0 h).symm)
    rw [he]
    exact hF.hasDerivAt.tendsto_slope
  simpa only [dd2,sub_zero] using (h1.sub h2).div_const k

lemma second_remainder_lipschitz {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    (hF : DifferentiableAt ℝ F 0) {M : ℝ} (hM : 0≤M)
    (hb : ∀ a∈I,∀ b∈I,∀ c∈I,∀ d∈I,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → |dd3 F a b c d|≤M) :
    LipschitzOnWith ⟨M,hM⟩ (fun k => (dd1 F 0 k-deriv F 0)/k) (I\{0}) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro k hk l hl
  by_cases hkl : k=l
  · simp [hkl]
  have hk0 : k≠0 := hk.2
  have hl0 : l≠0 := hl.2
  rw [Real.dist_eq,Real.dist_eq]
  have hc := ((tendsto_dd2_left hF hk0).sub (tendsto_dd2_left hF hl0)).abs
  apply le_of_tendsto hc
  have heg : ∀ᶠ h in 𝓝[≠] (0:ℝ),h∈I ∧ h≠0 ∧ h≠k ∧ h≠l := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds h0),self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hk0.symm),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hl0.symm)]
      with h hi hne hnk hnl
    exact ⟨hi,hne,hnk,hnl⟩
  filter_upwards [heg] with h hh
  rw [dd2_sub_last F hh.2.1.symm hk0.symm hl0.symm hh.2.2.1 hh.2.2.2 hkl,abs_mul]
  calc
    |k-l| * |dd3 F 0 h k l| ≤ |k-l| * M := mul_le_mul_of_nonneg_left
      (hb 0 h0 h hh.1 k hk.1 l hl.1 hh.2.1.symm hk0.symm hl0.symm hh.2.2.1 hh.2.2.2 hkl) (abs_nonneg _)
    _ = _ := by change |k-l| * M = M * |k-l|; ring

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology NNReal

namespace MicroscopicJamming
namespace Parameter

lemma twice_differentiable_of_dd_bounds {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    {M₂ M₃ : ℝ} (hM₂ : 0≤M₂) (hM₃ : 0≤M₃)
    (hb₂ : ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c → |dd2 F a b c|≤M₂)
    (hb₃ : ∀ a∈I,∀ b∈I,∀ c∈I,∀ d∈I,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → |dd3 F a b c d|≤M₃) :
    DifferentiableAt ℝ F 0 ∧ DifferentiableAt ℝ (deriv F) 0 := by
  have hd := differentiable_of_dd2_bound hI hM₂ hb₂
  refine ⟨hd 0 h0,?_⟩
  obtain ⟨g,hg,he⟩ := (second_remainder_lipschitz hI h0 (hd 0 h0) hM₃ hb₃).extend_real
  have hgm (k : ℝ) (hk : k∈I\{0}) :
      g k=(dd1 F 0 k-deriv F 0)/k := (he hk).symm
  have hgd (k : ℝ) (hk : k∈I\{0}) : DifferentiableAt ℝ g k := by
    have hk0 : k≠0 := hk.2
    have hr : DifferentiableAt ℝ (fun k => (dd1 F 0 k-deriv F 0)/k) k := by
      unfold dd1
      exact ((((hd k hk.1).sub_const _).div (differentiableAt_id.sub_const _) (by simpa using hk0)).sub_const _).div
        differentiableAt_id hk0
    apply hr.congr_of_eventuallyEq
    filter_upwards [(hI.sdiff isClosed_singleton).mem_nhds hk] with y hy
    exact hgm y hy
  have hrepr (k : ℝ) (hk : k∈I\{0}) : F k=F 0+deriv F 0*k+g k*k^2 := by
    rw [hgm k hk]
    unfold dd1
    have hk0 : k≠0 := hk.2
    simp only [sub_zero]
    field_simp
    ring
  have hder (k : ℝ) (hk : k∈I\{0}) :
      deriv F k=deriv F 0+deriv g k*k^2+g k*(2*k) := by
    have hh := ((hasDerivAt_const k (F 0)).add ((hasDerivAt_id k).const_mul (deriv F 0))).add
      ((hgd k hk).hasDerivAt.mul ((hasDerivAt_id k).pow 2))
    change HasDerivAt (fun y => F 0+deriv F 0*y+g y*y^2)
      (0+deriv F 0*1+(deriv g k*k^2+g k*(2*k^(2-1)*1))) k at hh
    norm_num only [Nat.reduceSub,pow_one,mul_one,zero_add] at hh
    have hhe : HasDerivAt F (deriv F 0+deriv g k*k^2+g k*(2*k)) k := by
      have ha : deriv F 0+(deriv g k*k^2+g k*(2*k))=deriv F 0+deriv g k*k^2+g k*(2*k) := by ring
      rw [ha] at hh
      apply hh.congr_of_eventuallyEq
      filter_upwards [(hI.sdiff isClosed_singleton).mem_nhds hk] with y hy
      exact hrepr y hy
    exact hhe.deriv
  have hb (k : ℝ) : |deriv g k|≤M₃ := by
    have hh := (norm_deriv_le_of_lipschitz hg : ‖deriv g k‖≤(⟨M₃,hM₃⟩:ℝ≥0))
    change |deriv g k|≤M₃ at hh
    exact hh
  have hv : Tendsto (fun k : ℝ => deriv g k*k) (𝓝 0) (𝓝 0) := by
    have hbound (k : ℝ) : ‖deriv g k*k‖≤M₃*|k| := by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hb k) (abs_nonneg _)
    have hh : Tendsto (fun k : ℝ => M₃*|k|) (𝓝 0) (𝓝 0) := by
      have hc := (((continuous_const : Continuous (fun _ : ℝ => M₃)).mul continuous_abs).continuousAt (x:= (0:ℝ))).tendsto
      change Tendsto (fun k : ℝ => M₃*|k|) (𝓝 0) (𝓝 (M₃*|0|)) at hc
      simpa only [abs_zero,mul_zero] using hc
    exact squeeze_zero_norm hbound hh
  have hsl : Tendsto (slope (deriv F) 0) (𝓝[≠] 0) (𝓝 (2*g 0)) := by
    have hh : Tendsto (fun k : ℝ => deriv g k*k+2*g k) (𝓝[≠] 0) (𝓝 (0+2*g 0)) := (hv.mono_left nhdsWithin_le_nhds).add
      ((hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul 2)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds h0),self_mem_nhdsWithin] with k hk hk0
    rw [slope_def_field,hder k ⟨hk,hk0⟩]
    have hkne : k≠0 := hk0
    simp only [sub_zero]
    field_simp
    ring
  exact (hasDerivAt_iff_tendsto_slope.mpr hsl).differentiableAt

end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
open Higher Parameter

lemma RankFamilyData.parameter_C2 {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (hI : IsOpen I) (h0 : (0:ℝ)∈I) :
    ∀ n : ℕ,∀ t∈Icc (0:ℝ) 1,∀ x,
      DifferentiableAt ℝ (fun e => iteratedDeriv n (F e t) x) 0 ∧
      DifferentiableAt ℝ (deriv (fun e => iteratedDeriv n (F e t) x)) 0 := by
  intro n t ht x
  obtain ⟨n₂,C₂,hC₂,hb₂⟩ := (field2_poly hf).bounds n
  obtain ⟨n₃,C₃,hC₃,hb₃⟩ := (field3_poly hf).bounds n
  apply twice_differentiable_of_dd_bounds hI h0 (show 0≤C₂*(1+|x|)^n₂ by positivity)
    (show 0≤C₃*(1+|x|)^n₃ by positivity)
  · intro a ha b hb c hc hab hac hbc
    let p : Nodes3 I := ⟨⟨a,b,ha,hb,hab⟩,c,hc,hac,hbc⟩
    have hh := hb₂ p trivial t ht x
    dsimp only at hh
    rw [field2_jet hf.smooth p n ht x] at hh
    exact hh
  · intro a ha b hb c hc d hd hab hac had hbc hbd hcd
    let p : Nodes4 I := ⟨⟨⟨a,b,ha,hb,hab⟩,c,hc,hac,hbc⟩,d,hd,had,hbd,hcd⟩
    have hh := hb₃ p trivial t ht x
    dsimp only at hh
    rw [field3_jet hf.smooth p n ht x] at hh
    exact hh

 

theorem row_parameter : RowParameterStatement := by
  intro u q η A B C κ Q hQ hu hq hη hη0 hη1
  obtain ⟨r,hr,F,hF,hdata⟩ := actual_parameter_family hQ hu hq hη hη0 hη1
  refine ⟨r,hr,F,hF,?_⟩
  exact RankFamilyData.parameter_C2 hdata isOpen_Ioo ⟨by linarith,hr⟩

end MicroscopicJamming

end

end OAI
