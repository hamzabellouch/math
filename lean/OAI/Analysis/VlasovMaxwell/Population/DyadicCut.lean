import Mathlib

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def dyadicCut (x : ℝ) : ℝ := 1-Real.smoothTransition (x-1)
def dyadicBump (x : ℝ) : ℝ := dyadicCut x-dyadicCut (2*x)
def dyadicFactor (n : ℕ) (x : ℝ) : ℝ := dyadicBump ((2:ℝ)^n*x)

lemma contDiff_dyadicCut : ContDiff ℝ ∞ dyadicCut :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
lemma contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCut.sub (contDiff_dyadicCut.comp (contDiff_const.mul contDiff_id))
lemma contDiff_dyadicFactor (n : ℕ) : ContDiff ℝ ∞ (dyadicFactor n) :=
  contDiff_dyadicBump.comp (contDiff_const.mul contDiff_id)

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
lemma dyadicCut_nonneg (x : ℝ) : 0≤dyadicCut x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma dyadicCut_le_one (x : ℝ) : dyadicCut x≤1 := sub_le_self _ (Real.smoothTransition.nonneg _)
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicBump_le_one (x : ℝ) : dyadicBump x≤1 :=
  (sub_le_self _ (dyadicCut_nonneg _)).trans (dyadicCut_le_one _)
lemma dyadicBump_support : tsupport dyadicBump ⊆ Icc (1/2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hx (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))
lemma compactSupport_dyadicBump : HasCompactSupport dyadicBump :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) dyadicBump_support
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _
lemma dyadicFactor_le_one (n : ℕ) (x : ℝ) : dyadicFactor n x≤1 := dyadicBump_le_one _

lemma dyadicFactor_eq (n : ℕ) (x : ℝ) :
    dyadicFactor n x=dyadicCut ((2:ℝ)^n*x)-dyadicCut ((2:ℝ)^(n+1)*x) := by
  simp only [dyadicFactor,dyadicBump,pow_succ]
  congr 2
  ring
lemma sum_dyadicFactor (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, dyadicFactor n x=dyadicCut x-dyadicCut ((2:ℝ)^N*x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,dyadicFactor_eq]; ring

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

lemma dyadicFactor_eventually_zero {x : ℝ} (hx : 0<x) :
    ∃ N : ℕ, ∀ n, N≤n → ∀ y, x/2<y → dyadicFactor n y=0 := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (4/x) (by norm_num : (1:ℝ)<2)
  refine ⟨N,fun n hn y hy => dyadicFactor_zero_large ?_⟩
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
  have hN' : 4<(2:ℝ)^N*x := (div_lt_iff₀ hx).mp hN
  have hp : 0<(2:ℝ)^n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hpow hx.le]

lemma dyadicFactor_locally_finite {x : ℝ} (hx : 0<x) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n, N≤n → dyadicFactor n y=0 := by
  obtain ⟨N,hN⟩ := dyadicFactor_eventually_zero hx
  refine ⟨N,?_⟩
  filter_upwards [Ioi_mem_nhds (show x/2<x by linarith)] with y hy n hn
  exact hN n hn y hy

lemma tsum_dyadicFactor {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    ∑' n : ℕ, dyadicFactor n x=1 := by
  obtain ⟨N,hN⟩ := dyadicFactor_eventually_zero hx
  have hz (n : ℕ) (hn : n ∉ Finset.range N) : dyadicFactor n x=0 :=
    hN n (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)) x (by linarith)
  rw [tsum_eq_sum (s:=Finset.range N) hz,sum_dyadicFactor,dyadicCut_one hx1]
  have hN' := hN N le_rfl (x/2+ x/4) (by linarith)
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (2/x) (by norm_num : (1:ℝ)<2)
  have hm : 2≤(2:ℝ)^(max N M)*x :=
    ((div_lt_iff₀ hx).mp hM).le.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (le_max_right N M)) hx.le)
  have he := sum_dyadicFactor (max N M) x
  have hs : ∑ n ∈ Finset.range (max N M), dyadicFactor n x =
      ∑ n ∈ Finset.range N, dyadicFactor n x := by
    symm
    apply Finset.sum_subset (Finset.range_mono (le_max_left N M))
    intro n _ hn
    exact hz n hn
  rw [hs,sum_dyadicFactor,dyadicCut_one hx1,dyadicCut_zero hm,sub_zero] at he
  exact he

lemma hasDerivAt_dyadicFactor (n : ℕ) (x : ℝ) :
    HasDerivAt (dyadicFactor n) ((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) x := by
  have hh := ((contDiff_dyadicBump.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul ((2:ℝ)^n))
  change HasDerivAt (fun y => dyadicBump ((2:ℝ)^n*y)) _ x
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using hh

lemma dyadicFactor_log_derivative_bound : ∃ C : ℝ, 0≤C ∧
    ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C := by
  have hd : Continuous (deriv dyadicBump) := contDiff_dyadicBump.continuous_deriv (by simp)
  have hcon : Continuous (fun x : ℝ => x*deriv dyadicBump x) := continuous_id.mul hd
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hcon).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,fun n x => ?_⟩
  rw [(hasDerivAt_dyadicFactor n x).deriv]
  have he : x*((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) =
      ((2:ℝ)^n*x)*deriv dyadicBump ((2:ℝ)^n*x) := by ring
  rw [he]
  by_cases hx : (2:ℝ)^n*x ∈ Icc (1/2:ℝ) 2
  · exact (hC _ ⟨(2:ℝ)^n*x,hx,rfl⟩).trans (le_max_right _ _)
  · rw [deriv_of_notMem_tsupport (fun h => hx (dyadicBump_support h)),mul_zero,abs_zero]
    exact le_max_left _ _

def DyadicBand (n : ℕ) (x : ℝ) : Prop := 1/2≤(2:ℝ)^n*x ∧ (2:ℝ)^n*x≤2

lemma dyadicFactor_tsupport {n : ℕ} {x : ℝ} (hx : x ∈ tsupport (dyadicFactor n)) :
    DyadicBand n x := by
  have hcl : IsClosed {x : ℝ | DyadicBand n x} :=
    (isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
      (isClosed_le (continuous_const.mul continuous_id) continuous_const)
  apply (closure_minimal (s:=(Function.support (dyadicFactor n))) ?_ hcl) hx
  intro y hy
  constructor
  · by_contra hn
    exact hy (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hy (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

lemma dyadicBand_index_le {n m : ℕ} {x : ℝ} (hn : DyadicBand n x) (hm : DyadicBand m x) :
    m≤n+2 := by
  by_contra hmn
  have hnm : n+3 ≤ m := by omega
  have hx : 0≤x := by
    have hp : 0<(2:ℝ)^n := by positivity
    by_contra hh
    have he := mul_neg_of_pos_of_neg hp (lt_of_not_ge hh)
    linarith [hn.1]
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnm) hx
  rw [pow_add] at he
  norm_num at he
  nlinarith [hn.1,hm.2]

lemma dyadicBand_card_le (S : Finset ℕ) {x : ℝ} (hS : ∀ n ∈ S, DyadicBand n x) :
    S.card≤5 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨n,hn⟩ := hs
    have hsub : S ⊆ Finset.Icc (n-2) (n+2) := by
      intro m hm
      have hlo := dyadicBand_index_le (hS m hm) (hS n hn)
      have hhi := dyadicBand_index_le (hS n hn) (hS m hm)
      exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasDerivAt_dyadicCut_zero_left {x : ℝ} (hx : x≤1) : HasDerivAt dyadicCut 0 x := by
  have hm : IsLocalMax dyadicCut x := Filter.Eventually.of_forall (fun y => by
    rw [dyadicCut_one hx]
    exact dyadicCut_le_one y)
  rw [← hm.deriv_eq_zero]
  exact (contDiff_dyadicCut.differentiable (by simp) x).hasDerivAt

lemma hasDerivAt_dyadicCut_zero_right {x : ℝ} (hx : 2≤x) : HasDerivAt dyadicCut 0 x := by
  have hm : IsLocalMin dyadicCut x := Filter.Eventually.of_forall (fun y => by
    rw [dyadicCut_zero hx]
    exact dyadicCut_nonneg y)
  rw [← hm.deriv_eq_zero]
  exact (contDiff_dyadicCut.differentiable (by simp) x).hasDerivAt

lemma hasDerivAt_sum_dyadicFactor_zero {x : ℝ} (N : ℕ) (hx : x≤1)
    (hN : 2≤(2:ℝ)^N*x) :
    HasDerivAt (fun y => ∑ n∈Finset.range N, dyadicFactor n y) 0 x := by
  have h := (hasDerivAt_dyadicCut_zero_left hx).sub
    ((hasDerivAt_dyadicCut_zero_right hN).comp x ((hasDerivAt_id x).const_mul ((2:ℝ)^N)))
  convert h using 1 <;> first | rfl | (simp [sum_dyadicFactor] <;> rfl)

def dyadicMultiFactor {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, dyadicFactor (n i) (x i)

def dyadicBox (ι : Type*) [Fintype ι] (N : ℕ) : Finset (ι → ℕ) :=
  by classical exact Fintype.piFinset (fun _ : ι => Finset.range N)

lemma dyadicMultiFactor_nonneg {ι : Type*} [Fintype ι] (n : ι→ℕ) (x : ι→ℝ) :
    0≤dyadicMultiFactor n x := Finset.prod_nonneg (fun _i _ => dyadicFactor_nonneg _ _)

lemma sum_dyadicMultiFactor {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x =
      ∏ i, (dyadicCut (x i)-dyadicCut ((2:ℝ)^N*x i)) := by
  classical
  unfold dyadicBox dyadicMultiFactor
  convert Finset.sum_prod_piFinset (Finset.range N) (fun i n => dyadicFactor n (x i)) using 1
  simp only [sum_dyadicFactor]

lemma sum_dyadicMultiFactor_eq_one {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ)
    (hx : ∀ i, x i≤1) (hN : ∀ i, 2≤(2:ℝ)^N*x i) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x=1 := by
  rw [sum_dyadicMultiFactor]
  simp only [dyadicCut_one (hx _),dyadicCut_zero (hN _),sub_zero,Finset.prod_const_one]

lemma differentiableAt_dyadicMultiFactor_curve {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t) (n : ι→ℕ) :
    DifferentiableAt ℝ (fun r => dyadicMultiFactor n (fun i => g i r)) t := by
  classical
  exact DifferentiableAt.fun_finsetProd (fun i _ =>
    (contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t) |>.comp t (hg i))

lemma hasDerivAt_sum_dyadicMultiFactor_zero {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t) :
    HasDerivAt (fun r => ∑ n∈dyadicBox ι N, dyadicMultiFactor n (fun i => g i r)) 0 t := by
  classical
  have hd (i : ι) : HasDerivAt (fun r => ∑ n∈Finset.range N,dyadicFactor n (g i r)) 0 t := by
    simpa only [Function.comp_def,zero_mul] using
      (hasDerivAt_sum_dyadicFactor_zero N (hx i) (hN i)).comp t (hg i).hasDerivAt
  have H := HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _ => hd i)
  simpa only [smul_zero,Finset.sum_const_zero,sum_dyadicFactor,← sum_dyadicMultiFactor] using H

lemma selected_dyadic_derivative_cancel {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t)
    (S : Finset (ι→ℕ)) (hS : S⊆dyadicBox ι N) :
    deriv (fun r => ∑ n∈S,dyadicMultiFactor n (fun i => g i r)) t =
      -(∑ n∈dyadicBox ι N \ S,deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t) := by
  classical
  have hd := differentiableAt_dyadicMultiFactor_curve hg
  rw [deriv_fun_sum (fun n _ => hd n)]
  have hall := (hasDerivAt_sum_dyadicMultiFactor_zero hg N hx hN).deriv
  rw [deriv_fun_sum (fun n _ => hd n)] at hall
  have he := Finset.sum_sdiff (f:=fun n => deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t) hS
  rw [hall] at he
  linarith

lemma selected_dyadic_derivative_boundary {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t)
    (S : Finset (ι→ℕ)) (hS : S⊆dyadicBox ι N)
    (hne : deriv (fun r => ∑ n∈S,dyadicMultiFactor n (fun i => g i r)) t ≠ 0) :
    (∃ n∈S, 0<dyadicMultiFactor n (fun i => g i t)) ∧
    (∃ n∈dyadicBox ι N \ S, 0<dyadicMultiFactor n (fun i => g i t)) := by
  classical
  have pos_of_ne (U : Finset (ι→ℕ))
      (hu : deriv (fun r => ∑ n∈U,dyadicMultiFactor n (fun i => g i r)) t≠0) :
      ∃ n∈U,0<dyadicMultiFactor n (fun i => g i t) := by
    by_contra hh
    push Not at hh
    have he : ∑ n∈U,dyadicMultiFactor n (fun i => g i t)=0 :=
      Finset.sum_eq_zero (fun n hn => le_antisymm (hh n hn) (dyadicMultiFactor_nonneg _ _))
    apply hu
    apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only
      rw [he]
      exact Finset.sum_nonneg (fun n _ => dyadicMultiFactor_nonneg _ _))
  refine ⟨pos_of_ne S hne,pos_of_ne (dyadicBox ι N \ S) ?_⟩
  intro he
  apply hne
  rw [selected_dyadic_derivative_cancel hg N hx hN S hS,
    ← deriv_fun_sum (fun n _ => differentiableAt_dyadicMultiFactor_curve hg n),he,neg_zero]

lemma dyadicMultiFactor_positive_bands {ι : Type*} [Fintype ι]
    {n : ι→ℕ} {x : ι→ℝ} (h : 0<dyadicMultiFactor n x) : ∀ i,DyadicBand (n i) (x i) := by
  classical
  intro i
  apply dyadicFactor_tsupport
  apply subset_tsupport
  intro he
  have hz : dyadicMultiFactor n x=0 := Finset.prod_eq_zero (Finset.mem_univ i) he
  linarith

lemma dyadicMultiFactor_positive_index_comparison {ι : Type*} [Fintype ι]
    {n m : ι→ℕ} {x : ι→ℝ} (hn : 0<dyadicMultiFactor n x)
    (hm : 0<dyadicMultiFactor m x) : ∀ i, m i ≤ n i + 2 ∧ n i ≤ m i + 2 := by
  intro i
  exact ⟨dyadicBand_index_le (dyadicMultiFactor_positive_bands hn i)
    (dyadicMultiFactor_positive_bands hm i),dyadicBand_index_le
      (dyadicMultiFactor_positive_bands hm i) (dyadicMultiFactor_positive_bands hn i)⟩

end RVM

end

end OAI
