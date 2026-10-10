import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RatWeight

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}

lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset

theorem one_pass_scaling {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3) :
    (∀ k i, scalingTrace hn G (k+1) i ≤ scalingTrace hn G k i) ∧
    (∀ i, alpha/2 ≤ scalingTrace hn G n i ∧ scalingTrace hn G n i ≤ 2) ∧
    (∀ i j, i≠j → G i j ≤ scalingTrace hn G n i * scalingTrace hn G n j) ∧
    (∀ i, ∃ j, j≠i ∧ scalingTrace hn G n i * scalingTrace hn G n j=G i j) := by
  have htrace := scalingTrace_invariant hn G hsym hG
  refine ⟨?_,(htrace n).1.lower |> fun h => ?_⟩
  · intro k i
    by_cases hk : k<n
    · change (if h : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,h⟩ else scalingTrace hn G k) i ≤ _
      rw [dite_eq_left hk]
      exact scaleUpdate_le hn G _ (htrace k).1 ⟨k,hk⟩ i
    · simp [scalingTrace,hk]
  · refine ⟨fun i => ⟨h i,(htrace n).1.upper i⟩,(htrace n).1.feasible,?_⟩
    intro i
    exact (htrace n).2 i i.isLt




def rowPeak {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.erase i).sup' (others_nonempty hn i) (g i)

def scaledHoleMatrix {n : ℕ} (g : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i j : Fin n) : ℝ :=
  g i j/(v i*v j)

def BalancedRows {n : ℕ} (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) : Prop :=
  ∀ i, (1:ℝ)/4 ≤ rowPeak hn g i ∧ rowPeak hn g i ≤ 1




theorem one_pass_restores_balance {n : ℕ} (hn : 2 ≤ n) (g G : Fin n → Fin n → ℝ)
    (hGsym : ∀ i j, G i j=G j i)
    (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (hpre : ∀ i, (1:ℝ)/8 ≤ rowPeak hn g i)
    (haccuracy : ∀ i j, i≠j → g i j ≤ G i j ∧ G i j ≤ g i j+2*alpha) :
    (∀ i, (1:ℝ)/16 ≤ scalingTrace hn G n i) ∧
      BalancedRows hn (scaledHoleMatrix g (scalingTrace hn G n)) := by
  let v := scalingTrace hn G n
  have hv := (scalingTrace_invariant hn G hGsym hG n).1
  have hlow (i : Fin n) : (1:ℝ)/16 ≤ v i := by
    obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (g i)
    have hji := (mem_erase.mp hj).1
    change rowPeak hn g i=g i j at heq
    have hgij : (1:ℝ)/8 ≤ g i j := by rw [← heq]; exact hpre i
    have hGi := (haccuracy i j hji.symm).1
    have hfeas := hv.feasible i j hji.symm
    have hup := mul_le_mul_of_nonneg_left (hv.upper j) (hv.pos i).le
    dsimp [v]
    linarith
  refine ⟨hlow,?_⟩
  intro i
  constructor
  · obtain ⟨j,hji,heq⟩ := (one_pass_scaling hn G hGsym hG).2.2.2 i
    have hprod : (1:ℝ)/256 ≤ v i*v j := by
      calc
        (1:ℝ)/256 = ((1:ℝ)/16)*((1:ℝ)/16) := by norm_num
        _ ≤ v i*v j := mul_le_mul (hlow i) (hlow j) (by norm_num) (hv.pos i).le
    have hacc := (haccuracy i j hji.symm).2
    have hg : (1:ℝ)/4 ≤ scaledHoleMatrix g v i j := by
      apply (le_div_iff₀ (mul_pos (hv.pos i) (hv.pos j))).mpr
      change v i*v j=G i j at heq
      norm_num [alpha] at hacc
      nlinarith
    apply hg.trans
    exact Finset.le_sup' (scaledHoleMatrix g v i) (mem_erase.mpr ⟨hji,mem_univ _⟩)
  · apply Finset.sup'_le
    intro j hj
    have hji := (mem_erase.mp hj).1
    apply (div_le_one (mul_pos (hv.pos i) (hv.pos j))).mpr
    exact ((haccuracy i j hji.symm).1).trans (hv.feasible i j hji.symm)



def sigma (D K : ℕ) (epsilon : ℝ) : ℝ := min (alpha/(100*D)) (epsilon/(1000*K))

def ratioEstimate (abar dbar : ℝ) : ℝ := if 0<abar then dbar/abar else 1

def upperEstimate (D : ℕ) (dbar zbar : ℝ) : ℝ :=
  if 0<dbar then max alpha (min 3 ((D:ℝ)*zbar/dbar+alpha)) else 1



lemma sigma_nonneg (D K : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) : 0  ≤  sigma D K epsilon := by
  unfold sigma alpha; positivity

lemma sigma_small (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℝ) : sigma D K epsilon  ≤  (1:ℝ)/10000000 := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (by positivity : 0  <  (100:ℝ)*D)).mpr
  norm_num [alpha]
  linarith

lemma sigma_times_D (D K : ℕ) (hD : 1 ≤ D) (epsilon : ℝ) : (D:ℝ)*sigma D K epsilon  ≤  alpha/100 := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hs : sigma D K epsilon  ≤  alpha/(100*D) := min_le_left _ _
  have hm := (le_div_iff₀ (by positivity : 0  <  (100:ℝ)*D)).mp hs
  norm_num [alpha] at hm ⊢
  nlinarith only [hm]

lemma sigma_relative (D K : ℕ) (epsilon : ℝ) : 10*sigma D K epsilon  ≤  epsilon/(100*K) := by
  have h : sigma D K epsilon  ≤  epsilon/(1000*K) := min_le_right _ _
  calc
    _  ≤  10*(epsilon/(1000*K)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

lemma ratio_error (s a d abar dbar : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ (1:ℝ)/100)
    (ha : (1:ℝ)/2 ≤ a) (hR : (1:ℝ)/2 ≤ d/a  ∧  d/a ≤ 1)
    (haerr : |abar-a| ≤ s) (hderr : |dbar-d| ≤ s) :
    |ratioEstimate abar dbar/(d/a)-1|  ≤  10*s := by
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  have hap : 0 < a := by linarith
  have habp : 0 < abar := by linarith
  have hRp : 0 < d/a := by linarith [hR.1]
  have hden : (1:ℝ)/5  ≤  (d/a)*abar := by
    have hbar : (1:ℝ)/2-s  ≤  abar := by linarith
    have hm := mul_le_mul hR.1 hbar (by linarith : 0  ≤  (1:ℝ)/2-s) hRp.le
    nlinarith
  have hnum : |dbar-(d/a)*abar|  ≤  2*s := by
    have hid : dbar-(d/a)*abar=(dbar-d)+(d/a)*(a-abar) := by
      have hm : (d/a)*a=d := div_mul_cancel₀ d hap.ne'
      nlinarith
    rw [hid]
    calc
      _  ≤  |dbar-d|+|(d/a)*(a-abar)| := abs_add_le _ _
      _ = |dbar-d|+(d/a)*|abar-a| := by rw [abs_mul,abs_of_pos hRp,abs_sub_comm a abar]
      _  ≤  s+(d/a)*s := add_le_add hderr (mul_le_mul_of_nonneg_left haerr hRp.le)
      _  ≤  2*s := by nlinarith [mul_le_mul_of_nonneg_right hR.2 hs]
  have hid : ratioEstimate abar dbar/(d/a)-1=(dbar-(d/a)*abar)/((d/a)*abar) := by
    simp only [ratioEstimate, ite_eq_left habp]
    have hdne : d ≠ 0 := by intro hh; simp [hh] at hRp
    field_simp [hap.ne', habp.ne', hdne]
  rw [hid,abs_div,abs_of_pos (mul_pos hRp habp)]
  apply (div_le_iff₀ (mul_pos hRp habp)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hden (show 0 ≤ 10*s by positivity)]



lemma upper_error (D : ℕ) (hD : 1 ≤ D) (s d z dbar zbar : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ (1:ℝ)/100)
    (hDs : (D:ℝ)*s ≤ alpha/100) (hd : (1:ℝ)/4 ≤ d)
    (hg : 0 ≤ (D:ℝ)*z/d ∧ (D:ℝ)*z/d ≤ 2)
    (hderr : |dbar-d| ≤ s) (hzerr : |zbar-z| ≤ s) :
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℝ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℝ)*z/d+2*alpha := by
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hdp : 0 < d := by linarith
  have hdb := abs_le.mp hderr
  have hbar : (1:ℝ)/5 ≤ dbar := by linarith
  have hbarp : 0 < dbar := by linarith
  let g := (D:ℝ)*z/d
  have hg0 : 0 ≤ g := hg.1
  have hg2 : g ≤ 2 := hg.2
  have hnum : |(D:ℝ)*(zbar-z)+g*(d-dbar)| ≤ ((D:ℝ)+2)*s := by
    calc
      _ ≤ |(D:ℝ)*(zbar-z)|+|g*(d-dbar)| := abs_add_le _ _
      _ = (D:ℝ)*|zbar-z|+g*|dbar-d| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg D), abs_of_nonneg hg0,
          abs_sub_comm d dbar]
      _ ≤ (D:ℝ)*s+g*s := add_le_add (mul_le_mul_of_nonneg_left hzerr (Nat.cast_nonneg D))
        (mul_le_mul_of_nonneg_left hderr hg0)
      _ ≤ ((D:ℝ)+2)*s := by nlinarith [mul_le_mul_of_nonneg_right hg2 hs]
  have hid : (D:ℝ)*zbar/dbar-g=((D:ℝ)*(zbar-z)+g*(d-dbar))/dbar := by
    dsimp [g]
    field_simp [hdp.ne', hbarp.ne']
    ring
  have hraw : |(D:ℝ)*zbar/dbar-g| ≤ alpha := by
    rw [hid, abs_div, abs_of_pos hbarp]
    apply (div_le_iff₀ hbarp).mpr
    have hsm : s ≤ (D:ℝ)*s := by nlinarith [mul_le_mul_of_nonneg_right hDr hs]
    have ha : 0 < alpha := by norm_num [alpha]
    have hm := mul_le_mul_of_nonneg_left hbar ha.le
    norm_num [alpha] at hDs hm ⊢
    nlinarith only [hDs, hm, hnum, hsm]
  have hbounds := abs_le.mp hraw
  unfold upperEstimate
  rw [ite_eq_left hbarp]
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · apply max_le
    · norm_num [alpha]
    · exact min_le_left _ _
  · apply le_max_of_le_right
    exact le_min (by linarith) (by linarith)
  · apply max_le
    · have ha : 0 ≤ alpha := by norm_num [alpha]
      linarith
    · exact (min_le_right _ _).trans (by linarith)



theorem successful_stage_estimates (D K : ℕ) (hD : 1 ≤ D) (_hK : 1 ≤ K)
    (epsilon : ℝ) (he : 0<epsilon) (he1 : epsilon<1)
    (a d z abar dbar zbar : ℝ) (ha : (1:ℝ)/2 ≤ a) (hd : (1:ℝ)/4 ≤ d)
    (hR : (1:ℝ)/2 ≤ d/a ∧ d/a ≤ 1)
    (hg : 0 ≤ (D:ℝ)*z/d ∧ (D:ℝ)*z/d ≤ 2)
    (haerr : |abar-a| ≤ sigma D K epsilon)
    (hderr : |dbar-d| ≤ sigma D K epsilon)
    (hzerr : |zbar-z| ≤ sigma D K epsilon) :
    0<abar ∧ 0<dbar ∧
    |ratioEstimate abar dbar/(d/a)-1| ≤ 10*sigma D K epsilon ∧
    10*sigma D K epsilon ≤ epsilon/(100*K) ∧
    alpha ≤ upperEstimate D dbar zbar ∧ upperEstimate D dbar zbar ≤ 3 ∧
    (D:ℝ)*z/d ≤ upperEstimate D dbar zbar ∧
    upperEstimate D dbar zbar ≤ (D:ℝ)*z/d+2*alpha := by
  have hs := sigma_nonneg D K epsilon he.le
  have hs1 : sigma D K epsilon ≤ (1:ℝ)/100 :=
    (sigma_small D K hD epsilon).trans (by norm_num)
  have hab := abs_le.mp haerr
  have hdb := abs_le.mp hderr
  refine ⟨by linarith, by linarith, ?_, sigma_relative D K epsilon, ?_⟩
  · exact ratio_error _ _ _ _ _ hs hs1 ha hR haerr hderr
  · exact upper_error D hD _ _ _ _ _ hs hs1 (sigma_times_D D K hD epsilon) hd hg hderr hzerr

end MatchingFPRAS.RealStage

end

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

def pairEdge (i j : V) (hij : i≠j) : LogicalEdge V :=
  ⟨(min i j,max i j),min_lt_max.mpr hij⟩

omit [Fintype V] in
lemma pairEdge_swap (i j : V) (hij : i≠j) : pairEdge i j hij=pairEdge j i hij.symm := by
  apply Subtype.ext
  simp [pairEdge,min_comm,max_comm]

omit [Fintype V] in
lemma pairEdge_holes (i j : V) (hij : i≠j) :
    ({source (pairEdge i j hij),target (pairEdge i j hij)} : Finset V)={i,j} := by
  rcases le_total i j with h|h
  · simp [pairEdge,source,target,min_eq_left h,max_eq_right h]
  · simp [pairEdge,source,target,min_eq_right h,max_eq_left h,Finset.pair_comm]

noncomputable def probeMatrix (z : LogicalEdge V → ℝ) (i j : V) : ℝ :=
  if hij : i=j then 0 else z (pairEdge i j hij)

omit [Fintype V] in
lemma probeMatrix_off (z : LogicalEdge V → ℝ) (i j : V) (hij : i≠j) :
    probeMatrix z i j=z (pairEdge i j hij) := dite_eq_right hij

omit [Fintype V] in
lemma probeMatrix_symm (z : LogicalEdge V → ℝ) (i j : V) : probeMatrix z i j=probeMatrix z j i := by
  by_cases hij : i=j
  · subst j; rfl
  · rw [probeMatrix_off _ _ _ hij,probeMatrix_off _ _ _ (Ne.symm hij),pairEdge_swap]

noncomputable def estimateMatrix (D : ℕ) (dbar : ℝ) (zbar : LogicalEdge V → ℝ) (i j : V) : ℝ :=
  RealStage.upperEstimate D dbar (probeMatrix zbar i j)

omit [Fintype V] in
lemma estimateMatrix_symm (D : ℕ) (dbar : ℝ) (zbar : LogicalEdge V → ℝ) (i j : V) :
    estimateMatrix D dbar zbar i j=estimateMatrix D dbar zbar j i := by
  rw [estimateMatrix,estimateMatrix,probeMatrix_symm]

lemma rowMax_cooling_lower (hn : 2 ≤ Fintype.card V) (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 ≤ w x y) (hz : 0 < partition w ∅)
    (hr : ∀ i,(1:ℝ)/4 ≤ rowMax hn w i)
    (hc : ∀ R,partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R) (i : V) :
    (1:ℝ)/8 ≤ rowMax hn w₁ i := by
  obtain ⟨j,hji,hj⟩ := rowMax_attained hn w i
  have h := (holeRatio_cooling w w₁ hw hz hc {i,j}).1
  have hu := holeRatio_le_rowMax hn w₁ i j hji.symm
  rw [hj] at h
  linarith [hr i]

variable [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def meanA (w : V → V → ℝ) (K : ℕ) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableA w K q

noncomputable def meanD (w w₁ : V → V → ℝ) (K : ℕ) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableD w w₁ K q

noncomputable def meanProbe (w w₁ : V → V → ℝ) (K : ℕ) (e : LogicalEdge (V)) : ℝ :=
  ∑ q : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) q*observableProbe w w₁ K e q

variable {n : ℕ} [Nontrivial (Fin n)]

noncomputable local instance (w : Fin n → Fin n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : Fin n → Fin n → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

omit [Nontrivial (Fin n)] in
lemma rowPeak_holeMatrix (hn : 2 ≤ n) (w : Fin n → Fin n → ℝ) (i : Fin n) :
    RealStage.rowPeak hn (fun i j => Switching.holeRatio w {i,j}) i=
      rowMax (by simpa using hn) w i := rfl

structure StageData (n K T : ℕ) where
  hn : 2 ≤ n
  w : Fin n → Fin n → ℝ
  next : Fin n → Fin n → ℝ
  positive : ∀ i j,0 < w i j
  next_positive : ∀ i j,0 < next i j
  partition_positive : 0 < partition w ∅
  lower : ∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using hn) w i
  upper : ∀ i,rowMax (by simpa using hn) w i ≤ 1
  cool_lower : ∀ i j,i≠j → (1+1/(n:ℝ))⁻¹*w i j ≤ next i j
  cool_upper : ∀ i j,i≠j → next i j ≤ w i j
  cap : ∀ i j,i≠j → edgeActivity w i j ≤ (4:ℝ)^K
  stages : 1 ≤ T
  epsilon : ℝ
  epsilon_positive : 0 < epsilon
  epsilon_lt_one : epsilon < 1

variable {K T : ℕ}

structure EmpiricalData (c : StageData n K T) where
  abar : ℝ
  dbar : ℝ
  zbar : LogicalEdge (Fin n) → ℝ
  errorA : |abar-meanA c.w K| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon
  errorD : |dbar-meanD c.w c.next K| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon
  errorProbe : ∀ e,|zbar e-meanProbe c.w c.next K e| ≤ RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon

omit [Nontrivial (Fin n)] in
lemma StageData.cooling (c : StageData n K T) (R : Finset (Fin n)) :
    partition c.w R/2 ≤ partition c.next R ∧ partition c.next R ≤ partition c.w R := by
  apply partition_cooling (by simpa using c.hn) c.w c.next (fun i j => (c.positive i j).le)
  · simpa using c.cool_lower
  · exact c.cool_upper

lemma StageData.mean_bounds (c : StageData n K T) :
    (1:ℝ)/2 ≤ meanA c.w K ∧ (1:ℝ)/4 ≤ meanD c.w c.next K ∧
    meanD c.w c.next K/meanA c.w K=partition c.next ∅/partition c.w ∅ ∧
    (1:ℝ)/2 ≤ meanD c.w c.next K/meanA c.w K ∧ meanD c.w c.next K/meanA c.w K ≤ 1 ∧
    (∀ e,(sourceD (V:=Fin n) K:ℝ)*meanProbe c.w c.next K e/meanD c.w c.next K=
      Switching.holeRatio c.next {source e,target e}) := by
  have h := source_observable_means (V:=Fin n) (by simpa using c.hn) c.w c.next c.positive c.partition_positive
    c.lower c.upper (by simpa using c.cool_lower) c.cool_upper K c.cap
  unfold meanA meanD meanProbe
  exact h.2.2

omit [Nontrivial (Fin n)] in
lemma StageData.hole_upper (c : StageData n K T) (i j : Fin n) (hij : i≠j) :
    Switching.holeRatio c.next {i,j} ≤ 2 := by
  have h := (holeRatio_cooling c.w c.next (fun i j => (c.positive i j).le)
    c.partition_positive c.cooling {i,j}).2
  have hr := (holeRatio_le_rowMax (by simpa using c.hn) c.w i j hij).trans (c.upper i)
  linarith

theorem actual_stage_statistics (c : StageData n K T) (b : EmpiricalData c) (i j : Fin n) (hij : i≠j) :
    let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
    0 < b.abar ∧ 0 < b.dbar ∧
    |RealStage.ratioEstimate b.abar b.dbar/(partition c.next ∅/partition c.w ∅)-1| ≤ c.epsilon/(100*T) ∧
    RealStage.alpha ≤ G i j ∧ G i j ≤ 3 ∧
    Switching.holeRatio c.next {i,j} ≤ G i j ∧
    G i j ≤ Switching.holeRatio c.next {i,j}+2*RealStage.alpha := by
  dsimp only
  have hm := c.mean_bounds
  have hem := hm.2.2.2.2.2 (pairEdge i j hij)
  rw [pairEdge_holes] at hem
  have hg0 := holeRatio_nonneg c.next (fun x y => (c.next_positive x y).le) {i,j}
  have h := RealStage.successful_stage_estimates (sourceD (V:=Fin n) K) T (sourceD_one K)
    c.stages c.epsilon c.epsilon_positive c.epsilon_lt_one
    (meanA c.w K) (meanD c.w c.next K) (meanProbe c.w c.next K (pairEdge i j hij))
    b.abar b.dbar (b.zbar (pairEdge i j hij)) hm.1 hm.2.1
    ⟨hm.2.2.2.1,hm.2.2.2.2.1⟩
    ⟨by rw [hem]; exact hg0,by rw [hem]; exact c.hole_upper i j hij⟩
    b.errorA b.errorD (b.errorProbe _)
  refine ⟨h.1,h.2.1,?_,?_⟩
  · have he := h.2.2.1.trans h.2.2.2.1
    rwa [hm.2.2.1] at he
  · simpa only [estimateMatrix,probeMatrix_off _ _ _ hij,hem] using h.2.2.2.2

theorem actual_successful_stage (c : StageData n K T) (b : EmpiricalData c) :
    let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
    let v := RealStage.scalingTrace c.hn G n
    (∀ i,(1:ℝ)/16 ≤ v i ∧ v i ≤ 2) ∧
    (∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ∧
      rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ≤ 1) ∧
    |RealStage.ratioEstimate b.abar b.dbar/(partition c.next ∅/partition c.w ∅)-1| ≤ c.epsilon/(100*T) := by
  dsimp only
  let G := estimateMatrix (sourceD (V:=Fin n) K) b.dbar b.zbar
  let g := fun i j => Switching.holeRatio c.next {i,j}
  have hest := actual_stage_statistics c b
  have hGs := estimateMatrix_symm (sourceD (V:=Fin n) K) b.dbar b.zbar
  have hGb : ∀ i j,i≠j → RealStage.alpha ≤ G i j ∧ G i j ≤ 3 := by
    intro i j hij
    exact ⟨(hest i j hij).2.2.2.1,(hest i j hij).2.2.2.2.1⟩
  have hGa : ∀ i j,i≠j → g i j ≤ G i j ∧ G i j ≤ g i j+2*RealStage.alpha := by
    intro i j hij
    exact (hest i j hij).2.2.2.2.2
  have hpre : ∀ i,(1:ℝ)/8 ≤ RealStage.rowPeak c.hn g i := by
    intro i
    rw [show g=(fun i j => Switching.holeRatio c.next {i,j}) from rfl,rowPeak_holeMatrix]
    exact rowMax_cooling_lower (by simpa using c.hn) c.w c.next (fun x y => (c.positive x y).le)
      c.partition_positive c.lower c.cooling i
  have hb := RealStage.one_pass_restores_balance c.hn g G hGs hGb hpre hGa
  let v := RealStage.scalingTrace c.hn G n
  have hv := (RealStage.scalingTrace_invariant c.hn G hGs hGb n).1
  have heq (i j : Fin n) (hij : i≠j) :
      Switching.holeRatio (fun x y => c.next x y*v x*v y) {i,j}=RealStage.scaledHoleMatrix g v i j := by
    rw [holeRatio_vertex_scaling c.next v (fun x => hv.pos x),Finset.prod_pair hij]
    rfl
  have hb' (i : Fin n) : (1:ℝ)/4 ≤ rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ∧
      rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i ≤ 1 := by
    have he : rowMax (by simpa using c.hn) (fun x y => c.next x y*v x*v y) i=
        RealStage.rowPeak c.hn (RealStage.scaledHoleMatrix g v) i := by
      unfold rowMax RealStage.rowPeak
      apply Finset.sup'_congr _ rfl
      intro j hj
      exact heq i j (Finset.mem_erase.mp hj).1.symm
    rw [he]
    exact hb.2 i
  refine ⟨fun i => ⟨hb.1 i,hv.upper i⟩,hb',?_⟩
  let i : Fin n := ⟨0,by have := c.hn; omega⟩
  let j : Fin n := ⟨1,by have := c.hn; omega⟩
  have hij : i≠j := by intro h; have := Fin.val_eq_of_eq h; dsimp [i,j] at this; omega
  exact (hest i j hij).2.2.1

end MatchingFPRAS.Enlargement

end OAI
