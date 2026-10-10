import Mathlib
import OAI.Probability.JammingConcavity.RowRefinementCovariance

namespace OAI

/-! Spherical Grid Density. -/

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
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma gridStep_error_cell (p : SphericalProfile) (n k : ℕ) (hk : k ≤ n)
    (s : ℝ) (hs : s ∈ Set.Ioo (spinGridPoint n k) (spinGridPoint n (k+1))) :
    |p.val s-(p.gridStep n).val s| ≤ p.val (spinGridPoint n (k+1))-p.val (spinGridPoint n k) := by
  have hl := spinGridPoint_mem n k (by omega)
  have hr := spinGridPoint_mem n (k+1) (by omega)
  have hsm : s ∈ Set.Icc 0 1 := ⟨hl.1.trans hs.1.le,hs.2.le.trans hr.2⟩
  rw [gridStep_val_cell p n k hk s hs,abs_of_nonneg (sub_nonneg.mpr (p.mono hl hsm hs.1.le))]
  exact sub_le_sub_right (p.mono hsm hr hs.2.le) _

lemma gridStep_distance_bound (p : SphericalProfile) (n : ℕ) :
    sphericalProfileDistance p.val (p.gridStep n).val ≤ (p.val 1-p.val 0)/((n:ℝ)+1) := by
  let g := fun s => |p.val s-(p.gridStep n).val s|
  have hg : IntervalIntegrable g volume 0 1 := (p.integrable.sub (p.gridStep n).integrable).abs
  have hint : ∀ k < n+1, IntervalIntegrable g volume (spinGridPoint n k) (spinGridPoint n (k+1)) := by
    intro k hk
    apply hg.mono_set
    rw [Set.uIcc_of_le (spinGridPoint_mono n (by omega)),Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro s hs
    exact ⟨(spinGridPoint_mem n k (by omega)).1.trans hs.1,
      hs.2.trans (spinGridPoint_mem n (k+1) (by omega)).2⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [spinGridPoint_zero,spinGridPoint_last] at hsum
  change (∫ s in (0:ℝ)..1, g s) ≤ _
  rw [←hsum]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1),
        (1/((n:ℝ)+1))*(p.val (spinGridPoint n (k+1))-p.val (spinGridPoint n k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Finset.mem_range.mp hk
      have H := intervalIntegral.integral_mono_on_of_le_Ioo
        (spinGridPoint_mono n (by omega)) (hint k hkn)
        (intervalIntegrable_const (c := p.val (spinGridPoint n (k+1))-p.val (spinGridPoint n k)))
        (gridStep_error_cell p n k (by omega))
      rw [intervalIntegral.integral_const, smul_eq_mul] at H
      have he : spinGridPoint n (k+1)-spinGridPoint n k = 1/((n:ℝ)+1) := by
        simp only [spinGridPoint,Nat.cast_add,Nat.cast_one]; ring
      rwa [he] at H
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_range_sub (fun j => p.val (spinGridPoint n j)) (n+1),spinGridPoint_last,spinGridPoint_zero]
      ring

lemma gridStep_distance_le (p : SphericalProfile) (B : ℝ)
    (hp : p ∈ boundedSphericalProfiles B) (n : ℕ) :
    sphericalProfileDistance p.val (p.gridStep n).val ≤ B/((n:ℝ)+1) := by
  apply (gridStep_distance_bound p n).trans
  apply div_le_div_of_nonneg_right _ (spinGridPoint_pos_denom n).le
  have hp1 := hp 1 (by norm_num)
  have hp0 := p.nonneg 0 (by norm_num)
  linarith

lemma exists_spinGrid_precision (B ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, B/((n:ℝ)+1) < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B/ε)
  refine ⟨n,(div_lt_iff₀ (spinGridPoint_pos_denom n)).2 ?_⟩
  have hh := (div_lt_iff₀ hε).1 hn
  nlinarith

end MicroscopicJamming

namespace MicroscopicJamming
lemma rowGrid_distance_sample (p q : SphericalProfile) (n : ℕ) :
    sphericalProfileDistance (p.gridStep n).val (q.gridStep n).val =
      ∑ k ∈ Finset.range (n+1), (1/((n:ℝ)+1))*
        |p.val (spinGridPoint n k)-q.val (spinGridPoint n k)| := by
  let g := fun s => |(p.gridStep n).val s-(q.gridStep n).val s|
  have hg : IntervalIntegrable g volume 0 1 := ((p.gridStep n).integrable.sub (q.gridStep n).integrable).abs
  have hint : ∀ k < n+1, IntervalIntegrable g volume (spinGridPoint n k) (spinGridPoint n (k+1)) := by
    intro k hk
    apply hg.mono_set
    rw [Set.uIcc_of_le (spinGridPoint_mono n (by omega)),Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro s hs
    exact ⟨(spinGridPoint_mem n k (by omega)).1.trans hs.1,
      hs.2.trans (spinGridPoint_mem n (k+1) (by omega)).2⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [spinGridPoint_zero,spinGridPoint_last] at hsum
  change (∫ s in (0:ℝ)..1, g s) = _
  rw [←hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hle := spinGridPoint_mono n (show k ≤ k+1 by omega)
  calc
    _ = ∫ _ in (spinGridPoint n k)..(spinGridPoint n (k+1)),
        |p.val (spinGridPoint n k)-q.val (spinGridPoint n k)| := by
      rw [intervalIntegral.integral_of_le hle,intervalIntegral.integral_of_le hle,
        integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp [g]
      rw [gridStep_val_cell p n k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) s hs,
        gridStep_val_cell q n k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) s hs]
    _ = _ := by
      rw [intervalIntegral.integral_const,smul_eq_mul]
      congr 1
      simp only [spinGridPoint,Nat.cast_add,Nat.cast_one]
      ring

lemma gridStep_distance_tendsto_pointwise {ι : Type*} {l : Filter ι}
    (pn : ι → SphericalProfile) (p : SphericalProfile)
    (h : ∀ s ∈ Set.Icc 0 1, Tendsto (fun i => (pn i).val s) l (𝓝 (p.val s))) (n : ℕ) :
    Tendsto (fun i => sphericalProfileDistance ((pn i).gridStep n).val (p.gridStep n).val) l (𝓝 0) := by
  simp_rw [rowGrid_distance_sample]
  have hh : Tendsto (fun i => ∑ k ∈ Finset.range (n+1), (1/((n:ℝ)+1))*
      |(pn i).val (spinGridPoint n k)-p.val (spinGridPoint n k)|) l
      (𝓝 (∑ k ∈ Finset.range (n+1), (0:ℝ))) := by
    apply tendsto_finsetSum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have hc := h (spinGridPoint n k) (spinGridPoint_mem n k (by omega))
    simpa using (((hc.sub (tendsto_const_nhds (x := p.val (spinGridPoint n k)))).abs).const_mul (1/((n:ℝ)+1)))
  simpa using hh
end MicroscopicJamming

namespace MicroscopicJamming
 

lemma profileDistance_tendsto_pointwise {ι : Type*} {l : Filter ι}
    (pn : ι → SphericalProfile) (p : SphericalProfile) (B : ℝ)
    (hpn : ∀ i s, s ∈ Set.Icc 0 1 → (pn i).val s ≤ B)
    (hp : ∀ s ∈ Set.Icc 0 1, p.val s ≤ B)
    (h : ∀ s ∈ Set.Icc 0 1, Tendsto (fun i => (pn i).val s) l (𝓝 (p.val s))) :
    Tendsto (fun i => sphericalProfileDistance (pn i).val p.val) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n,hn⟩ := exists_spinGrid_precision B (ε/3) (by positivity)
  have hg := gridStep_distance_tendsto_pointwise pn p h n
  have heb := (tendsto_order.mp hg).2 (ε/3) (by positivity)
  filter_upwards [heb] with i hi
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (sphericalProfileDistance_nonneg (pn i) p)]
  have h1 := gridStep_distance_le (pn i) B (hpn i) n
  have h2 := gridStep_distance_le p B hp n
  have h3 := sphericalProfileDistance_triangle (pn i) ((pn i).gridStep n).toProfile p
  have h4 := sphericalProfileDistance_triangle ((pn i).gridStep n).toProfile (p.gridStep n).toProfile p
  rw [sphericalProfileDistance_comm (p.gridStep n).toProfile p] at h4
  change sphericalProfileDistance (pn i).val p.val ≤ sphericalProfileDistance (pn i).val ((pn i).gridStep n).val + sphericalProfileDistance ((pn i).gridStep n).val p.val at h3
  change sphericalProfileDistance ((pn i).gridStep n).val p.val ≤ sphericalProfileDistance ((pn i).gridStep n).val (p.gridStep n).val + sphericalProfileDistance p.val (p.gridStep n).val at h4
  linarith
end MicroscopicJamming

 
open MeasureTheory Filter Set
open scoped BigOperators NNReal Topology

namespace MicroscopicJamming
 

lemma profileCompactFilter (pn : ℕ → SphericalProfile) (B : ℝ)
    (hpn : ∀ n s, s ∈ Set.Icc 0 1 → (pn n).val s ≤ B) :
    ∃ (p : SphericalProfile) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      (∀ s ∈ Set.Icc 0 1, p.val s ≤ B) ∧
      Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) l (𝓝 0) := by
  let c : ℝ → ℝ := fun s => max 0 (min s 1)
  have hc (s : ℝ) : c s ∈ Set.Icc 0 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩
  have hce (s : ℝ) (hs : s ∈ Set.Icc 0 1) : c s = s := by
    simp only [c,min_eq_left hs.2,max_eq_right hs.1]
  let seq : ℕ → (ℝ → Set.Icc (0:ℝ) B) := fun n s => ⟨(pn n).val (c s),
    (pn n).nonneg (c s) (hc s),hpn n (c s) (hc s)⟩
  let U := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨f,hf⟩ := exists_clusterPt_of_compactSpace (U.map seq : Filter (ℝ → Set.Icc (0:ℝ) B))
  have hf' : Tendsto seq (U : Filter ℕ) (𝓝 f) := (Ultrafilter.clusterPt_iff).mp hf
  have hfpoint (s : ℝ) : Tendsto (fun n => (pn n).val (c s)) (U : Filter ℕ) (𝓝 (f s:ℝ)) :=
    (continuous_subtype_val.tendsto (f s)).comp (((continuous_apply s).tendsto f).comp hf')
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
      Tendsto (fun n => (pn n).val s) (U : Filter ℕ) (𝓝 (f s:ℝ)) := by
    simpa only [hce s hs] using hfpoint s
  let p : SphericalProfile :=
    { val := fun s => (f s:ℝ)
      nonneg := fun s _ => (f s).property.1
      mono := fun s hs t ht hst => le_of_tendsto_of_tendsto (hpoint s hs) (hpoint t ht)
        (Eventually.of_forall fun n => (pn n).mono hs ht hst) }
  have hp : ∀ s ∈ Set.Icc 0 1, p.val s ≤ B := fun s _ => (f s).property.2
  exact ⟨p,(U:Filter ℕ),inferInstance,Ultrafilter.of_le atTop,hp,
    profileDistance_tendsto_pointwise pn p B hpn hp hpoint⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators MatrixOrder

namespace MicroscopicJamming
 

structure RowFiniteProfile (Q : ℝ) where
  ranks : List ℝ
  ordered : ranks.Pairwise (· < ·)
  valid : ∀ m ∈ ranks, 0 < m ∧ m < 1
  increment : ℕ → ℝ≥0
  root : ℝ≥0
  residual : ℝ≥0
  diagonal : rowReplicaDiagonal ranks.length increment root residual = Q

def RowFiniteProfile.profile {Q : ℝ} (P : RowFiniteProfile Q) : SphericalProfile :=
  rowCascadeProfile P.ranks P.increment P.root

 

def RowFiniteProfile.derivative {Q : ℝ} (P : RowFiniteProfile Q) (u : ℝ → ℝ)
    (s : ℝ) : ℝ :=
  ∫ x, rowDerivativeDepthMoment (rowGaussianBlocks P.ranks P.increment)
    (gaussianRowOperator 1 P.residual u) (rpcStepLevel P.ranks s) x
    ∂gaussianReal 0 P.root

 

def RowProfileTestConvergenceStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ (Q : ℝ) (P : ℕ → RowFiniteProfile Q) (q : SphericalProfile), q.val 1 ≤ Q →
    Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0) →
  ∀ φ : C(Set.Icc (0:ℝ) 1,ℝ), ∃ b : ℝ,
    Tendsto (fun n => ∫ s in (0:ℝ)..1, rowTestExtend φ s * (P n).derivative u s)
      atTop (𝓝 b)

def RowDerivativeLimitStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ (Q : ℝ) (P : ℕ → RowFiniteProfile Q) (q : SphericalProfile), q.val 1 ≤ Q →
    Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0) →
  ∃ D : SphericalProfile, (∀ s ∈ Set.Icc 0 1, D.val s ≤ L^2) ∧
    Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) D.val) atTop (𝓝 0)
end MicroscopicJamming

 
open scoped NNReal ENNReal BigOperators Topology
 

namespace MicroscopicJamming
def rowRankSelect (as : List ℝ) (M : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  match as with
  | [] => fun j _ => M j
  | a::as => fun j s => if s<a then M j else rowRankSelect as M (j+1) s

 

def rowDerivativeRankMoment (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (s x : ℝ) : ℝ :=
  rowRankSelect (rs.map Prod.fst) (fun j => rowDerivativeDepthMoment rs u j x) 0 s

end MicroscopicJamming

 
 

namespace MicroscopicJamming

def RowZeroRefinementStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ (pre post : List (ℝ × ℝ)) (a : ℝ),
    (∀ r ∈ pre ++ [(a,0)] ++ post, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    (pre ++ [(a,0)] ++ post).Pairwise (fun r s : ℝ × ℝ => r.1 ≤ s.1) →
    gaussianRowComposition (pre ++ [(a,0)] ++ post) u =
      gaussianRowComposition (pre ++ post) u ∧
    ∀ s x : ℝ, rowDerivativeRankMoment (pre ++ [(a,0)] ++ post) u s x =
      rowDerivativeRankMoment (pre ++ post) u s x
end MicroscopicJamming

 

namespace MicroscopicJamming
 

def RowZeroRefinementClosureStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ rs ss : List (ℝ × ℝ),
    (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    (∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    rs.Pairwise (fun r s => r.1 ≤ s.1) → ss.Pairwise (fun r s => r.1 ≤ s.1) →
    rs.filter (fun r => r.2 != 0) = ss.filter (fun r => r.2 != 0) →
    gaussianRowComposition rs u = gaussianRowComposition ss u ∧
      ∀ s x, rowDerivativeRankMoment rs u s x = rowDerivativeRankMoment ss u s x
end MicroscopicJamming
namespace MicroscopicJamming
end MicroscopicJamming
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

def rowRankIndex : List ℝ → ℝ → ℕ
  | [], _ => 0
  | a::as,s => if s<a then 0 else rowRankIndex as s+1

lemma rowRankSelect_index (as : List ℝ) (M : ℕ → ℝ) (j : ℕ) (s : ℝ) :
    rowRankSelect as M j s = M (j+rowRankIndex as s) := by
  induction as generalizing j with
  | nil => simp [rowRankSelect,rowRankIndex]
  | cons a as ih =>
    simp only [rowRankSelect,rowRankIndex]
    split_ifs with hs
    · simp
    · rw [ih]
      congr 1
      omega

lemma rowDerivativeRankMoment_index (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (s x : ℝ) :
    rowDerivativeRankMoment rs u s x =
      rowDerivativeDepthMoment rs u (rowRankIndex (rs.map Prod.fst) s) x := by
  unfold rowDerivativeRankMoment
  rw [rowRankSelect_index]
  simp only [Nat.zero_add]

lemma rowDerivativeRankMoment_cons (r : ℝ × ℝ) (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) (s x : ℝ) :
    rowDerivativeRankMoment (r::rs) u s x =
      if s<r.1 then (deriv (gaussianRowComposition (r::rs) u) x)^2
      else rowTiltStep r.1 r.2 (gaussianRowComposition rs u) x
        (fun y => rowDerivativeRankMoment rs u s y) := by
  simp only [rowDerivativeRankMoment_index,List.map_cons,rowRankIndex]
  split_ifs with hs
  · rfl
  · rfl

lemma rowGaussianComposition_insert_zero (pre post : List (ℝ × ℝ)) (a : ℝ) (u : ℝ → ℝ) :
    gaussianRowComposition (pre ++ (a,0)::post) u = gaussianRowComposition (pre ++ post) u := by
  induction pre with
  | nil =>
    simp only [List.nil_append,gaussianRowComposition]
    exact funext (gaussianRowOperator_zero a _)
  | cons r pre ih => simp only [List.cons_append,gaussianRowComposition,ih]

lemma rowDerivativeRankMoment_below (post : List (ℝ × ℝ)) (u : ℝ → ℝ) (s x : ℝ)
    (hs : ∀ r ∈ post, s<r.1) :
    rowDerivativeRankMoment post u s x = (deriv (gaussianRowComposition post u) x)^2 := by
  cases post with
  | nil => rfl
  | cons r rs => rw [rowDerivativeRankMoment_cons,ite_eq_left (hs r (by simp))]

lemma rowDerivativeRankMoment_insert_zero (pre post : List (ℝ × ℝ)) (a : ℝ) (u : ℝ → ℝ)
    (ha : ∀ r ∈ post, a ≤ r.1) : ∀ s x,
    rowDerivativeRankMoment (pre ++ (a,0)::post) u s x =
      rowDerivativeRankMoment (pre ++ post) u s x := by
  induction pre with
  | nil =>
    intro s x
    simp only [List.nil_append]
    rw [rowDerivativeRankMoment_cons]
    have hc := rowGaussianComposition_insert_zero [] post a u
    simp only [List.nil_append] at hc
    rw [hc]
    split_ifs with hs
    · exact (rowDerivativeRankMoment_below post u s x
        (fun r hr => hs.trans_le (ha r hr))).symm
    · exact rowTiltStep_zero a _ _ x
  | cons r pre ih =>
    intro s x
    simp only [List.cons_append,rowDerivativeRankMoment_cons]
    have hc := rowGaussianComposition_insert_zero (r::pre) post a u
    simp only [List.cons_append] at hc
    rw [hc, rowGaussianComposition_insert_zero pre post a u]
    simp only [funext (ih s)]

theorem rowZeroRefinement : RowZeroRefinementStatement := by
  intro u L H hu hL hH huB pre post a hpos hsort
  have ha : ∀ r ∈ post, a ≤ r.1 := by
    rw [List.append_assoc] at hsort
    have ht := (List.pairwise_append.mp hsort).2.1
    have hc : ((a,0)::post).Pairwise (fun r s : ℝ × ℝ => r.1 ≤ s.1) := by
      simpa only [List.singleton_append] using ht
    exact (List.pairwise_cons.mp hc).1
  simpa only [List.append_assoc,List.singleton_append] using
    And.intro (rowGaussianComposition_insert_zero pre post a u)
      (rowDerivativeRankMoment_insert_zero pre post a u ha)
end MicroscopicJamming

 

namespace MicroscopicJamming
lemma rowComposition_filter_zero (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) :
    gaussianRowComposition rs u = gaussianRowComposition (rs.filter (fun r => r.2 != 0)) u := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hz : r.2=0
    · simp only [List.filter_cons,hz,bne_self_eq_false,Bool.false_eq_true,ite_false]
      rw [show r=(r.1,0) from Prod.ext rfl hz]
      change gaussianRowOperator r.1 0 (gaussianRowComposition rs u) = _
      rw [funext (gaussianRowOperator_zero r.1 _),ih]
    · simp only [List.filter_cons, ne_eq, bne_iff_ne, hz, not_false_eq_true, ite_true,
        gaussianRowComposition, ih]

lemma rowRankDerivative_filter_zero (rs : List (ℝ × ℝ)) (u : ℝ → ℝ)
    (hord : rs.Pairwise (fun r s => r.1 ≤ s.1)) :
    ∀ s x, rowDerivativeRankMoment rs u s x =
      rowDerivativeRankMoment (rs.filter (fun r => r.2 != 0)) u s x := by
  induction rs with
  | nil => intros; rfl
  | cons r rs ih =>
    have htail := (List.pairwise_cons.mp hord).2
    have hhead := (List.pairwise_cons.mp hord).1
    intro s x
    by_cases hz : r.2=0
    · have he := rowDerivativeRankMoment_insert_zero [] rs r.1 u hhead s x
      rw [show r=(r.1,0) from Prod.ext rfl hz]
      simpa only [List.nil_append,List.filter_cons,Prod.snd,bne_self_eq_false,
        Bool.false_eq_true,ite_false] using he.trans (ih htail s x)
    · simp only [List.filter_cons,bne_iff_ne,ite_eq_left hz]
      rw [rowDerivativeRankMoment_cons,rowDerivativeRankMoment_cons]
      split_ifs with hs
      · rw [rowComposition_filter_zero (r::rs) u]
        simp only [List.filter_cons,bne_iff_ne,ite_eq_left hz]
      · rw [rowComposition_filter_zero rs u]
        congr 1
        exact funext (ih htail s)

theorem rowZeroRefinementClosure : RowZeroRefinementClosureStatement := by
  intro u L H hu hL hH hb rs ss hrs hss hordr hords he
  constructor
  · rw [rowComposition_filter_zero rs u,rowComposition_filter_zero ss u,he]
  · intro s x
    rw [rowRankDerivative_filter_zero rs u hordr,rowRankDerivative_filter_zero ss u hords,he]
end MicroscopicJamming

namespace MicroscopicJamming
lemma rowGaussianBlocks_ranks (ms : List ℝ) (d : ℕ → ℝ≥0) :
    (rowGaussianBlocks ms d).map Prod.fst = ms := by
  induction ms generalizing d with
  | nil => rfl
  | cons m ms ih => simp [rowGaussianBlocks,ih]

lemma rowGaussianBlocks_mem (ms : List ℝ) (d : ℕ → ℝ≥0) (r : ℝ × ℝ)
    (hr : r ∈ rowGaussianBlocks ms d) : r.1 ∈ ms ∧ 0 ≤ r.2 := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks] at hr
  | cons m ms ih =>
    simp only [rowGaussianBlocks,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨by simp,(d 0).coe_nonneg⟩
    · obtain ⟨hm,hd⟩ := ih _ hr
      exact ⟨by simp [hm],hd⟩

lemma rowRootResidual_valid (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    ∀ r ∈ (0,(p₀:ℝ))::(rowGaussianBlocks ms d ++ [(1,(Δ:ℝ))]),
      0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := by
  intro r hr
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ⟨le_rfl,zero_le_one,p₀.coe_nonneg⟩
  · obtain ⟨hrm,hdr⟩ := rowGaussianBlocks_mem ms d r hr
    exact ⟨(hm r.1 hrm).1.le,(hm r.1 hrm).2.le,hdr⟩
  · exact ⟨zero_le_one,le_rfl,Δ.coe_nonneg⟩

lemma rowRootResidual_sorted (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (hms : ms.Pairwise (· < ·)) (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    ((0,(p₀:ℝ))::(rowGaussianBlocks ms d ++ [(1,(Δ:ℝ))])).Pairwise
      (fun r s => r.1 ≤ s.1) := by
  have hp : (rowGaussianBlocks ms d).Pairwise (fun r s => r.1 ≤ s.1) := by
    apply List.pairwise_map.mp
    rw [rowGaussianBlocks_ranks]
    exact hms.imp (fun h => h.le)
  apply List.pairwise_cons.mpr
  refine ⟨?_,List.pairwise_append.mpr ⟨hp,by simp,?_⟩⟩
  · intro r hr
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact (hm r.1 (rowGaussianBlocks_mem ms d r hr).1).1.le
    · exact zero_le_one
  · intro r hr s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact (hm r.1 (rowGaussianBlocks_mem ms d r hr).1).2.le
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowRankIndex_eq_rpcStepLevel (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (s : ℝ) :
    rowRankIndex ms s = rpcStepLevel ms s := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    obtain ⟨hm,hms⟩ := List.pairwise_cons.mp hms
    by_cases hs : s < m
    · have hz : ms.filter (fun a => decide (a ≤ s)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        simp only [Bool.not_eq_true,decide_eq_false_iff_not]
        exact not_le.mpr (hs.trans (hm a ha))
      simp [rowRankIndex,rpcStepLevel,hs,not_le.mpr hs,hz]
    · simp [rowRankIndex,rpcStepLevel,hs,le_of_not_gt hs,ih hms]

lemma rowRankMoment_blocks (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (d : ℕ → ℝ≥0) (v : ℝ → ℝ) (s x : ℝ) :
    rowDerivativeRankMoment (rowGaussianBlocks ms d) v s x =
      rowDerivativeDepthMoment (rowGaussianBlocks ms d) v (rpcStepLevel ms s) x := by
  rw [rowDerivativeRankMoment_index,rowGaussianBlocks_ranks,rowRankIndex_eq_rpcStepLevel ms hms]

lemma rowMesh_depth_invariant (ms ts : List ℝ) (hms : ms.Pairwise (· < ·))
    (d : ℕ → ℝ≥0) (v : ℝ → ℝ) (s x : ℝ) :
    rowDerivativeDepthMoment (rowGaussianBlocks (rowMeshRanks ms ts) (rowMeshIncrement ms ts d))
      v (rpcStepLevel (rowMeshRanks ms ts) s) x =
    rowDerivativeDepthMoment (rowGaussianBlocks ms d) v (rpcStepLevel ms s) x := by
  rw [←rowRankMoment_blocks _ (rowMeshRanks_sorted _ _),←rowRankMoment_blocks _ hms]
  have hord (ms : List ℝ) (hm : ms.Pairwise (· < ·)) (d : ℕ → ℝ≥0) :
      (rowGaussianBlocks ms d).Pairwise (fun r t => r.1 ≤ t.1) := by
    apply List.pairwise_map.mp
    rw [rowGaussianBlocks_ranks]
    exact hm.imp (fun h => h.le)
  rw [rowRankDerivative_filter_zero _ v (hord _ (rowMeshRanks_sorted _ _) _),
    rowRankDerivative_filter_zero _ v (hord _ hms _),rowMeshBlocks_filter ms ts d hms]

lemma rowDepth_integrable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (rs : List (ℝ × ℝ)) (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (i : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (rowDerivativeDepthMoment rs u i) μ := by
  exact (integrable_const (L^2)).mono' (measurable_rowDerivativeDepthMoment hu rs hrs i).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rowDerivativeDepthMoment_bounds hu rs hrs i x).1]
      exact (rowDerivativeDepthMoment_bounds hu rs hrs i x).2)

lemma rowDepth_joint_measurable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hms : ∀ m ∈ ms, 0 ≤ m ∧ m ≤ 1) (d : ℕ → ℝ≥0) :
    Measurable (fun z : ℝ × ℝ =>
      rowDerivativeDepthMoment (rowGaussianBlocks ms d) u (rpcStepLevel ms z.1) z.2) := by
  have he : Measurable (fun z : ℕ × ℝ => rowDerivativeDepthMoment (rowGaussianBlocks ms d) u z.1 z.2) :=
    measurable_from_prod_countable_right fun i =>
      measurable_rowDerivativeDepthMoment hu _ (rowGaussianBlocks_valid ms hms d) i
  exact he.comp ((measurable_rpcStepLevel ms).prodMap measurable_id)

lemma RowFiniteProfile.derivative_measurable {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) :
    Measurable (P.derivative u) := by
  have hv := rowBoundedOperator_terminal hu (by norm_num : (0:ℝ) ≤ 1) le_rfl (P.residual:ℝ)
  exact (rowDepth_joint_measurable hv P.ranks (fun m hm => ⟨(P.valid m hm).1.le,(P.valid m hm).2.le⟩)
    P.increment).stronglyMeasurable.integral_prod_right'.measurable

lemma RowFiniteProfile.derivative_bounds {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (s : ℝ) :
    0 ≤ P.derivative u s ∧ P.derivative u s ≤ L^2 := by
  have hv := rowBoundedOperator_terminal hu (by norm_num : (0:ℝ) ≤ 1) le_rfl (P.residual:ℝ)
  have hr := rowGaussianBlocks_valid P.ranks
    (fun m hm => ⟨(P.valid m hm).1.le,(P.valid m hm).2.le⟩) P.increment
  refine ⟨integral_nonneg (fun x => (rowDerivativeDepthMoment_bounds hv _ hr _ x).1),?_⟩
  calc
    _ ≤ ∫ _, L^2 ∂gaussianReal 0 P.root := integral_mono
      (rowDepth_integrable hv _ hr _ _) (integrable_const _)
      (fun x => (rowDerivativeDepthMoment_bounds hv _ hr _ x).2)
    _ = _ := by simp

lemma RowFiniteProfile.derivative_monotone {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) :
    Monotone (P.derivative u) := by
  have hv := rowBoundedOperator_terminal hu (by norm_num : (0:ℝ) ≤ 1) le_rfl (P.residual:ℝ)
  have hr := rowGaussianBlocks_valid P.ranks
    (fun m hm => ⟨(P.valid m hm).1.le,(P.valid m hm).2.le⟩) P.increment
  intro s t hst
  exact integral_mono (rowDepth_integrable hv _ hr _ _) (rowDepth_integrable hv _ hr _ _)
    (fun x => rowDerivativeDepthMoment_monotone hv _ hr x ((rpcStepLevel_monotone P.ranks) hst))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace MicroscopicJamming
local instance (r : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := ⟨rfl⟩

lemma RowFiniteProfile.bound {Q : ℝ} (P : RowFiniteProfile Q) : P.profile.val 1 ≤ Q := by
  exact (rowCascadeProfile_bound P.ranks (fun m hm => (P.valid m hm).2) P.increment P.root P.residual).trans_eq P.diagonal

lemma rowVariableMesh_fields_converge
    (u : ℝ → ℝ) (L H : ℝ) (hu : ContDiff ℝ 2 u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (Q : ℝ) (P : ℕ → RowFiniteProfile Q) (q : SphericalProfile) (hq : q.val 1 ≤ Q)
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0))
    (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (k : ℕ) :
    ∃ (ρ : ℕ → ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)))
      (ρ₀ : ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ))),
      (∀ n, (ρ n : Measure _) =
        replicaFieldLaw
          (rowReplicaEnvironmentLaw (rowMeshRanks (P n).ranks (rankMesh n))
            (rowMeshIncrement (P n).ranks (rankMesh n) (P n).increment) (P n).root)
          (rowReplicaKernel (rowMeshRanks (P n).ranks (rankMesh n)) (P n).residual)
          (rowFullPotential (rowMeshRanks (P n).ranks (rankMesh n)) u)
          (rowFullPair (rowMeshRanks (P n).ranks (rankMesh n)) u (rowMeshTest (P n).ranks φ n)) k) ∧
      (ρ₀ : Measure _) = (gaussianAdjunctionMeasure (2+k)
        (rowFullRankCovariance (2+k) Q q) realizedRankLaw).map (rowFullRankView u φ k) ∧
      Tendsto ρ atTop (𝓝 ρ₀) := by
  let μ := realizedRankLaw.prod (stdGaussian (EuclideanSpace ℝ (Fin (2+k))))
  have hmeas (p : SphericalProfile) :
      Measurable (gaussianAdjunctionMap (2+k) (rowFullRankCovariance (2+k) Q p)) :=
    measurable_matrix_gaussian_map (2+k) _ (measurable_rowFullRankCovariance (2+k) Q p)
  let f (n : ℕ) := rowMeshRankView u φ k n ∘
    gaussianAdjunctionMap (2+k) (rowFullRankCovariance (2+k) Q (P n).profile)
  let g := rowFullRankView u φ k ∘ gaussianAdjunctionMap (2+k) (rowFullRankCovariance (2+k) Q q)
  have hf n : Measurable (f n) := (measurable_rowMeshRankView u hu φ k n).comp (hmeas _)
  have hg : Measurable g := (measurable_rowFullRankView u hu φ k).comp (hmeas _)
  let ρ : ℕ → ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)) := fun n =>
    ⟨μ.map (f n), inferInstance⟩
  let ρ₀ : ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)) :=
    ⟨μ.map g, inferInstance⟩
  refine ⟨ρ,ρ₀,?_,?_,?_⟩
  · intro n
    rw [rowMesh_fields_exact u L H hu hL hH hb _ (P n).ordered (P n).valid,
      (P n).diagonal]
    exact (Measure.map_map (measurable_rowMeshRankView u hu φ k n) (hmeas _)).symm
  · exact (Measure.map_map (measurable_rowFullRankView u hu φ k) (hmeas _)).symm
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ks,hks,hae⟩ := ((rowClosedProfile_tendstoInMeasure (fun n => (P n).profile) q hP).comp hns).exists_seq_tendsto_ae
    refine ⟨ks,?_⟩
    apply probabilityMap_tendsto_of_ae μ (fun n => f (ns (ks n))) g
      (fun n => (hf _).aemeasurable) hg.aemeasurable
    have hc := rowRankCovariance_tendsto_ae_of_profile_ae Q (fun n => (P (ns (ks n))).profile) q (2+k) hae
    have hps : ∀ᵐ U ∂realizedRankLaw, ∀ n,
        (rowFullRankCovariance (2+k) Q (P (ns (ks n))).profile U).PosSemidef :=
      ae_all_iff.mpr fun n => rowFullRankCovariance_psd (2+k) Q _ (P _).bound
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hc,
      Measure.quasiMeasurePreserving_fst.ae hps,
      Measure.quasiMeasurePreserving_fst.ae (rowFullRankCovariance_psd (2+k) Q q hq),
      Measure.quasiMeasurePreserving_fst.ae realizedRankLaw_constraints] with z hc hps hp hz
    have hzlim := matrix_gaussian_map_tendsto (2+k) _ _ hps hp hc z.2
    have ht := (rowTestExtend_continuous φ).continuousAt.tendsto.comp
      ((rankMeshValue_tendsto (hz.2.2.1 0 1)).comp (hns.comp hks.tendsto_atTop))
    have hd : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
    have he i := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.comp hzlim
    exact (ht.mul ((hd.continuousAt.tendsto.comp (he (Fin.castAdd k (0:Fin 2)))).mul
      (hd.continuousAt.tendsto.comp (he (Fin.castAdd k (1:Fin 2)))))).prodMk_nhds
        (tendsto_pi_nhds.mpr fun i => hu.continuous.continuousAt.tendsto.comp (he i))
end MicroscopicJamming

end

end OAI
