import Mathlib
import OAI.Probability.JammingConcavity.RowZeroRefinementClosureProfileDistanceEqZeroOfTests

namespace OAI

/-! Row Zero Refinement Closure Row Density Score Identity. -/

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
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma profileL1_tendsto_of_tests (pn : ℕ → SphericalProfile) (B : ℝ)
    (hpn : ∀ n s, s ∈ Set.Icc 0 1 → (pn n).val s ≤ B)
    (ht : ∀ φ : C(Set.Icc (0:ℝ) 1,ℝ), ∃ b : ℝ,
      Tendsto (fun n => ∫ s in (0:ℝ)..1, rowTestExtend φ s*(pn n).val s) atTop (𝓝 b)) :
    ∃ p : SphericalProfile, (∀ s ∈ Set.Icc 0 1, p.val s ≤ B) ∧
      Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0) := by
  obtain ⟨p,l,hl,hlT,hp,hlim⟩ := profileCompactFilter pn B hpn
  let := hl
  refine ⟨p,hp,?_⟩
  by_contra hh
  rw [Metric.tendsto_atTop] at hh
  push Not at hh
  obtain ⟨ε,hε,hbad⟩ := hh
  choose ns hns hbadns using hbad
  have hnsT : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  obtain ⟨q,k,hk,hkT,hq,hlimq⟩ := profileCompactFilter (fun n => pn (ns n)) B
    (fun n s hs => hpn (ns n) s hs)
  let := hk
  have he : sphericalProfileDistance q.val p.val = 0 := by
    apply profileDistance_eq_zero_of_tests
    intro φ
    obtain ⟨b,hb⟩ := ht φ
    have h1 := profileTest_tendsto_of_L1 pn p φ hlim
    have h2 := profileTest_tendsto_of_L1 (fun n => pn (ns n)) q φ hlimq
    have hpB := tendsto_nhds_unique h1 (hb.mono_left hlT)
    have hqB := tendsto_nhds_unique h2 ((hb.comp hnsT).mono_left hkT)
    exact hqB.trans hpB.symm
  have hlimp : Tendsto (fun n => sphericalProfileDistance (pn (ns n)).val p.val) k (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => ?_) hlimq
    have hb := sphericalProfileDistance_triangle (pn (ns n)) q p
    simpa [he] using hb
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hlimp).2 ε hε).exists
  have hb := hbadns n
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (sphericalProfileDistance_nonneg _ _)] at hb
  exact (not_lt_of_ge hb) hn

def RowFiniteProfile.derivativeProfile {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) : SphericalProfile where
  val := P.derivative u
  mono := (P.derivative_monotone hu).monotoneOn _
  nonneg := fun s _ => (P.derivative_bounds hu s).1

theorem rowDerivativeLimit : RowDerivativeLimitStatement := by
  intro u L H hu hL hH hb Q P q hq hP
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),hL,hH,
    fun x => (hb x).1,fun x => (hb x).2⟩
  exact profileL1_tendsto_of_tests (fun n => (P n).derivativeProfile ht) (L^2)
    (fun n s hs => ((P n).derivative_bounds ht s).2)
    (rowProfileTestConvergence u L H hu hL hH hb Q P q hq hP)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

def RowGeneralDerivativeStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ Q : ℝ, ∃ D : {q : SphericalProfile // q.val 1 ≤ Q} → SphericalProfile,
    (∀ q s, s ∈ Set.Icc 0 1 → (D q).val s ≤ L^2) ∧
    (∀ (q : {q : SphericalProfile // q.val 1 ≤ Q}) (P : ℕ → RowFiniteProfile Q),
      Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) (D q).val) atTop (𝓝 0)) ∧
    (∀ (q : {q : SphericalProfile // q.val 1 ≤ Q})
      (qn : ℕ → {q : SphericalProfile // q.val 1 ≤ Q}),
      Tendsto (fun n => sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0) →
      Tendsto (fun n => sphericalProfileDistance (D (qn n)).val (D q).val) atTop (𝓝 0))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma gridStep_total (q : SphericalProfile) (n : ℕ) :
    ((q.gridStep n).initial:ℝ) + ∑ j ∈ Finset.range n, ((q.gridStep n).variance j:ℝ) =
      q.val (spinGridPoint n n) := by
  rw [gridStep_initial]
  have hs : (∑ j ∈ Finset.range n, ((q.gridStep n).variance j:ℝ)) =
      q.val (spinGridPoint n n)-q.val 0 := by
    calc
      _ = ∑ j ∈ Finset.range n, (q.val (spinGridPoint n (j+1))-q.val (spinGridPoint n j)) :=
        Finset.sum_congr rfl (fun j hj => gridStep_variance q n j (Finset.mem_range.mp hj))
      _ = _ := by rw [Finset.sum_range_sub (fun j => q.val (spinGridPoint n j)),spinGridPoint_zero]
  rw [hs]; ring

lemma gridStep_total_le (q : SphericalProfile) (n : ℕ) :
    ((q.gridStep n).initial:ℝ) + ∑ j ∈ Finset.range n, ((q.gridStep n).variance j:ℝ) ≤ q.val 1 := by
  rw [gridStep_total]
  exact q.mono (spinGridPoint_mem n n (by omega)) (by norm_num) (spinGridPoint_mem n n (by omega)).2

def SphericalProfile.rowGrid {Q : ℝ} (q : SphericalProfile) (hQ : q.val 1 ≤ Q)
    (n : ℕ) : RowFiniteProfile Q where
  ranks := (q.gridStep n).ranks
  ordered := (q.gridStep n).ordered
  valid := (q.gridStep n).ranks_mem
  increment := (q.gridStep n).variance
  root := (q.gridStep n).initial
  residual := Real.toNNReal (Q-q.val (spinGridPoint n n))
  diagonal := by
    simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum]
    have h : q.val (spinGridPoint n n) ≤ Q :=
      (q.mono (spinGridPoint_mem n n (by omega)) (by norm_num)
        (spinGridPoint_mem n n (by omega)).2).trans hQ
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr h)]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((q.gridStep n).variance j:ℝ))]
    change ((q.gridStep n).initial:ℝ) + (∑ j ∈ Finset.range (spinGridRanks n).length,
      ((q.gridStep n).variance j:ℝ)) + (Q-q.val (spinGridPoint n n)) = Q
    rw [spinGridRanks_length,gridStep_total]; ring

lemma rowGaussianBlocks_cumulative (ms : List ℝ) (d : ℕ → ℝ≥0) (s : ℝ) :
    ((rowGaussianBlocks ms d).map (fun r => if r.1 ≤ s then r.2 else 0)).sum =
      ∑ j : Fin ms.length, if ms[j.val]! ≤ s then (d j:ℝ) else 0 := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks]
  | cons m ms ih =>
    simp only [rowGaussianBlocks,List.map_cons,List.sum_cons,
      List.length_cons,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
    simpa using congrArg ((if m ≤ s then (d 0:ℝ) else 0)+·) (ih (fun j => d (j+1)))

lemma sphericalProfile_ext {p q : SphericalProfile} (h : p.val = q.val) : p=q := by
  cases p; cases q; cases h; rfl

lemma rowGrid_profile {Q : ℝ} (q : SphericalProfile) (hQ : q.val 1 ≤ Q) (n : ℕ) :
    (q.rowGrid hQ n).profile = (q.gridStep n).toProfile := by
  apply sphericalProfile_ext
  funext s
  change (rowCascadeProfile (q.gridStep n).ranks (q.gridStep n).variance
    (q.gridStep n).initial).val s = _
  rw [rowCascadeProfile_sum _ (q.gridStep n).ordered,rowGaussianBlocks_cumulative,
    Fin.sum_univ_eq_sum_range (fun j => if (q.gridStep n).ranks[j]! ≤ s then
      ((q.gridStep n).variance j:ℝ) else 0)]
  rfl

lemma rowGrid_distance_tendsto {Q : ℝ} (q : SphericalProfile) (hQ : q.val 1 ≤ Q) :
    Tendsto (fun n => sphericalProfileDistance (q.rowGrid hQ n).profile.val q.val) atTop (𝓝 0) := by
  have hb : ∀ n, sphericalProfileDistance (q.rowGrid hQ n).profile.val q.val ≤
      q.val 1/((n:ℝ)+1) := by
    intro n
    rw [rowGrid_profile,sphericalProfileDistance_comm]
    exact gridStep_distance_le q (q.val 1) (fun s hs => q.mono hs (by norm_num) hs.2) n
  have ht : Tendsto (fun n : ℕ => q.val 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) hb ht
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma profile_L1_limit_unique (pn : ℕ → SphericalProfile) (p q : SphericalProfile)
    (hp : Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0))
    (hq : Tendsto (fun n => sphericalProfileDistance (pn n).val q.val) atTop (𝓝 0)) :
    sphericalProfileDistance p.val q.val = 0 := by
  apply profileDistance_eq_zero_of_tests
  intro φ
  exact tendsto_nhds_unique (profileTest_tendsto_of_L1 pn p φ hp)
    (profileTest_tendsto_of_L1 pn q φ hq)

lemma rowTerminal_of_C2 {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) :
    RowBoundedTerminal u L H := by
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  exact ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),hL,hH,
    fun x => (hb x).1,fun x => (hb x).2⟩

lemma rowDerivativeLimits_eq {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P R : ℕ → RowFiniteProfile Q) (q D E : SphericalProfile) (hq : q.val 1 ≤ Q)
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0))
    (hR : Tendsto (fun n => sphericalProfileDistance (R n).profile.val q.val) atTop (𝓝 0))
    (hD : Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) D.val) atTop (𝓝 0))
    (hE : Tendsto (fun n => sphericalProfileDistance ((R n).derivative u) E.val) atTop (𝓝 0)) :
    sphericalProfileDistance D.val E.val = 0 := by
  let Z : ℕ → RowFiniteProfile Q := fun n => if n % 2 = 0 then P n else R n
  have hZ : Tendsto (fun n => sphericalProfileDistance (Z n).profile.val q.val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _)
      (fun n => ?_) (show Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val +
      sphericalProfileDistance (R n).profile.val q.val) atTop (𝓝 0) by simpa using hP.add hR)
    dsimp [Z]
    split_ifs
    · exact le_add_of_nonneg_right (sphericalProfileDistance_nonneg _ _)
    · exact le_add_of_nonneg_left (sphericalProfileDistance_nonneg _ _)
  obtain ⟨F,hF,hZF⟩ := rowDerivativeLimit u L H hu hL hH hb Q Z q hq hZ
  have hte : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hto : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have he : ∀ n, Z (2*n) = P (2*n) := by intro n; simp [Z]
  have ho : ∀ n, Z (2*n+1) = R (2*n+1) := by intro n; simp [Z,Nat.add_mod]
  have ht := rowTerminal_of_C2 hu hL hH hb
  have hDF : sphericalProfileDistance D.val F.val = 0 :=
    profile_L1_limit_unique (fun n => (P (2*n)).derivativeProfile ht) D F
      (hD.comp hte) (by simpa only [Function.comp_def,he,RowFiniteProfile.derivativeProfile] using hZF.comp hte)
  have hFE : sphericalProfileDistance F.val E.val = 0 :=
    profile_L1_limit_unique (fun n => (R (2*n+1)).derivativeProfile ht) F E
      (by simpa only [Function.comp_def,ho,RowFiniteProfile.derivativeProfile] using hZF.comp hto) (hE.comp hto)
  exact le_antisymm (by simpa [hDF,hFE] using sphericalProfileDistance_triangle D F E)
    (sphericalProfileDistance_nonneg _ _)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowPrecision_tendsto : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem rowGeneralDerivative : RowGeneralDerivativeStatement := by
  intro u L H hu hL hH hb Q
  let T := {q : SphericalProfile // q.val 1 ≤ Q}
  have hex (q : T) : ∃ D : SphericalProfile, (∀ s ∈ Set.Icc 0 1, D.val s ≤ L^2) ∧
      Tendsto (fun n => sphericalProfileDistance ((q.1.rowGrid q.2 n).derivative u) D.val) atTop (𝓝 0) :=
    rowDerivativeLimit u L H hu hL hH hb Q (q.1.rowGrid q.2) q.1 q.2 (rowGrid_distance_tendsto q.1 q.2)
  choose D hDb hDlim using hex
  have ht := rowTerminal_of_C2 hu hL hH hb
  have hall (q : T) (P : ℕ → RowFiniteProfile Q)
      (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0)) :
      Tendsto (fun n => sphericalProfileDistance ((P n).derivative u) (D q).val) atTop (𝓝 0) := by
    obtain ⟨E,hE,hPE⟩ := rowDerivativeLimit u L H hu hL hH hb Q P q.1 q.2 hP
    have he := rowDerivativeLimits_eq hu hL hH hb P (q.1.rowGrid q.2) q.1 E (D q) q.2 hP
      (rowGrid_distance_tendsto q.1 q.2) hPE (hDlim q)
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg ((P n).derivativeProfile ht) (D q))
      (fun n => ?_) hPE
    simpa only [RowFiniteProfile.derivativeProfile,he,add_zero] using
      sphericalProfileDistance_triangle ((P n).derivativeProfile ht) E (D q)
  refine ⟨D,hDb,hall,?_⟩
  intro q qn hqn
  have hchoose (n : ℕ) : ∃ k : ℕ,
      sphericalProfileDistance ((qn n).1.rowGrid (qn n).2 k).profile.val (qn n).1.val < 1/((n:ℝ)+1) ∧
      sphericalProfileDistance (((qn n).1.rowGrid (qn n).2 k).derivative u) (D (qn n)).val < 1/((n:ℝ)+1) := by
    have he : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    exact (((tendsto_order.mp (rowGrid_distance_tendsto (qn n).1 (qn n).2)).2 _ he).and
      ((tendsto_order.mp (hDlim (qn n))).2 _ he)).exists
  choose k hk1 hk2 using hchoose
  let P : ℕ → RowFiniteProfile Q := fun n => (qn n).1.rowGrid (qn n).2 (k n)
  have hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.1.val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => ?_)
      (show Tendsto (fun n : ℕ => 1/((n:ℝ)+1)+sphericalProfileDistance (qn n).1.val q.1.val) atTop (𝓝 0)
        by simpa using rowPrecision_tendsto.add hqn)
    exact (sphericalProfileDistance_triangle (P n).profile (qn n).1 q.1).trans
      (add_le_add (hk1 n).le le_rfl)
  have hPD := hall q P hP
  apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => ?_)
    (show Tendsto (fun n : ℕ => 1/((n:ℝ)+1)+sphericalProfileDistance ((P n).derivative u) (D q).val)
      atTop (𝓝 0) by simpa using rowPrecision_tendsto.add hPD)
  have hh := sphericalProfileDistance_triangle (D (qn n)) ((P n).derivativeProfile ht) (D q)
  rw [sphericalProfileDistance_comm (D (qn n)) ((P n).derivativeProfile ht)] at hh
  exact hh.trans (add_le_add (hk2 n).le le_rfl)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma rowZero_fields_exact
    {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P : RowFiniteProfile Q) (k : ℕ) :
    replicaFieldLaw (rowReplicaEnvironmentLaw P.ranks P.increment P.root)
      (rowReplicaKernel P.ranks P.residual) (rowFullPotential P.ranks u)
      (fun _ : RowReplicaEnvironment P.ranks.length × (Fin 2 → RowReplicaSite P.ranks.length) => 0) k =
    (gaussianAdjunctionMeasure (2+k) (rowFullRankCovariance (2+k) Q P.profile)
      realizedRankLaw).map (rowFullRankView u 0 k) := by
  have he := rowRetainedRankLaw u L H hu hL hH hb P.ranks P.ordered P.valid
    P.increment P.root P.residual (fun _ => 0) k
  have hz : rowFullPair P.ranks u (fun _ => 0) =
      (fun _ : RowReplicaEnvironment P.ranks.length × (Fin 2 → RowReplicaSite P.ranks.length) => 0) := by
    funext z
    simp [rowFullPair]
  have hv : rowFullRankView u 0 k = (fun z : RankArray × EuclideanSpace ℝ (Fin (2+k)) =>
      (0,fun i => u (z.2 i))) := by
    funext z
    simp [rowFullRankView,rowTestExtend]
  rw [hz] at he
  rw [hv]
  simpa [P.diagonal,RowFiniteProfile.profile] using he

lemma rowLog_converges
    {u : ℝ → ℝ} {L H : ℝ} (hu : ContDiff ℝ 2 u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P : ℕ → RowFiniteProfile Q) (q : SphericalProfile) (hq : q.val 1 ≤ Q)
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0)) :
    ∃ ℓ : ℝ, Tendsto (fun n => ∫ ω, Real.log
      (replicaZ (rowReplicaKernel (P n).ranks (P n).residual) (rowFullPotential (P n).ranks u) ω)
        ∂rowReplicaEnvironmentLaw (P n).ranks (P n).increment (P n).root) atTop (𝓝 ℓ) := by
  have ht := rowTerminal_of_C2 hu hL hH hb
  apply (replicaLawContinuity (fun n => RowReplicaEnvironment (P n).ranks.length)
    (fun n => RowReplicaSite (P n).ranks.length) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun n => rowReplicaEnvironmentLaw (P n).ranks (P n).increment (P n).root)
    (fun n => rowReplicaKernel (P n).ranks (P n).residual)
    (fun n => by unfold rowReplicaEnvironmentLaw; infer_instance) (fun n => inferInstance)
    (fun n => rowFullPotential (P n).ranks u)
    (fun n => measurable_rowFullPotential _ _ hu.continuous.measurable)
    (rowUniformMoments ht Q P) 2 (fun _ _ => 0) (fun _ => measurable_const)
    ⟨0,fun _ _ => by norm_num⟩ ?_).1
  intro k
  obtain ⟨ρ,ρ₀,he,h₀,hlim⟩ := rowVariableMesh_fields_converge u L H hu hL hH hb Q P q hq hP 0 k
  refine ⟨ρ,ρ₀,?_,hlim⟩
  intro n
  rw [he n,rowMesh_fields_exact u L H hu hL hH hb _ (P n).ordered (P n).valid,
    rowZero_fields_exact hu hL hH hb,(P n).diagonal]
  congr 1

theorem rowCascadeLogContinuity : RowCascadeLogContinuityStatement := by
  intro u L H hu hL hH hb ms hms hm d p₀ Δ Q p hQ hp hP
  let P : ℕ → RowFiniteProfile Q := fun n =>
    ⟨ms n,hms n,hm n,d n,p₀ n,Δ n,congrArg NNReal.toReal (hQ n)⟩
  exact rowLog_converges hu hL hH hb P p hp hP
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

def rowInterpolatedBlocks (bs : List (ℝ × ℝ × ℝ)) (t : ℝ) : List (ℝ × ℝ) :=
  bs.map (fun b => (b.1,(1-t)*b.2.1+t*b.2.2))

def rowFiniteVarianceResponse : List (ℝ × ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ → ℝ
  | [],_,_,_ => 0
  | (a,T,R)::bs,u,t,x =>
    rowTiltStep a ((1-t)*T+t*R) (gaussianRowComposition (rowInterpolatedBlocks bs t) u) x
      (fun y => rowFiniteVarianceResponse bs u t y+(R-T)/2*
        (deriv (deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u)) y+
          a*(deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u) y)^2))

 

def RowFiniteVarianceStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ bs : List (ℝ × ℝ × ℝ),
      (∀ b ∈ bs, 0 ≤ b.1 ∧ b.1 ≤ 1 ∧ 0 ≤ b.2.1 ∧ 0 ≤ b.2.2) →
      ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ x,
        HasDerivAt (fun s => gaussianRowComposition (rowInterpolatedBlocks bs s) u x)
          (rowFiniteVarianceResponse bs u t x) t
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

def rowVarianceTotal (bs : List (ℝ × ℝ × ℝ)) : ℝ :=
  (bs.map (fun b => b.2.2-b.2.1)).sum

def rowVarianceCoefficients : List (ℝ × ℝ × ℝ) → ℝ → List ℝ
  | [],_ => []
  | (a,T,R)::bs,b => (rowVarianceTotal ((a,T,R)::bs)/2*(a-b))::rowVarianceCoefficients bs a

def rowDepthPairing (rs : List (ℝ × ℝ)) (u : ℝ → ℝ) : List ℝ → ℕ → ℝ → ℝ
  | [],_,_ => 0
  | c::cs,j,x => c*rowDerivativeDepthMoment rs u j x+rowDepthPairing rs u cs (j+1) x

 

def RowFiniteDiagonalStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
    ∀ bs : List (ℝ × ℝ × ℝ),
      (∀ c ∈ bs, 0 ≤ c.1 ∧ c.1 ≤ 1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2) →
      ∀ t ∈ Set.Ioo (0:ℝ) 1, ∀ b x : ℝ,
        HasDerivAt (fun s => gaussianRowComposition (rowInterpolatedBlocks bs s) u x)
          (rowVarianceTotal bs/2*(deriv (deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u)) x+
              b*(deriv (gaussianRowComposition (rowInterpolatedBlocks bs t) u) x)^2)+
            rowDepthPairing (rowInterpolatedBlocks bs t) u (rowVarianceCoefficients bs b) 0 x) t
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

def rowHeatDensity (T z : ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi*T))⁻¹ * Real.exp (-(z^2)/(2*T))

lemma rowHeatDensity_nonneg (T z : ℝ) : 0 ≤ rowHeatDensity T z := by
  unfold rowHeatDensity
  positivity

lemma rowHeatDensity_eq (T : ℝ≥0) (z : ℝ) :
    rowHeatDensity T z = gaussianPDFReal 0 T z := by simp [rowHeatDensity,gaussianPDFReal]

lemma gaussianHeat_eq_density {v : ℝ → ℝ} (hv : Measurable v)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    gaussianHeat v T x = ∫ z, rowHeatDensity T z*v (x+z) := by
  have he : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt T*z) = gaussianReal 0 ⟨T,hT.le⟩ := by
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
    exact Subtype.ext (Real.sq_sqrt hT.le)
  have hi := integral_map (μ := gaussianReal 0 1) (show AEMeasurable (fun z : ℝ => Real.sqrt T*z) (gaussianReal 0 1) from (by fun_prop : Measurable _).aemeasurable)
    ((show Measurable (fun z : ℝ => v (x+z)) from hv.comp (by fun_prop)).aestronglyMeasurable)
  rw [he,integral_gaussianReal_eq_integral_smul (show (⟨T,hT.le⟩ : ℝ≥0) ≠ 0 from by intro h; exact hT.ne' (congrArg NNReal.toReal h))] at hi
  convert hi.symm using 1 <;> simp [gaussianHeat,gaussianPDFReal,rowHeatDensity]
  congr 1

lemma rowHeatDensity_derivative {T : ℝ} (hT : 0 < T) (z : ℝ) :
    HasDerivAt (fun r => rowHeatDensity r z)
      (rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))) T := by
  have hπ : 0 < 2*Real.pi*T := by positivity
  have hd₁ := ((hasDerivAt_id T).const_mul (2*Real.pi)).sqrt hπ.ne'
  have hd₂ := ((hasDerivAt_const T (-(z^2))).div ((hasDerivAt_id T).const_mul 2)
    (by positivity : 2*T ≠ 0)).exp
  convert (hd₁.inv (Real.sqrt_ne_zero'.mpr hπ)).mul hd₂ using 1 <;> first | rfl | skip
  simp only [rowHeatDensity,id_eq,Pi.div_apply,Pi.inv_apply,zero_mul,mul_one]
  rw [Real.sq_sqrt hπ.le]
  field_simp [hT.ne',Real.sqrt_ne_zero'.mpr hπ,Real.pi_ne_zero]
  ring

lemma integrable_gaussian_linear_envelope {b : ℝ} (hb : 0 < b) (L : ℝ) :
    Integrable (fun z : ℝ => (1+z^2)*Real.exp (-b*z^2+L*|z|)) := by
  have hi₀ := integrable_exp_neg_mul_sq (by positivity : 0 < b/2)
  have hi₂ : Integrable (fun z : ℝ => z^2*Real.exp (-(b/2)*z^2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < b/2) (by norm_num : (-1:ℝ) < 2)
  apply ((hi₀.add hi₂).const_mul (Real.exp (L^2/(2*b)))).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1+z^2)*Real.exp (-b*z^2+L*|z|))]
  have he : -b*z^2+L*|z| ≤ -(b/2)*z^2+L^2/(2*b) := by
    have hh := sq_nonneg (b*|z|-L)
    ring_nf at hh
    rw [sq_abs] at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*b)).mpr (show
      (-b*z^2+L*|z|+(b/2)*z^2)*(2*b) ≤ L^2 by nlinarith [sq_abs z])
    linarith
  calc
    _ ≤ (1+z^2)*Real.exp (-(b/2)*z^2+L^2/(2*b)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = Real.exp (L^2/(2*b))*(Real.exp (-(b/2)*z^2)+z^2*Real.exp (-(b/2)*z^2)) := by
      rw [Real.exp_add]; ring

lemma rowHeatDensity_bounds {a b T : ℝ} (ha : 0 < a) (haT : a ≤ T) (hTb : T ≤ b) (z : ℝ) :
    rowHeatDensity T z ≤ (Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (-(1/(2*b))*z^2) ∧
    |rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))| ≤
      (Real.sqrt (2*Real.pi*a))⁻¹*(1/(2*a^2)+1/(2*a))*(1+z^2)*Real.exp (-(1/(2*b))*z^2) := by
  have hT : 0 < T := ha.trans_le haT
  have hb : 0 < b := hT.trans_le hTb
  have hpdf : rowHeatDensity T z ≤ (Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (-(1/(2*b))*z^2) := by
    unfold rowHeatDensity
    apply mul_le_mul _ _ (Real.exp_pos _).le (by positivity)
    · apply inv_anti₀ (by positivity)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left haT (by positivity))
    · apply Real.exp_le_exp.mpr
      have hh := div_le_div_of_nonneg_left (sq_nonneg z) (by positivity : 0 < 2*T)
        (show 2*T ≤ 2*b by linarith)
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith only [hh]
  refine ⟨hpdf,?_⟩
  have ht : |z^2/(2*T^2)-1/(2*T)| ≤ (1/(2*a^2)+1/(2*a))*(1+z^2) := by
    have h₂ : z^2/(2*T^2) ≤ z^2/(2*a^2) := div_le_div_of_nonneg_left (sq_nonneg z) (by positivity)
      (by nlinarith)
    have h₁ : 1/(2*T) ≤ 1/(2*a) := one_div_le_one_div_of_le (by positivity) (by linarith)
    calc
      _ ≤ |z^2/(2*T^2)|+|1/(2*T)| := abs_sub _ _
      _ = z^2/(2*T^2)+1/(2*T) := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      _ ≤ z^2/(2*a^2)+1/(2*a) := add_le_add h₂ h₁
      _ ≤ _ := by
        have : 0 ≤ (1/(2*a^2)) + (1/(2*a))*z^2 := by positivity
        simp only [div_eq_mul_inv] at *
        nlinarith
  rw [abs_mul,abs_of_nonneg (rowHeatDensity_nonneg T z)]
  calc
    _ ≤ ((Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (-(1/(2*b))*z^2))*
        ((1/(2*a^2)+1/(2*a))*(1+z^2)) :=
      mul_le_mul hpdf ht (abs_nonneg _) (by positivity)
    _ = _ := by ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowDensity_product_bound {a b T K L v z : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hTb : T ≤ b) (hK : 0 ≤ K) (hv : |v| ≤ K*Real.exp (L*|z|)) :
    |rowHeatDensity T z*v| ≤ ((Real.sqrt (2*Real.pi*a))⁻¹*K)*
      ((1+z^2)*Real.exp (-(1/(2*b))*z^2+L*|z|)) := by
  rw [abs_mul,abs_of_nonneg (rowHeatDensity_nonneg _ _)]
  calc
    _ ≤ ((Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (-(1/(2*b))*z^2))*(K*Real.exp (L*|z|)) :=
      mul_le_mul (rowHeatDensity_bounds ha haT hTb z).1 hv (abs_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [Real.exp_add]
      have : 0 ≤ (Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (-(1/(2*b))*z^2)*K*Real.exp (L*|z|)*z^2 := by positivity
      nlinarith

lemma rowDensity_response_bound {a b T K L v w δ z : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hTb : T ≤ b) (hK : 0 ≤ K) (hv : |v| ≤ K*Real.exp (L*|z|))
    (hw : |w| ≤ K*Real.exp (L*|z|)) :
    |rowHeatDensity T z*(w+δ*(z^2/(2*T^2)-1/(2*T))*v)| ≤
      ((Real.sqrt (2*Real.pi*a))⁻¹*K +
        (Real.sqrt (2*Real.pi*a))⁻¹*(1/(2*a^2)+1/(2*a))*|δ| *K)*
      ((1+z^2)*Real.exp (-(1/(2*b))*z^2+L*|z|)) := by
  have hh := rowHeatDensity_bounds ha haT hTb z
  have h₁ := rowDensity_product_bound ha haT hTb hK hw
  have h₂ : |rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))*δ*v| ≤
      ((Real.sqrt (2*Real.pi*a))⁻¹*(1/(2*a^2)+1/(2*a))*|δ| *K)*
      ((1+z^2)*Real.exp (-(1/(2*b))*z^2+L*|z|)) := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (((Real.sqrt (2*Real.pi*a))⁻¹*(1/(2*a^2)+1/(2*a))*(1+z^2)*
          Real.exp (-(1/(2*b))*z^2))*|δ|)*(K*Real.exp (L*|z|)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hh.2 (abs_nonneg δ)) hv (abs_nonneg _) (by positivity)
      _ = _ := by rw [Real.exp_add]; ring
  calc
    _ = |rowHeatDensity T z*w + rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))*δ*v| := by congr 1; ring
    _ ≤ |rowHeatDensity T z*w|+|rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))*δ*v| := abs_add_le _ _
    _ ≤ _ := by have := add_le_add h₁ h₂; nlinarith only [this]

 

lemma rowDensity_parameter_derivative
    {f f' : ℝ → ℝ → ℝ} {T : ℝ → ℝ} {δ t₀ a b K L : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀) (ha : 0 < a) (hK : 0 ≤ K)
    (hT : ∀ t ∈ s, a ≤ T t ∧ T t ≤ b)
    (hdT : ∀ t ∈ s, HasDerivAt T δ t)
    (hm : ∀ t, Measurable (f t)) (hm' : Measurable (f' t₀))
    (hd : ∀ t ∈ s, ∀ z, HasDerivAt (fun r => f r z) (f' t z) t)
    (hb : ∀ t ∈ s, ∀ z, |f t z| ≤ K*Real.exp (L*|z|) ∧ |f' t z| ≤ K*Real.exp (L*|z|)) :
    HasDerivAt (fun t => ∫ z, rowHeatDensity (T t) z*f t z)
      (∫ z, rowHeatDensity (T t₀) z*(f' t₀ z+δ*(z^2/(2*(T t₀)^2)-1/(2*T t₀))*f t₀ z)) t₀ := by
  let C := (Real.sqrt (2*Real.pi*a))⁻¹*K +
        (Real.sqrt (2*Real.pi*a))⁻¹*(1/(2*a^2)+1/(2*a))*|δ| *K
  have ht₀ := mem_of_mem_nhds hs
  have hb0 : 0 < b := (ha.trans_le (hT t₀ ht₀).1).trans_le (hT t₀ ht₀).2
  have hi := integrable_gaussian_linear_envelope (by positivity : 0 < 1/(2*b)) L
  have hiF : Integrable (fun z => rowHeatDensity (T t₀) z*f t₀ z) := by
    refine (hi.const_mul ((Real.sqrt (2*Real.pi*a))⁻¹*K)).mono' ?_ ?_
    · exact ((by unfold rowHeatDensity; fun_prop : Measurable (rowHeatDensity (T t₀))).mul (hm t₀)).aestronglyMeasurable
    · filter_upwards [] with z
      exact rowDensity_product_bound ha (hT t₀ ht₀).1 (hT t₀ ht₀).2 hK (hb t₀ ht₀ z).1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (μ := volume) (F := fun t z => rowHeatDensity (T t) z*f t z)
    (F' := fun t z => rowHeatDensity (T t) z*(f' t z+δ*(z^2/(2*(T t)^2)-1/(2*T t))*f t z))
    (bound := fun z => C*((1+z^2)*Real.exp (-(1/(2*b))*z^2+L*|z|))) hs ?_ hiF ?_ ?_ (hi.const_mul C) ?_).2
  · exact Eventually.of_forall fun t => ((by unfold rowHeatDensity; fun_prop : Measurable (rowHeatDensity (T t))).mul (hm t)).aestronglyMeasurable
  · exact ((by unfold rowHeatDensity; fun_prop : Measurable (rowHeatDensity (T t₀))).mul
      (hm'.add (((by fun_prop : Measurable (fun z : ℝ => δ*(z^2/(2*(T t₀)^2)-1/(2*T t₀)))).mul (hm t₀))))).aestronglyMeasurable
  · filter_upwards [] with z
    intro t ht
    exact rowDensity_response_bound ha (hT t ht).1 (hT t ht).2 hK (hb t ht z).1 (hb t ht z).2
  · filter_upwards [] with z
    intro t ht
    convert (((rowHeatDensity_derivative (ha.trans_le (hT t ht).1) z).comp t (hdT t ht)).mul (hd t ht z)) using 1
    <;> first | rfl | (simp only [Function.comp_apply]; ring)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma RowExpGrowth.mul {v w : ℝ → ℝ} (hv : RowExpGrowth v) (hw : RowExpGrowth w) :
    RowExpGrowth (fun x => v x*w x) := by
  obtain ⟨K,L,hK,hL,hv⟩ := hv
  obtain ⟨K',L',hK',hL',hw⟩ := hw
  refine ⟨K*K',L+L',mul_nonneg hK hK',add_nonneg hL hL',fun x => ?_⟩
  rw [abs_mul]
  calc
    _ ≤ (K*Real.exp (L*|x|))*(K'*Real.exp (L'*|x|)) := mul_le_mul (hv _) (hw _) (abs_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,Real.exp_add]; ring

lemma rowExpGrowth_pow (n : ℕ) : RowExpGrowth (fun x : ℝ => x^n) := by
  refine ⟨1,n,by norm_num,by positivity,fun x => ?_⟩
  rw [abs_pow,one_mul,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (abs_nonneg _)
  linarith [Real.add_one_le_exp |x|]

lemma RowExpGrowth.affine {v : ℝ → ℝ} (hv : RowExpGrowth v) (a b : ℝ) :
    RowExpGrowth (fun z => v (a+b*z)) := by
  obtain ⟨K,L,hK,hL,hv⟩ := hv
  refine ⟨K*Real.exp (L*|a|),L*|b|,by positivity,by positivity,fun z => ?_⟩
  calc
    _ ≤ K*Real.exp (L*|a+b*z|) := hv _
    _ ≤ K*Real.exp (L*(|a|+|b| *|z|)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
      exact mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_add_le a (b*z)) hL
    _ = _ := by rw [mul_add,Real.exp_add]; ring_nf

lemma RowExpGrowth.integrable {v : ℝ → ℝ} (hv : RowExpGrowth v) (hm : Measurable v) :
    Integrable v (gaussianReal 0 1) := by simpa using hv.integrable_affine hm 0 1

lemma rowGaussian_second_stein {v v₁ v₂ : ℝ → ℝ}
    (hv : Measurable v) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (hg : RowExpGrowth v) (hg₁ : RowExpGrowth v₁) (hg₂ : RowExpGrowth v₂)
    (hd : ∀ y, HasDerivAt v (v₁ y) y) (hd₁ : ∀ y, HasDerivAt v₁ (v₂ y) y)
    (x b : ℝ) :
    (∫ z, (z^2-1)*v (x+b*z) ∂gaussianReal 0 1) =
      b^2*(∫ z, v₂ (x+b*z) ∂gaussianReal 0 1) := by
  have h₀ := hg.integrable_affine hv x b
  have h₁ := hg₁.integrable_affine hv₁ x b
  have h₂ := hg₂.integrable_affine hv₂ x b
  have hz₀ : Integrable (fun z => z*v (x+b*z)) (gaussianReal 0 1) := by
    simpa using ((rowExpGrowth_pow 1).mul (hg.affine x b)).integrable (by fun_prop)
  have hz₁ : Integrable (fun z => z*v₁ (x+b*z)) (gaussianReal 0 1) := by
    simpa using ((rowExpGrowth_pow 1).mul (hg₁.affine x b)).integrable (by fun_prop)
  have hzz₀ : Integrable (fun z => z^2*v (x+b*z)) (gaussianReal 0 1) :=
    ((rowExpGrowth_pow 2).mul (hg.affine x b)).integrable (by fun_prop)
  have hs₁ := standardGaussian_integration_by_parts
    (f := fun z => v₁ (x+b*z)) (f' := fun z => b*v₂ (x+b*z))
    (fun z => by convert (hd₁ _).comp z ((hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b)) using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply]; ring))
    h₁ (h₂.const_mul b) hz₁
  have hs₀ := standardGaussian_integration_by_parts
    (f := fun z => z*v (x+b*z)) (f' := fun z => v (x+b*z)+b*(z*v₁ (x+b*z)))
    (fun z => by convert (hasDerivAt_id z).mul ((hd _).comp z ((hasDerivAt_const z x).add ((hasDerivAt_id z).const_mul b))) using 1 <;> first | rfl | (simp only [id_eq, Pi.add_apply, Function.comp_apply]; ring))
    hz₀ (h₀.add (hz₁.const_mul b)) (by convert hzz₀ using 1; funext z; ring)
  rw [integral_const_mul] at hs₁
  rw [integral_add h₀ (hz₁.const_mul b),integral_const_mul,hs₁] at hs₀
  calc
    _ = (∫ z, z^2*v (x+b*z) ∂gaussianReal 0 1) - ∫ z,v (x+b*z) ∂gaussianReal 0 1 := by
      rw [← integral_sub hzz₀ h₀]; congr 1; funext z; ring
    _ = _ := by
      have he : (∫ z,z^2*v (x+b*z) ∂gaussianReal 0 1) = ∫ z,z*(z*v (x+b*z)) ∂gaussianReal 0 1 := by congr 1; funext z; ring
      rw [he,hs₀]; ring
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowDensity_integrable {v : ℝ → ℝ} (hm : Measurable v) (hg : RowExpGrowth v)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    Integrable (fun z => rowHeatDensity T z*v (x+z)) := by
  obtain ⟨K,L,hK,hL,hg⟩ := hg.affine x 1
  have hi := integrable_gaussian_linear_envelope (by positivity : 0 < 1/(2*T)) L
  refine (hi.const_mul ((Real.sqrt (2*Real.pi*T))⁻¹*K)).mono' (by unfold rowHeatDensity; fun_prop) ?_
  filter_upwards [] with z
  exact rowDensity_product_bound hT le_rfl le_rfl hK (by simpa using hg z)

lemma rowDensity_score_identity {v v₁ v₂ : ℝ → ℝ}
    (hv : Measurable v) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (hg : RowExpGrowth v) (hg₁ : RowExpGrowth v₁) (hg₂ : RowExpGrowth v₂)
    (hd : ∀ y, HasDerivAt v (v₁ y) y) (hd₁ : ∀ y, HasDerivAt v₁ (v₂ y) y)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (∫ z, rowHeatDensity T z*(z^2/(2*T^2)-1/(2*T))*v (x+z)) =
      (1/2:ℝ)*gaussianHeat v₂ T x := by
  have hm : Measurable (fun z : ℝ => (z^2/(2*T^2)-1/(2*T))*v (x+z)) := by fun_prop
  have he := gaussianHeat_eq_density hm hT 0
  simp only [zero_add] at he
  calc
    _ = gaussianHeat (fun z => (z^2/(2*T^2)-1/(2*T))*v (x+z)) T 0 := by
      rw [he]; congr 1; funext z; ring
    _ = (1/(2*T))*(∫ z, (z^2-1)*v (x+Real.sqrt T*z) ∂gaussianReal 0 1) := by
      rw [← integral_const_mul]
      unfold gaussianHeat
      congr 1; funext z
      simp only [zero_add]
      rw [mul_pow,Real.sq_sqrt hT.le]
      field_simp
    _ = _ := by
      rw [rowGaussian_second_stein hv hv₁ hv₂ hg hg₁ hg₂ hd hd₁,Real.sq_sqrt hT.le]
      unfold gaussianHeat
      field_simp
end MicroscopicJamming

end

end OAI
