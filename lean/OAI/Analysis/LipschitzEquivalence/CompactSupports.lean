import OAI.Analysis.LipschitzEquivalence.FiniteMultipliers

namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped Topology
open Filter Set
variable {M : Type uM} [MetricSpace M]

theorem near_isClosed (A : Finset M) (δ : ℝ) : IsClosed (Near A δ) := by
  have he : Near A δ = ⋃ a ∈ A, Metric.closedBall a δ := by
    ext x
    simp only [Near,Set.mem_ofPred_eq,Set.mem_iUnion,Metric.mem_closedBall]
    constructor <;> rintro ⟨a,ha,h⟩ <;> exact ⟨a,ha,h⟩
  rw [he]
  exact isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall)

theorem nested_finite_cover_compact [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (A : ℕ → Finset M) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) :
    IsCompact (⋂ n, K n) := by
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_,(isClosed_iInter hc).isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  refine ⟨(A N : Set M),(A N).finite_toSet,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := hcover N (Set.mem_iInter.mp hx (N+1))
  exact Set.mem_iUnion₂.mpr ⟨a,ha,hxa.trans_lt hrN⟩

theorem nested_finite_cover_range (K : ℕ → Set M) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n))
    (x : ℕ → M) (hx : ∀ n, x n ∈ K n) : TotallyBounded (Set.range x) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hr ε hε
  have hrN : r N < ε := (le_abs_self _).trans_lt (by simpa only [dist_zero_right,Real.norm_eq_abs] using hN N le_rfl)
  let F : Finset M := A N ∪ (Finset.range (N+1)).image x
  refine ⟨(F : Set M),F.finite_toSet,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < N+1
  · apply Set.mem_iUnion₂.mpr
    refine ⟨x n,?_,?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hn,rfl⟩)
    · simpa only [Metric.mem_ball,dist_self] using hε
  · obtain ⟨a,ha,hxa⟩ := hcover N (hanti (le_of_not_gt hn) (hx n))
    exact Set.mem_iUnion₂.mpr ⟨a,Finset.mem_union_left _ ha,hxa.trans_lt hrN⟩

theorem nested_finite_cover_uniform [CompleteSpace M] (K : ℕ → Set M)
    (hc : ∀ n, IsClosed (K n)) (hanti : Antitone K)
    (A : ℕ → Finset M) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hcover : ∀ n, K (n+1) ⊆ Near (A n) (r n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ x ∈ K N, ∃ y ∈ ⋂ n, K n, dist x y < ε := by
  classical
  by_contra! h
  choose x hx hfar using h
  have hb := nested_finite_cover_range K hanti A r hr hcover x hx
  have hcompact : IsCompact (closure (Set.range x)) :=
    isCompact_iff_totallyBounded_isComplete.mpr ⟨hb.closure,isClosed_closure.isComplete⟩
  obtain ⟨y,_hy,a,ha,hlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hy : y ∈ ⋂ n, K n := by
    apply Set.mem_iInter.mpr
    intro n
    apply (hc n).mem_of_tendsto hlim
    filter_upwards [(tendsto_atTop.mp ha.tendsto_atTop) n] with i hi
    exact hanti hi (hx (a i))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  exact (not_lt_of_ge (hfar (a N) y hy)) (hN N le_rfl)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem test_tendsto_of_pointwise {f : ℕ → M → ℝ} {g : M → ℝ} {C D : ℝ≥0}
    (hf : ∀ n, LipschitzWith C (f n)) (hg : LipschitzWith D g)
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (μ : Space M) :
    Tendsto (fun n => test (normalized (f n) (hf n)) μ) atTop (𝓝 (test (normalized g hg) μ)) := by
  have hfinite (a : M →₀ ℝ) :
      Tendsto (fun n => test (normalized (f n) (hf n)) (Finsupp.linearCombination ℝ point a))
        atTop (𝓝 (test (normalized g hg) (Finsupp.linearCombination ℝ point a))) := by
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,test_point,smul_eq_mul]
    change Tendsto (fun n => ∑ x ∈ a.support, a x*(f n x-f n 0))
      atTop (𝓝 (∑ x ∈ a.support, a x*(g x-g 0)))
    apply tendsto_finsetSum
    intro x _
    exact tendsto_const_nhds.mul ((hpoint x).sub (hpoint 0))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := exists_finite_approx μ (show 0 < ε/(2*((C : ℝ)+D+1)) by positivity)
  let ν := Finsupp.linearCombination ℝ point a
  have hsmall : ((C : ℝ)+D)*‖μ-ν‖ < ε/2 := by
    have hh := (lt_div_iff₀ (show (0 : ℝ) < 2*((C : ℝ)+D+1) by positivity)).mp ha
    have hn := norm_nonneg (μ-ν)
    change ‖μ-ν‖*(2*((C : ℝ)+D+1)) < ε at hh
    nlinarith
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hfinite a) (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have h₁ : dist (test (normalized (f n) (hf n)) μ) (test (normalized (f n) (hf n)) ν) ≤ C*‖μ-ν‖ := by
    rw [dist_eq_norm,← map_sub]
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le _ _) (norm_nonneg _))
  have h₃ : dist (test (normalized g hg) ν) (test (normalized g hg) μ) ≤ D*‖μ-ν‖ := by
    rw [dist_comm,dist_eq_norm,← map_sub]
    exact (norm_test_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalized_le _ _) (norm_nonneg _))
  have ht := dist_triangle (test (normalized (f n) (hf n)) μ)
    (test (normalized (f n) (hf n)) ν) (test (normalized g hg) μ)
  have ht' := dist_triangle (test (normalized (f n) (hf n)) ν)
    (test (normalized g hg) ν) (test (normalized g hg) μ)
  have hm := hN n hn
  change dist (test (normalized (f n) (hf n)) ν) (test (normalized g hg) ν) < ε/2 at hm
  linarith

theorem mem_supported_of_annihilating {K : Set M} (μ : Space M)
    (h : ∀ f : M → ℝ, ∀ hf : LipschitzWith 1 f, f 0 = 0 →
      (∀ x ∈ K, f x = 0) → test (normalized f hf) μ = 0) : μ ∈ supported K := by
  let S := supported K
  let : IsClosed (S : Set (Space M)) := supported_isClosed K
  by_contra hμ
  have hne : S.mkQL μ ≠ 0 := by
    intro hz
    apply hμ
    exact (Submodule.Quotient.mk_eq_zero S).mp hz
  have hp : 0 < ‖S.mkQL μ‖ := norm_pos_iff.mpr hne
  have hfar : ∀ ν : Space M, ν ∈ S → ‖S.mkQL μ‖ ≤ ‖μ-ν‖ := by
    intro ν hν
    have hz : S.mkQL ν = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hν
    have he : S.mkQL (μ-ν) = S.mkQL μ := by rw [map_sub,hz,sub_zero]
    rw [← he]
    exact Submodule.Quotient.norm_mk_le S (μ-ν)
  obtain ⟨f,hf,hf0,hfK,hlarge⟩ := exists_vanishing_test K μ hfar
  have hz := h f hf hf0 hfK
  have hl := hlarge hf
  rw [hz] at hl
  exact (not_le_of_gt hp) hl

def clip (ε t : ℝ) : ℝ := max (t-ε) 0 + min (t+ε) 0

theorem clip_lipschitz (ε : ℝ) : LipschitzWith 2 (clip ε) := by
  have h₁ := (lipschitz_sub_const (fun t : ℝ => t) LipschitzWith.id ε).max_const 0
  have h₂ : LipschitzWith 1 (fun t : ℝ => min (t+ε) 0) := by
    simpa only [sub_neg_eq_add] using
      (lipschitz_sub_const (fun t : ℝ => t) LipschitzWith.id (-ε)).min_const 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (h₁.add h₂).dist_le_mul x y
  simpa only [clip,NNReal.coe_add,NNReal.coe_one,one_add_one_eq_two] using h

theorem clip_zero {ε t : ℝ} (ht : |t| ≤ ε) : clip ε t = 0 := by
  have ht' := abs_le.mp ht
  simp only [clip,max_eq_right (by linarith : t-ε ≤ 0),min_eq_right (by linarith : 0 ≤ t+ε),add_zero]

theorem clip_tendsto {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => clip (ε n) t) atTop (𝓝 t) := by
  have h : Tendsto (fun n => max (t-ε n) 0+min (t+ε n) 0) atTop
      (𝓝 (max (t-0) 0+min (t+0) 0)) :=
    ((tendsto_const_nhds.sub hε).max tendsto_const_nhds).add
      ((tendsto_const_nhds.add hε).min tendsto_const_nhds)
  change Tendsto (fun n => clip (ε n) t) atTop (𝓝 (max (t-0) 0+min (t+0) 0)) at h
  simpa only [sub_zero,add_zero,max_add_min] using h

theorem supported_intersection_of_uniform (K : ℕ → Set M)
    (huniform : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ x ∈ K N,
      ∃ y ∈ ⋂ n, K n, dist x y < ε) (μ : Space M)
    (hμ : ∀ n, μ ∈ supported (K n)) : μ ∈ supported (⋂ n, K n) := by
  classical
  apply mem_supported_of_annihilating μ
  intro f hf hf0 hfK
  let ε : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose N hN using fun n => huniform (ε n) (hε n)
  let fs : ℕ → M → ℝ := fun n x => clip (ε n) (f x)
  have hfs (n : ℕ) : LipschitzWith 2 (fs n) := by
    simpa only [mul_one,Function.comp_def] using (clip_lipschitz (ε n)).comp hf
  have hfs0 (n : ℕ) : fs n 0 = 0 := by
    exact clip_zero (by rw [hf0,abs_zero]; exact (hε n).le)
  have hzero (n : ℕ) : test (normalized (fs n) (hfs n)) μ = 0 := by
    apply supported_le_ker (K := K (N n)) (test (normalized (fs n) (hfs n))) ?_ (hμ (N n))
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hN n x hx
    have hfx : |f x| ≤ ε n := by
      have h := hf.dist_le_mul x y
      rw [hfK y hy,dist_zero_right,Real.norm_eq_abs,NNReal.coe_one,one_mul] at h
      exact h.trans hxy.le
    change fs n x-fs n 0 = 0
    rw [hfs0]
    exact sub_eq_zero.mpr (clip_zero hfx)
  have hlim := test_tendsto_of_pointwise hfs hf (fun x => clip_tendsto hεlim (f x)) μ
  have he : (fun n => test (normalized (fs n) (hfs n)) μ) = fun _ => 0 := funext hzero
  rw [he] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end LipschitzCounterexample.FreeSpace

end

end OAI
