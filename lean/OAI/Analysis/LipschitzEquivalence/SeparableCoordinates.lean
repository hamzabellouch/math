import OAI.Analysis.LipschitzEquivalence.LocalOrthogonality

namespace OAI

universe uIndex uI uE uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]
abbrev Hilbert := lp (fun n => EuclideanSpace ℝ (ι n)) 2

def coord (a : Σ n, ι n) : Hilbert (ι := ι) →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : ι a.1 => ℝ) a.2).comp
    (lp.evalCLM ℝ (fun n => EuclideanSpace ℝ (ι n)) 2 a.1)

@[simp] theorem coord_apply (a : Σ n, ι n) (x : Hilbert (ι := ι)) : coord a x = x a.1 a.2 := rfl

def space (S : Set (Σ n, ι n)) : Submodule ℝ (Hilbert (ι := ι)) :=
  ⨅ a : {a // a ∉ S}, (coord a.val).ker

@[simp] theorem mem_space (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) :
    x ∈ space S ↔ ∀ a, a ∉ S → x a.1 a.2 = 0 := by
  simp [space]

theorem space_isClosed (S : Set (Σ n, ι n)) : IsClosed (space S : Set (Hilbert (ι := ι))) := by
  simp only [space, Submodule.coe_iInf]
  exact isClosed_iInter (fun a => (coord a.val).isClosed_ker)

theorem inner_eq_zero_of_disjoint {S T : Set (Σ n, ι n)} (hST : Disjoint S T)
    {x y : Hilbert (ι := ι)} (hx : x ∈ space S) (hy : y ∈ space T) : ⟪x,y⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ n, ⟪x n,y n⟫_ℝ = 0 by simp only [h, tsum_zero]
  intro n
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hs : (⟨n,a⟩ : Σ n, ι n) ∈ S
  · have ht : (⟨n,a⟩ : Σ n, ι n) ∉ T := fun ht => Set.disjoint_left.mp hST hs ht
    rw [(mem_space T y).mp hy ⟨n,a⟩ ht, inner_zero_right]
  · rw [(mem_space S x).mp hx ⟨n,a⟩ hs, inner_zero_left]

def basisVector (a : Σ n, ι n) : Hilbert (ι := ι) :=
  lp.single 2 a.1 (PiLp.single 2 a.2 (1 : ℝ))

@[simp] theorem basisVector_coord (a b : Σ n, ι n) :
    basisVector a b.1 b.2 = if a = b then 1 else 0 := by
  classical
  rcases a with ⟨n,a⟩
  rcases b with ⟨m,b⟩
  by_cases h : n = m
  · subst m
    simp [basisVector, lp.single_apply, eq_comm]
  · simp [basisVector, lp.single_apply, h, Ne.symm h]

theorem basisVector_mem {S : Set (Σ n, ι n)} {a : Σ n, ι n} (ha : a ∈ S) :
    basisVector a ∈ space S := by
  rw [mem_space]
  intro b hb
  rw [basisVector_coord, ite_eq_right]
  exact fun he => hb (he ▸ ha)

theorem space_eq_topologicalClosure_span (S : Set (Σ n, ι n)) :
    space S = (Submodule.span ℝ (basisVector '' S)).topologicalClosure := by
  classical
  apply le_antisymm
  · intro x hx
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (lp.hasSum_single (by simp) x).tendsto_sum_nat
    apply Eventually.of_forall
    intro N
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.le_topologicalClosure
    have he : lp.single 2 n (x n) =
        ∑ a : ι n, (x n a) • basisVector ⟨n,a⟩ := by
      apply lp.ext
      funext m
      apply PiLp.ext
      intro b
      change coord ⟨m,b⟩ (lp.single 2 n (x n)) = coord ⟨m,b⟩ (∑ a : ι n, (x n a) • basisVector ⟨n,a⟩)
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, coord_apply]
      have hcoord (a : ι n) : basisVector ⟨n,a⟩ m b =
          if (⟨n,a⟩ : Σ n, ι n) = ⟨m,b⟩ then 1 else 0 := basisVector_coord ⟨n,a⟩ ⟨m,b⟩
      simp only [hcoord]
      by_cases h : n = m
      · subst m
        simp [lp.single_apply]
      · simp [lp.single_apply, h, Ne.symm h]
    rw [he]
    apply Submodule.sum_mem
    intro a ha
    by_cases hs : (⟨n,a⟩ : Σ n, ι n) ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n,a⟩,hs,rfl⟩)
    · rw [(mem_space S x).mp hx ⟨n,a⟩ hs, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.topologicalClosure_minimal _ _ (space_isClosed S)
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    exact basisVector_mem ha
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

instance (S : Set (Σ n, ι n)) : CompleteSpace (space S) := (space_isClosed S).completeSpace_coe

def projection (S : Set (Σ n, ι n)) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) :=
  (space S).starProjection

theorem projection_mem (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) : projection S x ∈ space S :=
  (space S).starProjection_apply_mem x

theorem norm_projection_le (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) : ‖projection S x‖ ≤ ‖x‖ :=
  (space S).norm_starProjection_apply_le x

theorem inner_projection (S : Set (Σ n, ι n)) {x : Hilbert (ι := ι)} (hx : x ∈ space S)
    (y : Hilbert (ι := ι)) : ⟪x,projection S y⟫_ℝ = ⟪x,y⟫_ℝ := by
  rw [projection, ← Submodule.inner_starProjection_left_eq_right,
    (space S).starProjection_eq_self_iff.mpr hx]

theorem norm_projection_sq (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) :
    ‖projection S x‖^2 = ⟪x,projection S x⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  exact (inner_projection S (projection_mem S x) x).trans (real_inner_comm _ _)

theorem sum_projection_sq_le {I : Type uI} [Fintype I] (S : I → Set (Σ n, ι n))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (x : Hilbert (ι := ι)) :
    ∑ i, ‖projection (S i) x‖^2 ≤ ‖x‖^2 := by
  let v := fun i => projection (S i) x
  have hv : Pairwise (fun i j => ⟪v i,v j⟫_ℝ = 0) := by
    intro i j hij
    exact inner_eq_zero_of_disjoint (hS hij) (projection_mem (S i) x) (projection_mem (S j) x)
  have hs : ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simp_rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq _
    · intro j hj hji
      exact hv hji
    · simp
  have ht : ⟪x,∑ i, v i⟫_ℝ = ∑ i, ‖v i‖^2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (norm_projection_sq (S i) x).symm
  have he := norm_sub_sq_real x (∑ i, v i)
  rw [hs,ht] at he
  have hn := sq_nonneg ‖x-∑ i, v i‖
  dsimp [v] at hs ht he hn ⊢
  linarith
end LipschitzCounterexample.CoordinateSpaces

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace Topology
variable {E : ℕ → Type uE} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]

@[simp] theorem cutHead_apply (l n : ℕ) (x : HilbertSum E) :
    cutHead l x n = if n < l then x n else 0 := by
  classical
  change lp.evalCLM ℝ E 2 n (∑ i ∈ Finset.range l, lp.single 2 i (x i)) = _
  rw [map_sum]
  change (∑ i ∈ Finset.range l, (lp.single 2 i (x i)) n) = _
  simp [lp.single_apply]

@[simp] theorem tailCLM_coord (l n : ℕ) (x : HilbertSum E) :
    tailCLM l x n = if l ≤ n then x n else 0 := by
  rw [tailCLM_apply]
  change x n - cutHead l x n = _
  rw [cutHead_apply]
  split_ifs <;> simp_all
  omega
end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal InnerProductSpace Topology
open HilbertSlots RadialBudget SlowAngles RotatingStages Filter Set CoordinateSpaces

theorem D_local_orthogonality {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ S : I → Set (Σ n, BlockLabel n),
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ i a, a ∈ S i → l ≤ a.1) ∧
      (∀ i y, y ∈ Metric.ball (x i) r → tailCLM l (D y) ∈ space (S i)) := by
  classical
  obtain ⟨r,hr,l,hl⟩ := finite_slot_locality x hx
  let S : I → Set (Σ n, BlockLabel n) := fun i =>
    {a | l ≤ a.1 ∧ ∃ y ∈ Metric.ball (x i) r, slot a.1 y a.2 ≠ 0}
  refine ⟨r,hr,l,S,?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨n,a⟩ ⟨hn,y,hy,hya⟩ ⟨_,z,hz,hza⟩
    exact (hl i j hij n hn y hy z hz a).elim hya hza
  · intro i a ha
    exact ha.1
  · intro i y hy
    rw [mem_space]
    rintro ⟨n,a⟩ ha
    rw [tailCLM_coord]
    by_cases hn : l ≤ n
    · rw [ite_eq_left hn, D_coord]
      change (scalarSlot slot y n - ⟪slot n y,y.fst n⟫_ℝ) * slot n y a = 0
      have hz : slot n y a = 0 := by
        by_contra h
        exact ha ⟨hn,y,hy,h⟩
      rw [hz,mul_zero]
    · rw [ite_eq_right hn]
      rfl

theorem D_local_orthogonal_subspaces {I : Type uI} [Fintype I] (x : I → M) (hx : Function.Injective x) :
    ∃ r : ℝ, 0 < r ∧ ∃ l : ℕ, ∃ H : I → Submodule ℝ U,
      (∀ i, IsClosed (H i : Set U)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ H i, ∀ v ∈ H j, ⟪u,v⟫_ℝ = 0) ∧
      (∀ i u, u ∈ H i → ∀ n < l, u n = 0) ∧
      (∀ i y, y ∈ Metric.ball (x i) r → tailCLM l (D y) ∈ H i) := by
  obtain ⟨r,hr,l,S,hS,ht,hD⟩ := D_local_orthogonality x hx
  refine ⟨r,hr,l,fun i => space (S i),fun i => space_isClosed (S i),?_,?_,hD⟩
  · intro i j hij u hu v hv
    exact inner_eq_zero_of_disjoint (hS i j hij) hu hv
  · intro i u hu n hn
    apply PiLp.ext
    intro a
    exact (mem_space (S i) u).mp hu ⟨n,a⟩ (fun h => (not_le_of_gt hn) (ht i ⟨n,a⟩ h))
end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.FreeSpace
open scoped Topology NNReal
open Filter Set
variable {M : Type uM} [MetricSpace M] [Zero M]

def supported (K : Set M) : Submodule ℝ (Space M) :=
  (Submodule.span ℝ (point '' K)).topologicalClosure

theorem supported_isClosed (K : Set M) : IsClosed (supported K : Set (Space M)) :=
  Submodule.isClosed_topologicalClosure _

theorem point_mem_supported {K : Set M} {x : M} (hx : x ∈ K) : point x ∈ supported K :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x,hx,rfl⟩)

theorem supported_le_ker {K : Set M} (T : Space M →L[ℝ] ℝ)
    (hT : ∀ x ∈ K, T (point x) = 0) : supported K ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal _ _ T.isClosed_ker
  apply Submodule.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact hT x hx

theorem supported_pairing_le {K : Set M} (hK : (0 : M) ∈ K)
    (f : M → ℝ) {C L : ℝ≥0} (hf : LipschitzWith L f) (hC : LipschitzOnWith C f K)
    (μ : Space M) (hμ : μ ∈ supported K) :
    |LocalizedLinearization.test (LocalizedLinearization.normalized f hf) μ| ≤ C * ‖μ‖ := by
  obtain ⟨g,hg,hfg⟩ := hC.extend_real
  let F := LocalizedLinearization.test (LocalizedLinearization.normalized f hf)
  let G := LocalizedLinearization.test (LocalizedLinearization.normalized g hg)
  have hker : supported K ≤ (F-G).ker := by
    apply supported_le_ker
    intro x hx
    change (f x-f 0) - (g x-g 0) = 0
    rw [hfg hx,hfg hK,sub_self]
  have he : F μ = G μ := sub_eq_zero.mp (hker hμ)
  change |F μ| ≤ _
  rw [he, ← Real.norm_eq_abs]
  exact (LocalizedLinearization.norm_test_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (LocalizedLinearization.norm_normalized_le g hg) (norm_nonneg μ))

def HasCompactReduction : Prop :=
  ∀ μ : ℕ → Space M, WeakSequences.WeakNull μ → ∀ τ : ℝ, 0 < τ →
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ

end LipschitzCounterexample.FreeSpace

namespace LipschitzCounterexample.CoordinateSpaces
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

@[simp] theorem inner_basisVector_left (a : Σ n, ι n) (x : Hilbert (ι := ι)) :
    ⟪basisVector a,x⟫_ℝ = x a.1 a.2 := by
  rw [basisVector, lp.inner_single_left]
  simp [PiLp.inner_apply]

@[simp] theorem projection_coord (S : Set (Σ n, ι n)) (x : Hilbert (ι := ι)) (a : Σ n, ι n) :
    projection S x a.1 a.2 = if a ∈ S then x a.1 a.2 else 0 := by
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha]
    simpa only [inner_basisVector_left] using inner_projection S (basisVector_mem ha) x
  · rw [ite_eq_right ha]
    exact (mem_space S _).mp (projection_mem S x) a ha

def headSet (l : ℕ) : Set (Σ n, ι n) := {a | a.1 < l}
def tailSet (l : ℕ) : Set (Σ n, ι n) := {a | l ≤ a.1}
def head (l : ℕ) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) := projection (headSet l)
def tail (l : ℕ) : Hilbert (ι := ι) →L[ℝ] Hilbert (ι := ι) := projection (tailSet l)

@[simp] theorem head_coord (l n : ℕ) (a : ι n) (x : Hilbert (ι := ι)) :
    head l x n a = if n < l then x n a else 0 := by
  by_cases hn : n < l <;> simpa [head,headSet,hn] using projection_coord (headSet l) x ⟨n,a⟩
@[simp] theorem tail_coord (l n : ℕ) (a : ι n) (x : Hilbert (ι := ι)) :
    tail l x n a = if l ≤ n then x n a else 0 := by
  by_cases hn : l ≤ n <;> simpa [tail,tailSet,hn] using projection_coord (tailSet l) x ⟨n,a⟩

theorem head_add_tail (l : ℕ) (x : Hilbert (ι := ι)) : head l x + tail l x = x := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  change head l x n a + tail l x n a = x n a
  rw [head_coord,tail_coord]
  split_ifs <;> simp_all
  omega

theorem inner_head (l : ℕ) (x y : Hilbert (ι := ι)) : ⟪head l x,y⟫_ℝ = ⟪x,head l y⟫_ℝ :=
  (space (headSet l)).inner_starProjection_left_eq_right x y

theorem head_eq_sum (l : ℕ) (x : Hilbert (ι := ι)) :
    head l x = ∑ n ∈ Finset.range l, lp.single 2 n (x n) := by
  apply lp.ext
  funext n
  apply PiLp.ext
  intro a
  change head l x n a = coord ⟨n,a⟩ (∑ m ∈ Finset.range l, lp.single 2 m (x m))
  rw [head_coord,map_sum]
  simp only [coord_apply]
  by_cases hn : n < l
  · rw [ite_eq_left hn,Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp [lp.single_apply, Ne.symm hmn]
    · simp [hn]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := fun h => hn (h ▸ Finset.mem_range.mp hm)
    simp [lp.single_apply, Ne.symm hmn]

theorem head_tendsto_zero {b : ℕ → Hilbert (ι := ι)}
    (hb : ∀ a : Σ n, ι n, Tendsto (fun i => b i a.1 a.2) atTop (𝓝 0)) (l : ℕ) :
    Tendsto (fun i => head l (b i)) atTop (𝓝 0) := by
  have hn (n : ℕ) : Tendsto (fun i => b i n) atTop (𝓝 0) := by
    apply (PiLp.continuous_toLp 2 (fun _ : ι n => ℝ)).continuousAt.tendsto.comp
    exact tendsto_pi_nhds.mpr (fun a => hb ⟨n,a⟩)
  have hs (n : ℕ) : Tendsto (fun i => (lp.single 2 n (b i n) : Hilbert (ι := ι))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, lp.singleContinuousLinearMap_apply, map_zero] using ((lp.singleContinuousLinearMap ℝ (fun n => EuclideanSpace ℝ (ι n)) 2 n).continuous.tendsto 0).comp (hn n)
  simpa only [head_eq_sum, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range l) (fun n _ => hs n)

end LipschitzCounterexample.CoordinateSpaces

end

end OAI
