import OAI.Analysis.SeparableQuotients.BranchPaths

namespace OAI

noncomputable section

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- A strictly singular operator is not bounded below on any closed infinite-dimensional subspace. -/
def StrictlySingular (T : Y →L[𝕜] Z) : Prop :=
  ∀ M : Submodule 𝕜 Y, IsClosed (M : Set Y) → ¬ FiniteDimensional 𝕜 M →
    ∀ c : ℝ, 0 < c → ∃ x : M, ‖T x‖ < c*‖x‖

lemma finiteDimensional_of_ker [FiniteDimensional 𝕜 Z] (T : Y →ₗ[𝕜] Z)
    [FiniteDimensional 𝕜 T.ker] : FiniteDimensional 𝕜 Y := by
  have h : FiniteDimensional 𝕜 (Submodule.comap T (⊤ : Submodule 𝕜 Z)) := inferInstance
  rw [Submodule.comap_top] at h
  exact FiniteDimensional.of_injective (Submodule.topEquiv : (⊤ : Submodule 𝕜 Y) ≃ₗ[𝕜] Y).symm.toLinearMap
    (Submodule.topEquiv.symm.injective)

lemma exists_finite_vector_normers (F : Submodule 𝕜 Y) [FiniteDimensional 𝕜 F] :
    ∃ D : Finset (StrongDual 𝕜 Y), (∀ d ∈ D, ‖d‖ ≤ 1) ∧
      ∀ v : F, ∃ d ∈ D, ‖v‖ ≤ 2*‖d v‖ := by
  let U (d : closedBall (0 : StrongDual 𝕜 Y) 1) : Set F := {v | (1/2 : ℝ) < ‖d.1 v‖}
  have hU : ∀ d, IsOpen (U d) := fun d =>
    isOpen_lt continuous_const ((d.1.comp F.subtypeL).continuous.norm)
  have hc : sphere (0 : F) 1 ⊆ ⋃ d, U d := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    obtain ⟨d,hd,he⟩ := exists_dual_vector'' 𝕜 (v : Y)
    refine Set.mem_iUnion.mpr ⟨⟨d,by simpa only [mem_closedBall,dist_zero_right] using hd⟩,?_⟩
    change (1/2 : ℝ) < ‖d v‖
    rw [he,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    change (1/2 : ℝ) < ‖v‖
    rw [hn]; norm_num
  obtain ⟨t,ht⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U hU hc
  refine ⟨insert 0 (t.image Subtype.val),?_,?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hd
      simpa only [mem_closedBall,dist_zero_right] using d.property
  · intro v
    by_cases hv : v = 0
    · subst v; exact ⟨0,Finset.mem_insert_self _ _,by simp⟩
    have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : F := (↑‖v‖ : 𝕜)⁻¹ • v
    have hw : w ∈ sphere (0 : F) 1 := by
      simp only [w,mem_sphere,dist_zero_right,norm_smul,norm_inv,RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg v),inv_mul_cancel₀ hp.ne']
    obtain ⟨d,hd,he⟩ := Set.mem_iUnion₂.mp (ht hw)
    refine ⟨d,Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩),?_⟩
    change (1/2 : ℝ) < ‖d.1 ((↑‖v‖ : 𝕜)⁻¹ • (v : Y))‖ at he
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg v)] at he
    have hm := mul_lt_mul_of_pos_left he hp
    rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul] at hm
    linarith

/-- Finitely many exact annihilation conditions preserve infinite dimension. -/
lemma finite_annihilator (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y))
    (hI : ¬ FiniteDimensional 𝕜 M) (D : Finset (StrongDual 𝕜 Y)) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ∀ d ∈ D, d x = 0 := by
  let A : Y →L[𝕜] (D → 𝕜) := ContinuousLinearMap.pi (fun d => d.1)
  let N := M ⊓ A.ker
  refine ⟨N,inf_le_left,hM.inter A.isClosed_ker,?_,?_⟩
  · intro hn
    let : FiniteDimensional 𝕜 N := hn
    let B := A.comp M.subtypeL
    have hker : FiniteDimensional 𝕜 B.ker := by
      let L : B.ker →ₗ[𝕜] N := {
        toFun := fun x => ⟨x.1.1,⟨x.1.2,x.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      exact FiniteDimensional.of_injective L (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun y : N => (y : Y)) h)))
    exact hI (finiteDimensional_of_ker B.toLinearMap)
  · intro x hx d hd
    have he : A x = 0 := hx.2
    exact congrFun he ⟨d,hd⟩

lemma StrictlySingular.exists_unit_small (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) : ∃ x : M, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  obtain ⟨x,hx⟩ := hT M hM hI ε hε
  have hx0 : 0 < ‖x‖ := by
    by_contra hh
    have hz : ‖x‖ = 0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hz,mul_zero] at hx
    exact (not_lt_of_ge (norm_nonneg _)) hx
  refine ⟨(↑‖x‖ : 𝕜)⁻¹ • x,?_,?_⟩
  · simp only [norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hx0.ne']
  · change ‖T ((↑‖x‖ : 𝕜)⁻¹ • (x : Y))‖ < ε
    rw [map_smul,norm_smul,norm_inv,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
    exact (inv_mul_lt_iff₀ hx0).mpr (by nlinarith [hx])

end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

structure VectorNormers (u : ℕ → Y) where
  D : ℕ → Finset (StrongDual 𝕜 Y)
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2 * ‖d (∑ i ∈ Finset.range m, c i • u i)‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, d (u n) = 0

namespace VectorNormers
variable {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
lemma prefix_eval (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) {d : StrongDual 𝕜 Y} (hd : d ∈ H.D m) :
    d (∑ i ∈ Finset.range N, c i • u i) = d (∑ i ∈ Finset.range m, c i • u i) := by
  simp only [map_sum,map_smul]
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i _ hi
  rw [H.vanish m i (by simpa using hi) d hd,smul_zero]

include H in
lemma prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hm : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • u i‖ ≤ 2*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  obtain ⟨d,hd,hb⟩ := H.norming m c
  rw [← H.prefix_eval c hm hd] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left ((d.le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (H.unit m d hd) (norm_nonneg _))) (by norm_num))

include H in
lemma coefficient_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ 4*‖∑ i ∈ Finset.range N, c i • u i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • u n = (∑ i ∈ Finset.range (n+1), c i • u i) - (∑ i ∈ Finset.range n, c i • u i) := by
    rw [Finset.sum_range_succ,add_sub_cancel_left]
  have hh := norm_sub_le (∑ i ∈ Finset.range (n+1), c i • u i) (∑ i ∈ Finset.range n, c i • u i)
  rw [← he,norm_smul,hu,mul_one] at hh
  linarith

lemma linearCombination_eq_range (c : ℕ →₀ 𝕜) {N : ℕ} (hN : c.support ⊆ Finset.range N) :
    Finsupp.linearCombination 𝕜 u c = ∑ i ∈ Finset.range N, c i • u i := by
  change (∑ i ∈ c.support, c i • u i) = _
  apply Finset.sum_subset hN
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi,zero_smul]

include H in
lemma finsupp_bound (hu : ∀ n, ‖u n‖ = 1) (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ 4*‖Finsupp.linearCombination 𝕜 u c‖ := by
  obtain ⟨N,hN⟩ := (insert n c.support).exists_nat_subset_range
  rw [linearCombination_eq_range c (fun i hi => hN (Finset.mem_insert_of_mem hi))]
  exact H.coefficient_bound hu c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

include H in
lemma linearIndependent (hu : ∀ n, ‖u n‖ = 1) : LinearIndependent 𝕜 u := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have hb := H.finsupp_bound hu c n
  rw [hc,norm_zero,mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
end VectorNormers

namespace SmallRestriction

def listSpan (l : List Y) : Submodule 𝕜 Y := Submodule.span 𝕜 (l.toFinset : Set Y)
instance (l : List Y) : FiniteDimensional 𝕜 (listSpan (𝕜 := 𝕜) l) := FiniteDimensional.span_finset 𝕜 _

def listNormers (l : List Y) : Finset (StrongDual 𝕜 Y) :=
  (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose
lemma listNormers_spec (l : List Y) : (∀ d ∈ listNormers (𝕜 := 𝕜) l, ‖d‖ ≤ 1) ∧
    ∀ x ∈ listSpan (𝕜 := 𝕜) l, ∃ d ∈ listNormers (𝕜 := 𝕜) l, ‖x‖ ≤ 2*‖d x‖ := by
  have hh := (exists_finite_vector_normers (listSpan (𝕜 := 𝕜) l)).choose_spec
  exact ⟨hh.1,fun x hx => hh.2 ⟨x,hx⟩⟩

structure State (𝕜 Y : Type*) [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  vectors : List Y
  normers : Finset (StrongDual 𝕜 Y)

variable (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
  (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
  (ε : ℝ) (hε : 0 < ε)

include hT hM hI hε in
lemma exists_next (s : State 𝕜 Y) : ∃ y : Y, y ∈ M ∧ ‖y‖ = 1 ∧
    ‖T y‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧ ∀ d ∈ s.normers, d y = 0 := by
  obtain ⟨N,hNM,hNc,hNi,hNd⟩ := finite_annihilator M hM hI s.normers
  obtain ⟨y,hy,hTy⟩ := StrictlySingular.exists_unit_small T hT N hNc hNi
    (ε*(1/2 : ℝ)^(s.vectors.length+3)) (by positivity)
  exact ⟨y,hNM y.property,hy,hTy,hNd y y.property⟩

def nextVector (s : State 𝕜 Y) : Y := (exists_next T hT M hM hI ε hε s).choose
lemma nextVector_spec (s : State 𝕜 Y) : nextVector T hT M hM hI ε hε s ∈ M ∧
    ‖nextVector T hT M hM hI ε hε s‖ = 1 ∧
    ‖T (nextVector T hT M hM hI ε hε s)‖ < ε*(1/2 : ℝ)^(s.vectors.length+3) ∧
    ∀ d ∈ s.normers, d (nextVector T hT M hM hI ε hε s) = 0 :=
  (exists_next T hT M hM hI ε hε s).choose_spec

def step (s : State 𝕜 Y) : State 𝕜 Y :=
  let l := s.vectors ++ [nextVector T hT M hM hI ε hε s]
  ⟨l,s.normers ∪ listNormers l⟩

def state : ℕ → State 𝕜 Y
  | 0 => ⟨[],listNormers []⟩
  | n+1 => step T hT M hM hI ε hε (state n)

def seq (n : ℕ) : Y := nextVector T hT M hM hI ε hε (state T hT M hM hI ε hε n)

local notation "s" => state T hT M hM hI ε hε
local notation "u" => seq T hT M hM hI ε hε
lemma vectors_state (n : ℕ) : (s n).vectors = List.ofFn (fun i : Fin n => u i) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change (s n).vectors ++ [u n] = _
    rw [ih,List.ofFn_succ_last (f := fun i : Fin (n+1) => u i)]
    rfl

lemma state_length (n : ℕ) : (s n).vectors.length = n := by rw [vectors_state,List.length_ofFn]
lemma seq_spec (n : ℕ) : u n ∈ M ∧ ‖u n‖ = 1 ∧ ‖T (u n)‖ < ε*(1/2 : ℝ)^(n+3) := by
  have hh := nextVector_spec T hT M hM hI ε hε (s n)
  rw [state_length] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

lemma normers_mono : Monotone (fun n => (s n).normers) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

lemma normers_unit (n : ℕ) : ∀ d ∈ (s n).normers, ‖d‖ ≤ 1 := by
  induction n with
  | zero => exact (listNormers_spec []).1
  | succ n ih =>
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact ih d hd
    · exact (listNormers_spec _).1 d hd

lemma listNormers_subset (n : ℕ) : listNormers (s n).vectors ⊆ (s n).normers := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact Finset.subset_union_right

def normers : VectorNormers (𝕜 := 𝕜) u where
  D := fun n => (s n).normers
  unit := normers_unit T hT M hM hI ε hε
  norming := by
    intro m c
    have hx : (∑ i ∈ Finset.range m, c i • u i) ∈ listSpan (𝕜 := 𝕜) (s m).vectors := by
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      apply Submodule.subset_span
      rw [Finset.mem_coe,List.mem_toFinset,vectors_state]
      exact List.mem_ofFn.mpr ⟨⟨i,Finset.mem_range.mp hi⟩,rfl⟩
    obtain ⟨d,hd,hb⟩ := (listNormers_spec (s m).vectors).2 _ hx
    exact ⟨d,listNormers_subset T hT M hM hI ε hε m hd,hb⟩
  vanish := by
    intro m n hmn d hd
    exact (nextVector_spec T hT M hM hI ε hε (s n)).2.2.2 d
      (normers_mono T hT M hM hI ε hε hmn hd)

end SmallRestriction
end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric Filter
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma VectorNormers.norm_small {u : ℕ → Y} (H : VectorNormers (𝕜 := 𝕜) u)
    (hu : ∀ n, ‖u n‖ = 1) (T : Y →L[𝕜] Z) (ε : ℝ) (hε : 0 ≤ ε)
    (hT : ∀ n, ‖T (u n)‖ ≤ ε*(1/2 : ℝ)^(n+3)) (c : ℕ →₀ 𝕜) :
    ‖T (Finsupp.linearCombination 𝕜 u c)‖ ≤ ε*‖Finsupp.linearCombination 𝕜 u c‖ := by
  let x := Finsupp.linearCombination 𝕜 u c
  have hc (n : ℕ) := H.finsupp_bound hu c n
  have hgeo : (∑ i ∈ c.support, (1/2 : ℝ)^i) ≤ 2 := by
    simpa only [tsum_geometric_two] using summable_geometric_two.sum_le_tsum c.support (fun i _ => by positivity)
  calc
    ‖T x‖ ≤ ∑ i ∈ c.support, ‖c i‖*‖T (u i)‖ := by
      change ‖T (∑ i ∈ c.support, c i • u i)‖ ≤ _
      rw [map_sum]
      simpa only [map_smul,norm_smul] using norm_sum_le c.support (fun i => T (c i • u i))
    _ ≤ ∑ i ∈ c.support, (4*‖x‖)*(ε*(1/2 : ℝ)^(i+3)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (hT i) (norm_nonneg _) (by positivity)
    _ = (4*‖x‖*ε*(1/2 : ℝ)^3)*(∑ i ∈ c.support, (1/2 : ℝ)^i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_add]; ring
    _ ≤ (4*‖x‖*ε*(1/2 : ℝ)^3)*2 := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = ε*‖x‖ := by ring

/-- A strictly singular operator has arbitrarily small norm on a closed infinite-dimensional subspace. -/
theorem StrictlySingular.exists_small_restriction (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ x ∈ N, ‖T x‖ ≤ ε*‖x‖ := by
  let u := SmallRestriction.seq T hT M hM hI ε hε
  have hu (n : ℕ) := SmallRestriction.seq_spec T hT M hM hI ε hε n
  let H := SmallRestriction.normers T hT M hM hI ε hε
  let A := Submodule.span 𝕜 (Set.range u)
  let N := A.topologicalClosure
  have hAM : A ≤ M := Submodule.span_le.mpr (by rintro _ ⟨n,rfl⟩; exact (hu n).1)
  refine ⟨N,closure_minimal hAM hM,Submodule.isClosed_topologicalClosure _,?_,?_⟩
  · intro hn
    let : FiniteDimensional 𝕜 N := hn
    let v (n : ℕ) : N := ⟨u n,Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))⟩
    have hv : LinearIndependent 𝕜 v := LinearIndependent.of_comp N.subtype
      (H.linearIndependent (fun n => (hu n).2.1))
    exact Module.Finite.not_linearIndependent_of_infinite v hv
  · have hc : IsClosed {x : Y | ‖T x‖ ≤ ε*‖x‖} :=
      isClosed_le T.continuous.norm (continuous_const.mul continuous_norm)
    apply closure_minimal _ hc
    intro x hx
    obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    exact H.norm_small (fun n => (hu n).2.1) T ε hε.le (fun n => (hu n).2.2.le) c

/-- Finitely many strictly singular operators admit a common closed
infinite-dimensional small restriction, including the original ambient subspace. -/
theorem exists_small_restriction_finite (D : Finset (Y →L[𝕜] Z))
    (hD : ∀ T ∈ D, StrictlySingular T)
    (M : Submodule 𝕜 Y) (hM : IsClosed (M : Set Y)) (hI : ¬ FiniteDimensional 𝕜 M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : Submodule 𝕜 Y, N ≤ M ∧ IsClosed (N : Set Y) ∧ ¬ FiniteDimensional 𝕜 N ∧
      ∀ T ∈ D, ∀ x ∈ N, ‖T x‖ ≤ ε*‖x‖ := by
  induction D using Finset.induction_on generalizing M with
  | empty => exact ⟨M,le_rfl,hM,hI,by simp⟩
  | @insert T D hTD ih =>
    obtain ⟨N,hNM,hNc,hNi,hNd⟩ := ih (fun S hS => hD S (Finset.mem_insert_of_mem hS)) M hM hI
    obtain ⟨N',hN'N,hN'c,hN'i,hN'T⟩ := StrictlySingular.exists_small_restriction T
      (hD T (Finset.mem_insert_self _ _)) N hNc hNi ε hε
    refine ⟨N',hN'N.trans hNM,hN'c,hN'i,?_⟩
    intro S hS x hx
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact hN'T x hx
    · exact hNd S hS x (hN'N hx)

end SeparableQuotient.Singular

namespace SeparableQuotient.Singular
open Set Metric
open scoped Classical Topology
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y Z W : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

lemma not_strictlySingular_iff (T : Y →L[𝕜] Z) :
    ¬ StrictlySingular T ↔ ∃ (M : Submodule 𝕜 Y), IsClosed (M : Set Y) ∧
      ¬ FiniteDimensional 𝕜 M ∧ ∃ c : ℝ, 0 < c ∧ ∀ x : M, c*‖x‖ ≤ ‖T x‖ := by
  simp only [StrictlySingular, not_forall, not_exists, not_lt, exists_prop]

lemma lowerBound_antilipschitz (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : AntilipschitzWith ⟨c⁻¹,inv_nonneg.mpr hc.le⟩ T := by
  apply T.antilipschitz_of_bound
  intro x
  change ‖x‖ ≤ c⁻¹*‖T x‖
  exact (le_inv_mul_iff₀ hc).mpr (by simpa [mul_comm] using h x)

lemma lowerBound_isClosed_range [CompleteSpace Y] (T : Y →L[𝕜] Z) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c*‖x‖ ≤ ‖T x‖) : IsClosed (Set.range T) :=
  (lowerBound_antilipschitz T c hc h).isClosed_range T.uniformContinuous

/-- A non-strictly-singular map furnishes a closed infinite-dimensional image
and a bounded lift into its original domain. -/
theorem exists_lift_of_not_strictlySingular [CompleteSpace Y] [CompleteSpace Z] (T : Y →L[𝕜] Z)
    (hT : ¬ StrictlySingular T) :
    ∃ (H : Submodule 𝕜 Z), IsClosed (H : Set Z) ∧ ¬ FiniteDimensional 𝕜 H ∧
      ∃ U : H →L[𝕜] Y, ∀ x : H, T (U x) = x := by
  obtain ⟨M,hM,hI,c,hc,h⟩ := (not_strictlySingular_iff T).mp hT
  let : CompleteSpace M := hM.completeSpace_coe
  let A := T.comp M.subtypeL
  let e := A.equivRange (lowerBound_antilipschitz A c hc h).injective
    (lowerBound_isClosed_range A c hc h)
  refine ⟨A.range,lowerBound_isClosed_range A c hc h,?_,M.subtypeL.comp e.symm.toContinuousLinearMap,?_⟩
  · intro hF
    let : FiniteDimensional 𝕜 A.range := hF
    exact hI (FiniteDimensional.of_injective e.toLinearMap e.injective)
  · intro x
    exact congrArg (fun x : A.range => (x : Z)) (e.apply_symm_apply x)

lemma StrictlySingular.comp_left (T : Y →L[𝕜] Z) (hT : StrictlySingular T)
    (S : Z →L[𝕜] W) : StrictlySingular (S.comp T) := by
  intro M hM hI c hc
  obtain ⟨x,hx⟩ := hT M hM hI (c/(‖S‖+1)) (div_pos hc (by positivity))
  refine ⟨x,?_⟩
  have hp : 0 < ‖x‖ := by
    by_contra hh
    have hz := le_antisymm (le_of_not_gt hh) (norm_nonneg x)
    rw [hz,mul_zero] at hx
    exact (not_lt_of_ge (norm_nonneg _)) hx
  have hn := S.le_opNorm (T x)
  change ‖S (T x)‖ < _
  have hs : ‖S‖/(‖S‖+1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  calc
    _ ≤ ‖S‖*‖T x‖ := hn
    _ ≤ ‖S‖*((c/(‖S‖+1))*‖x‖) := mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    _ = (‖S‖/(‖S‖+1))*(c*‖x‖) := by ring
    _ < 1*(c*‖x‖) := mul_lt_mul_of_pos_right hs (mul_pos hc hp)
    _ = _ := one_mul _

lemma StrictlySingular.comp_right [CompleteSpace X] [CompleteSpace Y]
    (T : Y →L[𝕜] Z) (hT : StrictlySingular T) (R : X →L[𝕜] Y) :
    StrictlySingular (T.comp R) := by
  by_contra hTR
  obtain ⟨M,hM,hI,c,hc,h⟩ := (not_strictlySingular_iff _).mp hTR
  let : CompleteSpace M := hM.completeSpace_coe
  let A := R.comp M.subtypeL
  have ha : ∀ x : M, (c/(‖T‖+1))*‖x‖ ≤ ‖A x‖ := by
    intro x
    have ht := T.le_opNorm (R x)
    have hh := h x
    change c*‖x‖ ≤ ‖T (R x)‖ at hh
    change (c/(‖T‖+1))*‖x‖ ≤ ‖R x‖
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < ‖T‖+1)]
    nlinarith [norm_nonneg (R x)]
  have hap : 0 < c/(‖T‖+1) := div_pos hc (by positivity)
  let e := A.equivRange (lowerBound_antilipschitz A _ hap ha).injective
    (lowerBound_isClosed_range A _ hap ha)
  have hAi : ¬ FiniteDimensional 𝕜 A.range := by
    intro hF
    let : FiniteDimensional 𝕜 A.range := hF
    exact hI (FiniteDimensional.of_injective e.toLinearMap e.injective)
  obtain ⟨y,hy⟩ := hT A.range (lowerBound_isClosed_range A _ hap ha) hAi
    (c/(‖R‖+1)) (div_pos hc (by positivity))
  obtain ⟨x,hx⟩ := y.property
  have hr := R.le_opNorm (x : X)
  have hh := h x
  have hxy : (y : Y) = R x := hx.symm
  change ‖T (y : Y)‖ < (c/(‖R‖+1))*‖(y : Y)‖ at hy
  rw [hxy] at hy
  change c*‖x‖ ≤ ‖T (R x)‖ at hh
  have hd : (c/(‖R‖+1))*‖R x‖ ≤ c*‖x‖ := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < ‖R‖+1)]
    change ‖R (x : X)‖ ≤ ‖R‖*‖x‖ at hr
    nlinarith [norm_nonneg x]
  exact (not_lt_of_ge hh) (hy.trans_le hd)

end SeparableQuotient.Singular

end

end OAI
