import OAI.Analysis.FreeGroupFactor.Reducing

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH uα uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace ConjugateSectors

 def basisAction {ι : Type uι} : FreeGroup ι →* MulAut (FreeGroup (FreeGroup ι)) where
  toFun g := FreeGroup.freeGroupCongr (Equiv.mulLeft g)
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply FreeGroup.ext_hom
    intro j
    simp [FreeGroup.freeGroupCongr_apply]
  map_mul' g h := by
    apply MulEquiv.toMonoidHom_injective
    apply FreeGroup.ext_hom
    intro j
    simp [FreeGroup.freeGroupCongr_apply, mul_assoc]

 abbrev Witness (ι : Type uι) := FreeGroup (FreeGroup ι) ⋊[basisAction] FreeGroup ι

 @[simp] theorem basisAction_of {ι : Type uι} (g j : FreeGroup ι) :
    basisAction g (FreeGroup.of j) = FreeGroup.of (g * j) := by
  simp [basisAction, FreeGroup.freeGroupCongr_apply]

 def witness {ι : Type uι} : FreeGroup (Option ι) →* Witness ι :=
  FreeGroup.lift (fun i => match i with
    | none => SemidirectProduct.inl (FreeGroup.of 1)
    | some j => SemidirectProduct.inr (FreeGroup.of j))

 @[simp] theorem witness_some {ι : Type uι} (g : FreeGroup ι) :
    witness (FreeGroup.map Option.some g) = SemidirectProduct.inr g := by
  have hh : (witness (ι := ι)).comp (FreeGroup.map Option.some) = SemidirectProduct.inr := by
    apply FreeGroup.ext_hom
    intro j
    simp [witness]
  exact DFunLike.congr_fun hh g

 @[simp] theorem witness_none {ι : Type uι} :
    witness (FreeGroup.of (none : Option ι)) = SemidirectProduct.inl (FreeGroup.of 1) := by
  simp [witness]

 def conjugate {ι : Type uι} (g : FreeGroup ι) : FreeGroup (Option ι) :=
  FreeGroup.map Option.some g * FreeGroup.of none * (FreeGroup.map Option.some g)⁻¹

 @[simp] theorem witness_conjugate {ι : Type uι} (g : FreeGroup ι) :
    witness (conjugate g) = SemidirectProduct.inl (FreeGroup.of g) := by
  simp only [conjugate, map_mul, map_inv, witness_some, witness_none]
  rw [← map_inv, ← SemidirectProduct.inl_aut, basisAction_of, mul_one]

 def begins {ι : Type uι} [DecidableEq ι] (i : ι) (g : FreeGroup ι) : Prop :=
  ∃ b w, g.toWord = (i, b) :: w

 theorem begins_unique {ι : Type uι} [DecidableEq ι] {i j : ι} {g : FreeGroup ι}
    (hi : begins i g) (hj : begins j g) : i = j := by
  obtain ⟨b, w, hi⟩ := hi
  obtain ⟨c, v, hj⟩ := hj
  rw [hi] at hj
  exact congrArg Prod.fst (List.cons.inj hj).1

 theorem reduce_prepend {ι : Type uι} [DecidableEq ι] (i : ι) (b : Bool)
    (w : List (ι × Bool)) (hw : FreeGroup.reduce w = w)
    (hhead : ∀ c v, w ≠ (i, c) :: v) (n : ℕ) :
    FreeGroup.reduce (List.replicate n (i, b) ++ w) = List.replicate n (i, b) ++ w := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, FreeGroup.reduce.cons, ih]
    cases n with
    | zero =>
      cases w with
      | nil => rfl
      | cons a v =>
        rcases a with ⟨j, c⟩
        have hij : i ≠ j := by
          intro he
          subst j
          exact hhead c v rfl
        simp [hij]
    | succ n => simp [List.replicate_succ]

 theorem begins_pow_mul {ι : Type uι} [DecidableEq ι] (i : ι) (g : FreeGroup ι)
    (hg : ¬ begins i g) (k : ℤ) (hk : k ≠ 0) : begins i ((FreeGroup.of i) ^ k * g) := by
  have hh : ∀ c v, g.toWord ≠ (i, c) :: v := by
    intro c v eq
    exact hg ⟨c, v, eq⟩
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact (hk rfl).elim
    | succ n =>
      refine ⟨true, List.replicate n (i, true) ++ g.toWord, ?_⟩
      rw [Int.ofNat_eq_natCast, zpow_natCast, FreeGroup.toWord_mul, FreeGroup.toWord_of_pow,
        reduce_prepend i true g.toWord (FreeGroup.reduce_toWord g) hh]
      simp [List.replicate_succ]
  | negSucc n =>
    refine ⟨false, List.replicate n (i, false) ++ g.toWord, ?_⟩
    rw [zpow_negSucc, FreeGroup.toWord_mul, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow]
    simp only [FreeGroup.invRev, List.reverse_replicate, List.map_replicate, Bool.not_true]
    rw [reduce_prepend i false g.toWord (FreeGroup.reduce_toWord g) hh]
    simp [List.replicate_succ]

 def sector {ι : Type uι} [DecidableEq ι] (i : FreeGroup ι) : Set (FreeGroup (Option ι)) :=
  {g | begins i (witness g).left}

 theorem sector_disjoint {ι : Type uι} [DecidableEq ι] {i j : FreeGroup ι} (hij : i ≠ j) :
    Disjoint (sector i) (sector j) := by
  rw [Set.disjoint_left]
  intro g hi hj
  exact hij (begins_unique hi hj)

 theorem sector_prefix {ι : Type uι} [DecidableEq ι] (i : FreeGroup ι)
    (g : FreeGroup (Option ι)) (hg : g ∉ sector i) (k : ℤ) (hk : k ≠ 0) :
    (conjugate i) ^ k * g ∈ sector i := by
  change begins i (witness ((conjugate i) ^ k * g)).left
  rw [map_mul, map_zpow, witness_conjugate, ← map_zpow]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply]
  exact begins_pow_mul i (witness g).left hg k hk

end ConjugateSectors

namespace CoordinateProjection

abbrev Hilbert (α : Type uα) := lp (fun _ : α => ℂ) 2

def restrict {α : Type uα} (s : Set α) (ξ : Hilbert α) : Hilbert α := by
  classical
  refine ⟨s.indicator ξ, (lp.memℓp ξ).mono' ?_⟩
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

@[simp] theorem restrict_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    restrict s ξ a = s.indicator ξ a := rfl

theorem norm_restrict_le {α : Type uα} (s : Set α) (ξ : Hilbert α) :
    ‖restrict s ξ‖ ≤ ‖ξ‖ := by
  classical
  apply lp.norm_mono (by norm_num)
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

def linearMap {α : Type uα} (s : Set α) : Hilbert α →ₗ[ℂ] Hilbert α where
  toFun := restrict s
  map_add' ξ η := by
    classical
    ext a
    by_cases ha : a ∈ s <;> simp [Set.indicator, ha]
  map_smul' c ξ := by
    classical
    ext a
    by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

def proj {α : Type uα} (s : Set α) : Hilbert α →L[ℂ] Hilbert α :=
  (linearMap s).mkContinuous 1 (fun ξ => by
    change ‖restrict s ξ‖ ≤ 1 * ‖ξ‖
    simpa only [one_mul] using norm_restrict_le s ξ)

@[simp] theorem proj_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    proj s ξ a = s.indicator ξ a := rfl

theorem norm_proj_le {α : Type uα} (s : Set α) : ‖proj s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  change ‖restrict s ξ‖ ≤ 1 * ‖ξ‖
  simpa only [one_mul] using norm_restrict_le s ξ

theorem star_proj {α : Type uα} (s : Set α) : star (proj s) = proj s := by
  classical
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

theorem proj_orthogonal {α : Type uα} (s t : Set α) (hst : Disjoint s t)
    (ξ η : Hilbert α) : inner ℂ (proj s ξ) (proj t η) = 0 := by
  classical
  rw [lp.inner_eq_tsum]
  have hz (a : α) : inner ℂ (proj s ξ a) (proj t η a) = 0 := by
    by_cases hs : a ∈ s
    · have ht : a ∉ t := fun ht => Set.disjoint_left.mp hst hs ht
      simp [Set.indicator, ht]
    · simp [Set.indicator, hs]
  simp only [hz, tsum_zero]

@[simp] theorem complement_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    ((1 - proj s) ξ) a = sᶜ.indicator ξ a := by
  classical
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

end CoordinateProjection

open scoped BigOperators
namespace FreeSum
variable {ι : Type uι} {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

omit [CompleteSpace H] in
theorem norm_sum_sq (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  have hh : inner ℂ (∑ i ∈ s, v i) (∑ i ∈ s, v i) =
      ∑ i ∈ s, inner ℂ (v i) (v i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact hv i hi j hj hji.symm
    · simp_all
  simp only [inner_self_eq_norm_sq_to_K] at hh
  exact_mod_cast hh

omit [CompleteSpace H] in

theorem norm_sum_orthogonal (s : Finset ι) (T : ι → Op) (b : ι → ℝ)
    (hT : ∀ i ∈ s, ‖T i‖ ≤ b i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y,
      inner ℂ (T i x) (T j y) = 0) :
    ‖∑ i ∈ s, T i‖ ≤ Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  simp only [sum_apply]
  have hsq := norm_sum_sq s (fun i => T i x) (fun i hi j hj hij => horth i hi j hj hij x x)
  have hle : ∑ i ∈ s, ‖T i x‖ ^ 2 ≤ (∑ i ∈ s, b i ^ 2) * ‖x‖ ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hnorm : ‖T i x‖ ≤ b i * ‖x‖ :=
      (T i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hT i hi) (norm_nonneg x))
    calc
      ‖T i x‖ ^ 2 ≤ (b i * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
      _ = b i ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
  have hsum : 0 ≤ ∑ i ∈ s, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt := Real.sq_sqrt hsum
  have hn := norm_nonneg (∑ i ∈ s, T i x)
  have hr := mul_nonneg (Real.sqrt_nonneg (∑ i ∈ s, b i ^ 2)) (norm_nonneg x)
  nlinarith

omit [CompleteSpace H] in

theorem norm_weighted_sum_orthogonal (s : Finset ι) (T : ι → Op) (k : ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hT : ∀ i ∈ s, ‖T i‖ ≤ K)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y,
      inner ℂ (T i x) (T j y) = 0) :
    ‖∑ i ∈ s, (k i : ℂ) • T i‖ ≤ K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
  have hh := norm_sum_orthogonal s (fun i => (k i : ℂ) • T i)
    (fun i => |k i| * K) (by
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hT i hi) (abs_nonneg _)) (by
      intro i hi j hj hij x y
      simp only [smul_apply, inner_smul_left, inner_smul_right,
        horth i hi j hj hij, mul_zero])
  have hs : Real.sqrt (∑ i ∈ s, (|k i| * K) ^ 2) =
      K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
    simp_rw [mul_pow, sq_abs]
    rw [← Finset.sum_mul, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sqrt_sq hK, mul_comm]
  rwa [hs] at hh

theorem three_block_bound (s : Finset ι) (P S : ι → Op) (k : ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ i ∈ s, star (P i) = P i) (hPn : ∀ i ∈ s, ‖P i‖ ≤ 1)
    (hS : ∀ i ∈ s, star (S i) = S i) (hSn : ∀ i ∈ s, ‖S i‖ ≤ K)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y,
      inner ℂ (P i x) (P j y) = 0)
    (hcompression : ∀ i ∈ s, (1 - P i) * S i * (1 - P i) = 0) :
    ‖∑ i ∈ s, (k i : ℂ) • S i‖ ≤ 3 * K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
  classical
  let A : Op := ∑ i ∈ s, (k i : ℂ) • (P i * S i)
  let D : Op := ∑ i ∈ s, (k i : ℂ) • (P i * S i * P i)
  have hPS (i : ι) (hi : i ∈ s) : ‖P i * S i‖ ≤ K := by
    calc
      ‖P i * S i‖ ≤ ‖P i‖ * ‖S i‖ := norm_mul_le _ _
      _ ≤ 1 * K := mul_le_mul (hPn i hi) (hSn i hi) (norm_nonneg _) (by norm_num)
      _ = K := one_mul _
  have hA : ‖A‖ ≤ K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
    apply norm_weighted_sum_orthogonal s _ k K hK hPS
    intro i hi j hj hij x y
    exact horth i hi j hj hij (S i x) (S j y)
  have hD : ‖D‖ ≤ K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
    apply norm_weighted_sum_orthogonal s _ k K hK
    · intro i hi
      calc
        ‖P i * S i * P i‖ ≤ ‖P i * S i‖ * ‖P i‖ := norm_mul_le _ _
        _ ≤ K * 1 := mul_le_mul (hPS i hi) (hPn i hi) (norm_nonneg _) hK
        _ = K := mul_one _
    · intro i hi j hj hij x y
      exact horth i hi j hj hij (S i (P i x)) (S j (P j y))
  have heq : (∑ i ∈ s, (k i : ℂ) • S i) = A + star A - D := by
    dsimp [A, D]
    simp only [star_sum, star_smul, star_trivial,
      star_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hP i hi, hS i hi, ← smul_add, ← smul_sub]
    congr 1
    apply sub_eq_zero.mp
    calc
      S i - (P i * S i + S i * P i - P i * S i * P i) =
          (1 - P i) * S i * (1 - P i) := by noncomm_ring
      _ = 0 := hcompression i hi
  rw [heq]
  calc
    ‖A + star A - D‖ ≤ ‖A + star A‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖star A‖) + ‖D‖ := by gcongr; exact norm_add_le _ _
    _ = 2 * ‖A‖ + ‖D‖ := by rw [norm_star]; ring
    _ ≤ 2 * (K * Real.sqrt (∑ i ∈ s, k i ^ 2)) +
        K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by gcongr
    _ = _ := by ring

end FreeSum

open scoped BigOperators ENNReal
open ConjugateSectors CoordinateProjection

 theorem operator_eq_zero_of_single {α : Type uα} [DecidableEq α]
    (T : GroupOperator α) (hT : ∀ g, T (lp.single 2 g 1) = 0) : T = 0 := by
  apply operator_matrix_ext
  intro g
  simpa only [zero_apply] using hT g

 theorem sector_compression {ι : Type uι} [DecidableEq ι] (i : FreeGroup ι)
    (T : groupVonNeumann (FreeGroup (Option ι)))
    (hsupport : ∀ g, ((T : GroupOperator _) (lp.single 2 1 1)) g ≠ 0 →
      ∃ k : ℤ, k ≠ 0 ∧ g = conjugate i ^ k) :
    (1 - proj (sector i)) * (T : GroupOperator _) * (1 - proj (sector i)) = 0 := by
  classical
  apply operator_eq_zero_of_single
  intro y
  have hQ : (1 - proj (sector i)) (lp.single 2 y 1) =
      if y ∈ sector i then 0 else lp.single 2 y 1 := by
    ext x
    by_cases hy : y ∈ sector i <;> by_cases hx : x ∈ sector i <;>
      simp_all [Set.indicator, lp.single_apply, Pi.single_apply] <;>
      intro he <;> subst x <;> contradiction
  change (1 - proj (sector i)) ((T : GroupOperator _)
    ((1 - proj (sector i)) (lp.single 2 y 1))) = 0
  rw [hQ]
  split_ifs with hy
  · simp
  · ext x
    change ((1 - proj (sector i)) ((T : GroupOperator _) (lp.single 2 y 1))) x = 0
    rw [complement_apply]
    by_cases hx : x ∈ sector i
    · simp [Set.indicator, hx]
    · simp only [Set.indicator_of_mem (Set.mem_compl hx)]
      rw [groupVN_matrix]
      by_contra hne
      obtain ⟨k, hk, he⟩ := hsupport (x * y⁻¹) (by rwa [deltaOne_eq] at hne)
      have hx' : x = conjugate i ^ k * y := by
        rw [← he, inv_mul_cancel_right]
      exact hx (hx'.symm ▸ sector_prefix i y hy k hk)

 theorem concrete_free_sum {ι : Type uι} [DecidableEq ι]
    (s : Finset (FreeGroup ι)) (T : FreeGroup ι → groupVonNeumann (FreeGroup (Option ι)))
    (k : FreeGroup ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hsa : ∀ i ∈ s, star (T i) = T i) (hn : ∀ i ∈ s, ‖T i‖ ≤ K)
    (hsupport : ∀ i ∈ s, ∀ g, ((T i : GroupOperator (FreeGroup (Option ι))) (lp.single 2 1 1)) g ≠ 0 →
      ∃ m : ℤ, m ≠ 0 ∧ g = conjugate i ^ m) :
    ‖∑ i ∈ s, (k i : ℂ) • (T i : GroupOperator (FreeGroup (Option ι)))‖ ≤
      3 * K * Real.sqrt (∑ i ∈ s, k i ^ 2) := by
  apply FreeSum.three_block_bound s (fun i => proj (sector i))
    (fun i => (T i : GroupOperator (FreeGroup (Option ι)))) k K hK
  · intro i _; exact star_proj _
  · intro i _; exact norm_proj_le _
  · intro i hi; exact congrArg Subtype.val (hsa i hi)
  · exact hn
  · intro i _ j _ hij x y
    exact proj_orthogonal _ _ (sector_disjoint hij) x y
  · intro i hi
    exact sector_compression i (T i) (hsupport i hi)

open scoped BigOperators

@[simp] theorem groupUnitary_mul {G : Type uG} [Group G] (g h : G) :
    groupUnitary (g*h) = groupUnitary g * groupUnitary h := by
  apply Subtype.ext
  exact leftRegular_mul g h

@[simp] theorem groupUnitary_inv {G : Type uG} [Group G] (g : G) :
    groupUnitary g⁻¹ = star (groupUnitary g) := by
  apply Subtype.ext
  exact (leftRegular_star g).symm

@[simp] theorem groupUnitary_one {G : Type uG} [Group G] : groupUnitary (1 : G) = 1 := by
  apply Subtype.ext
  exact leftRegular_one

def groupLaurent {G : Type uG} [Group G] (g : G) (l : ℤ →₀ ℂ) : groupVonNeumann G :=
  l.sum (fun m c => c • groupUnitary (g^m))

theorem groupLaurent_conjugate {G : Type uG} [Group G] (g c : G) (l : ℤ →₀ ℂ) :
    groupLaurent (g*c*g⁻¹) l = groupUnitary g * groupLaurent c l * star (groupUnitary g) := by
  classical
  simp only [groupLaurent, Finsupp.sum, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [conj_zpow, groupUnitary_mul, groupUnitary_mul, groupUnitary_inv]

theorem groupLaurent_coe {G : Type uG} [Group G] (c : G) (l : ℤ →₀ ℂ) :
    (groupLaurent c l : GroupOperator G) = ∑ m ∈ l.support, l m • leftRegular (c^m) := by
  change (groupVonNeumann G).subtype (∑ m ∈ l.support, l m • groupUnitary (c^m)) = _
  simp only [map_sum, map_smul]
  rfl

theorem groupLaurent_support {G : Type uG} [Group G] [DecidableEq G]
    (c : G) (l : ℤ →₀ ℂ) (h0 : l 0 = 0) (x : G)
    (hne : ((groupLaurent c l : GroupOperator G) (lp.single 2 1 1)) x ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ x = c^m := by
  classical
  by_contra! hn
  apply hne
  rw [groupLaurent_coe]
  simp only [sum_apply, smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro m hm
  have hm0 : m ≠ 0 := by
    intro he
    subst m
    exact (Finsupp.mem_support_iff.mp hm) h0
  simp [leftRegular_apply, lp.single_apply, inv_mul_eq_one, (hn m hm0).symm]

theorem centered_laurent_free_sum {ι : Type uι} [DecidableEq ι]
    (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hsa : IsSelfAdjoint (groupLaurent (FreeGroup.of (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖groupLaurent (FreeGroup.of (none : Option ι)) l‖ ≤ K)
    (k : FreeGroup ι →₀ ℝ) :
    ‖k.sum (fun g r => (r : ℂ) • groupLaurent (ConjugateSectors.conjugate g) l)‖ ≤
      3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  classical
  have he (g : FreeGroup ι) := groupLaurent_conjugate
    (FreeGroup.map Option.some g) (FreeGroup.of (none : Option ι)) l
  change ‖(groupVonNeumann (FreeGroup (Option ι))).subtype
    (∑ g ∈ k.support, (k g : ℂ) • groupLaurent (ConjugateSectors.conjugate g) l)‖ ≤ _
  simp only [map_sum, map_smul]
  apply concrete_free_sum k.support (fun g => groupLaurent (ConjugateSectors.conjugate g) l)
    k K hK
  · intro g _hg
    rw [ConjugateSectors.conjugate] at *
    rw [he, star_mul, star_mul, star_star, hsa.star_eq, mul_assoc]
  · intro g _hg
    change ‖(groupLaurent (ConjugateSectors.conjugate g) l : GroupOperator (FreeGroup (Option ι)))‖ ≤ _
    rw [ConjugateSectors.conjugate, he]
    change ‖leftRegular _ * (groupLaurent (FreeGroup.of (none : Option ι)) l :
      GroupOperator (FreeGroup (Option ι))) * star (leftRegular _)‖ ≤ _
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (leftRegular_unitary _)),
      CStarRing.norm_mem_unitary_mul _ (leftRegular_unitary _)]
    exact hn
  · intro g _hg x hx
    exact groupLaurent_support _ l h0 x hx

end

end FreeGroupFactorMain

end OAI
