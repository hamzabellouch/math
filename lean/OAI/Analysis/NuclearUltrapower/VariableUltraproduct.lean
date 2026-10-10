import Mathlib

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
namespace NuclearUltrapower

/-- A bounded scalar family has a genuine ultralimit. -/
theorem tendsto_ultralimit_of_bounded {ι : Type u} (ω : Ultrafilter ι)
    {F : Type v} [NormedAddCommGroup F] [ProperSpace F] (f : ι → F)
    (hf : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) :
    Tendsto f (ω : Filter ι) (𝓝 (limUnder (ω : Filter ι) f)) := by
  obtain ⟨C, hC⟩ := hf
  apply tendsto_nhds_limUnder
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : F) C).ultrafilter_le_nhds'
    (Ultrafilter.map f ω) (by
      change {i | f i ∈ Metric.closedBall 0 C} ∈ (ω : Filter ι)
      exact Filter.Eventually.of_forall (fun i => by simpa using hC i))
  exact ⟨x, hx⟩

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)

abbrev Seq := lp A ∞
instance : CStarAlgebra (Seq A) where

/-- Equality modulo norm-null sequences, with unrestricted varying dimensions. -/
def Rel (x y : Seq A) : Prop :=
  Tendsto (fun i => ‖x i - y i‖) (ω : Filter ι) (𝓝 0)

omit [∀ i, Nontrivial (A i)] in
private theorem null_add {x y : Seq A}
    (hx : Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0))
    (hy : Tendsto (fun i => ‖y i‖) (ω : Filter ι) (𝓝 0)) :
    Tendsto (fun i => ‖(x+y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => norm_add_le (x i) (y i))
  simpa using hx.add hy

omit [∀ i, Nontrivial (A i)] in
private theorem null_mul_left {x : Seq A}
    (hx : Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)) (y : Seq A) :
    Tendsto (fun i => ‖(x*y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => (norm_mul_le (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero y i) (norm_nonneg _)))
  simpa using hx.mul_const ‖y‖

omit [∀ i, Nontrivial (A i)] in
private theorem null_mul_right (x : Seq A) {y : Seq A}
    (hy : Tendsto (fun i => ‖y i‖) (ω : Filter ι) (𝓝 0)) :
    Tendsto (fun i => ‖(x*y) i‖) (ω : Filter ι) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => (norm_mul_le (x i) (y i)).trans
      (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero x i) (norm_nonneg _)))
  simpa using hy.const_mul ‖x‖

def con : RingCon (Seq A) where
  r := Rel A ω
  iseqv := {
    refl := fun x => by simp [Rel]
    symm := fun {x y} h => by simpa only [Rel, norm_sub_rev] using h
    trans := fun {x y z} hxy hyz => by
      have h := null_add A ω (x := x-y) (y := y-z) hxy hyz
      simpa only [Rel, sub_add_sub_cancel, lp.coeFn_sub, Pi.sub_apply] using h }
  add' := by
    intro x y z t hxy hzt
    have h := null_add A ω (x := x-y) (y := z-t) hxy hzt
    change Tendsto (fun i => ‖(x+z-(y+t)) i‖) (ω : Filter ι) (𝓝 0)
    have he : x+z-(y+t) = (x-y)+(z-t) := by abel
    rw [he]
    exact h
  mul' := by
    intro x y z t hxy hzt
    have h := null_add A ω (null_mul_left A ω (x := x-y) hxy z)
      (null_mul_right A ω y (y := z-t) hzt)
    simpa only [Rel, sub_mul, mul_sub, sub_add_sub_cancel, lp.coeFn_sub, Pi.sub_apply] using h

abbrev Algebra := (con A ω).Quotient

omit [∀ i, Nontrivial (A i)] in
private theorem rel_star {x y : Seq A} (h : Rel A ω x y) :
    Rel A ω (star x) (star y) := by
  simpa only [Rel, lp.coeFn_star, Pi.star_apply, ← star_sub, norm_star] using h

instance : Star (Algebra A ω) where
  star := Quotient.map' star (fun _ _ h => rel_star A ω h)
instance : StarRing (Algebra A ω) where
  star_involutive x := by
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_star x)
  star_mul x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_mul x y)
  star_add x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_add x y)
instance : StarModule ℂ (Algebra A ω) where
  star_smul c x := by
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_smul c x)

def mk : Seq A →⋆ₐ[ℂ] Algebra A ω where
  __ := (con A ω).mkₐ ℂ
  map_star' _ := rfl

def seqNorm (x : Seq A) : ℝ := limUnder (ω : Filter ι) (fun i => ‖x i‖)

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_tendsto (x : Seq A) :
    Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 (seqNorm A ω x)) :=
  tendsto_ultralimit_of_bounded ω _ ⟨‖x‖, fun i => by
    simpa only [Real.norm_eq_abs, abs_norm] using lp.norm_apply_le_norm ENNReal.top_ne_zero x i⟩

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_nonneg (x : Seq A) : 0 ≤ seqNorm A ω x :=
  ge_of_tendsto (seqNorm_tendsto A ω x) (Filter.Eventually.of_forall fun _ => norm_nonneg _)

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_le (x : Seq A) : seqNorm A ω x ≤ ‖x‖ :=
  le_of_tendsto (seqNorm_tendsto A ω x)
    (Filter.Eventually.of_forall (lp.norm_apply_le_norm ENNReal.top_ne_zero x))

theorem seqNorm_lipschitz : LipschitzWith 1 (seqNorm A ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply le_of_tendsto (((seqNorm_tendsto A ω x).sub (seqNorm_tendsto A ω y)).abs)
  exact Filter.Eventually.of_forall (fun i =>
    (abs_norm_sub_norm_le (x i) (y i)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero (x-y) i))

def null : Submodule ℂ (Seq A) where
  carrier := {x | Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)}
  zero_mem' := by simp
  add_mem' := null_add A ω
  smul_mem' c x hx := by
    change Tendsto (fun i => ‖(c • x) i‖) (ω : Filter ι) (𝓝 0)
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, mul_zero] using hx.const_mul ‖c‖

theorem mem_null_iff (x : Seq A) : x ∈ null A ω ↔ seqNorm A ω x = 0 := by
  constructor
  · intro hx
    exact tendsto_nhds_unique (seqNorm_tendsto A ω x) hx
  · intro hx
    change Tendsto (fun i => ‖x i‖) (ω : Filter ι) (𝓝 0)
    simpa only [hx] using seqNorm_tendsto A ω x

instance null_closed : IsClosed ((null A ω : Submodule ℂ (Seq A)) : Set (Seq A)) := by
  have he : (null A ω : Set (Seq A)) = (seqNorm A ω) ⁻¹' {0} := by
    ext x
    exact mem_null_iff A ω x
  rw [he]
  exact isClosed_singleton.preimage (seqNorm_lipschitz A ω).continuous

/-- Identification with the ordinary complete normed linear quotient. -/
def quotientEquiv : Algebra A ω ≃ₗ[ℂ] (Seq A ⧸ null A ω) :=
  LinearEquiv.ofBijective
    (show Algebra A ω →ₗ[ℂ] (Seq A ⧸ null A ω) from
    { toFun := Quotient.lift (fun x : Seq A => (Submodule.Quotient.mk x : Seq A ⧸ null A ω))
        (by intro x y h; exact (Submodule.Quotient.eq _).mpr h)
      map_add' := by
        intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y => rfl
      map_smul' := by
        intro c x
        induction x using Quotient.inductionOn with | h x => rfl })
    ⟨by
      intro x y h
      induction x using Quotient.inductionOn with | h x =>
        induction y using Quotient.inductionOn with | h y =>
          exact Quotient.sound ((Submodule.Quotient.eq _).mp h),
     by
      intro x
      obtain ⟨y, rfl⟩ := Quotient.exists_rep x
      exact ⟨mk A ω y, rfl⟩⟩

instance : NormedAddCommGroup (Algebra A ω) :=
  NormedAddCommGroup.induced _ _ (quotientEquiv A ω).toAddEquiv (quotientEquiv A ω).injective

@[simp] theorem norm_eq_quotient_norm (x : Algebra A ω) :
    ‖x‖ = ‖quotientEquiv A ω x‖ := rfl

omit [∀ i, Nontrivial (A i)] in
theorem seqNorm_eq_of_rel {x y : Seq A} (h : Rel A ω x y) :
    seqNorm A ω x = seqNorm A ω y := by
  have hd : Tendsto (fun i => ‖x i‖ - ‖y i‖) (ω : Filter ι) (𝓝 0) :=
    squeeze_zero_norm (fun i => (by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x i) (y i))) h
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((seqNorm_tendsto A ω x).sub (seqNorm_tendsto A ω y)) hd)

/-- Exact quotient norm, including the truncation upper bound. -/
theorem mk_norm (x : Seq A) : ‖mk A ω x‖ = seqNorm A ω x := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    have hr0 : 0 ≤ r := (seqNorm_nonneg A ω x).trans hr.le
    let y : Seq A := ⟨fun i => if ‖x i‖ < r then x i else 0, memℓp_infty ⟨r, by
      rintro _ ⟨i, rfl⟩
      by_cases hi : ‖x i‖ < r
      · simp [hi, hi.le]
      · simp [hi, hr0]⟩⟩
    have he : mk A ω x = mk A ω y := by
      apply Quotient.sound
      have hv : ∀ᶠ i in (ω : Filter ι), ‖x i - y i‖ = 0 := by
        filter_upwards [(seqNorm_tendsto A ω x).eventually (gt_mem_nhds hr)] with i hi
        simp [y, hi]
      exact tendsto_const_nhds.congr' (hv.mono fun _ h => h.symm)
    rw [he, norm_eq_quotient_norm]
    apply (Submodule.Quotient.norm_mk_le (null A ω) y).trans
    apply lp.norm_le_of_forall_le hr0
    intro i
    change ‖(if ‖x i‖ < r then x i else 0 : A i)‖ ≤ r
    by_cases hi : ‖x i‖ < r
    · simp [hi, hi.le]
    · simp [hi, hr0]
  · change seqNorm A ω x ≤ ‖(Submodule.Quotient.mk x : Seq A ⧸ null A ω)‖
    apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have hr : Rel A ω y x := (Submodule.Quotient.eq _).mp hy
    rw [← seqNorm_eq_of_rel A ω hr]
    exact seqNorm_le A ω y

instance : NormedRing (Algebra A ω) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        change ‖mk A ω (x*y)‖ ≤ ‖mk A ω x‖ * ‖mk A ω y‖
        simp only [mk_norm]
        exact le_of_tendsto_of_tendsto (seqNorm_tendsto A ω (x*y))
          ((seqNorm_tendsto A ω x).mul (seqNorm_tendsto A ω y))
          (Filter.Eventually.of_forall fun i => norm_mul_le (x i) (y i))
instance : NormedAlgebra ℂ (Algebra A ω) where
  norm_smul_le c x := by
    induction x using Quotient.inductionOn with | h x =>
      change ‖mk A ω (c • x)‖ ≤ ‖c‖ * ‖mk A ω x‖
      simp only [mk_norm]
      exact le_of_tendsto_of_tendsto (seqNorm_tendsto A ω (c • x))
        (tendsto_const_nhds.mul (seqNorm_tendsto A ω x))
        (Filter.Eventually.of_forall fun i => norm_smul_le c (x i))
instance : CStarRing (Algebra A ω) where
  norm_mul_self_le x := by
    induction x using Quotient.inductionOn with | h x =>
      change ‖mk A ω x‖ * ‖mk A ω x‖ ≤ ‖mk A ω (star x * x)‖
      simp only [mk_norm]
      exact le_of_tendsto_of_tendsto
        ((seqNorm_tendsto A ω x).mul (seqNorm_tendsto A ω x))
        (seqNorm_tendsto A ω (star x * x))
        (Filter.Eventually.of_forall fun i => (CStarRing.norm_star_mul_self (x := x i)).ge)

def quotientIsometry : Algebra A ω ≃ₗᵢ[ℂ] (Seq A ⧸ null A ω) where
  __ := quotientEquiv A ω
  norm_map' _ := rfl
instance : CompleteSpace (Algebra A ω) :=
  (quotientIsometry A ω).toIsometryEquiv.completeSpace_iff.mpr inferInstance
instance : CStarAlgebra (Algebra A ω) where
instance : Nontrivial (Algebra A ω) := by
  apply nontrivial_of_ne (1 : Algebra A ω) 0
  intro h
  have hn : ‖(1 : Algebra A ω)‖ = 1 := by
    change ‖mk A ω 1‖ = 1
    rw [mk_norm]
    exact tendsto_nhds_unique (seqNorm_tendsto A ω 1) (by
      change Tendsto (fun i : ι => ‖(1 : A i)‖) (ω : Filter ι) (𝓝 1)
      simpa only [norm_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) (ω : Filter ι) (𝓝 1)))
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower
namespace VariableUltra
open scoped WithCStarModule

/-- A dimension-controlled bound for the C*-matrix norm, independent of the
entry algebra. This also proves continuity for bounded varying-algebra families. -/
theorem matrix_norm_le_sum {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {n : Type*} [Fintype n]
    (M : CStarMatrix n n A) : ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  classical
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]

local instance entryOrder (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance entryStarOrder (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
local instance quotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance quotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

/-- One entry of a bounded family of matrices is a bounded family. -/
def matrixEntry (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) : Seq A :=
  ⟨fun i => M i j k, memℓp_infty ⟨‖M‖, by
    rintro _ ⟨i, rfl⟩
    exact CStarMatrix.norm_entry_le_norm.trans (lp.norm_apply_le_norm ENNReal.top_ne_zero M i)⟩⟩

omit [∀ i, Nontrivial (A i)] [Nonempty n] in
@[simp] theorem matrixEntry_apply (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) (i : ι) :
    matrixEntry A n M j k i = M i j k := rfl

/-- Assemble a finite matrix of bounded families. There is no bound on the
dimension of any of the entry algebras. -/
def matrixFamily (M : CStarMatrix n n (Seq A)) : Seq (fun i => CStarMatrix n n (A i)) :=
  ⟨fun i => CStarMatrix.ofMatrix (fun j k => M j k i), memℓp_infty
    ⟨∑ k, ∑ j, ‖M j k‖, by
      rintro _ ⟨i, rfl⟩
      apply (matrix_norm_le_sum _).trans
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (M j k) i⟩⟩

omit [∀ i, Nontrivial (A i)] [Nonempty n] in
@[simp] theorem matrixFamily_apply (M : CStarMatrix n n (Seq A)) (i : ι) (j k : n) :
    matrixFamily A n M i j k = M j k i := rfl

/-- Pass to the ultraproduct in every matrix entry. -/
def matrixQuotient : Algebra (fun i => CStarMatrix n n (A i)) ω →⋆ₐ[ℂ]
    CStarMatrix n n (Algebra A ω) where
  toFun := Quotient.lift
    (fun M => CStarMatrix.ofMatrix (fun j k => mk A ω (matrixEntry A n M j k)))
    (by
      intro M N h
      apply CStarMatrix.ext
      intro j k
      apply Quotient.sound
      apply squeeze_zero (fun _ => norm_nonneg _)
        (fun i => CStarMatrix.norm_entry_le_norm (M := M i - N i) (i := j) (j := k))
      exact h)
  map_zero' := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω 0 = 0
    exact map_zero _
  map_one' := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω (matrixEntry A n 1 j k) = (1 : CStarMatrix n n (Algebra A ω)) j k
    have he : matrixEntry A n 1 j k = if j = k then 1 else 0 := by
      ext i
      by_cases h : j = k <;> simp [matrixEntry, h]
    rw [he, CStarMatrix.one_apply]
    split <;> simp
  map_add' := by
    intro M N
    induction M using Quotient.inductionOn with | h M =>
      induction N using Quotient.inductionOn with | h N =>
        apply CStarMatrix.ext
        intro j k
        change mk A ω (matrixEntry A n (M+N) j k) =
          mk A ω (matrixEntry A n M j k) + mk A ω (matrixEntry A n N j k)
        have he : matrixEntry A n (M+N) j k = matrixEntry A n M j k + matrixEntry A n N j k := rfl
        rw [he, map_add]
  map_mul' := by
    intro M N
    induction M using Quotient.inductionOn with | h M =>
      induction N using Quotient.inductionOn with | h N =>
        apply CStarMatrix.ext
        intro j k
        change mk A ω (matrixEntry A n (M*N) j k) = ∑ l, _
        have he : matrixEntry A n (M*N) j k =
            ∑ l, matrixEntry A n M j l * matrixEntry A n N l k := by
          ext i
          change (M i * N i) j k = _
          rw [CStarMatrix.mul_apply]
          change (∑ l, M i j l * N i l k) =
            (∑ l, matrixEntry A n M j l * matrixEntry A n N l k) i
          rw [lp.coeFn_sum]
          change (∑ l, M i j l * N i l k) =
            (∑ l, (fun i : ι => M i j l * N i l k)) i
          rw [Finset.sum_apply]
        rw [he, map_sum]
        simp only [map_mul]
        rfl
  commutes' c := by
    apply CStarMatrix.ext
    intro j k
    change mk A ω (matrixEntry A n (algebraMap ℂ (Seq (fun i => CStarMatrix n n (A i))) c) j k) = _
    have he : matrixEntry A n (algebraMap ℂ (Seq (fun i => CStarMatrix n n (A i))) c) j k =
        if j = k then algebraMap ℂ (Seq A) c else 0 := by
      ext i
      by_cases h : j = k
      · subst k
        simp only
        change (algebraMap ℂ (CStarMatrix n n (A i)) c) j j = algebraMap ℂ (A i) c
        simp [CStarMatrix.algebraMap_apply]
      · simp only [ite_eq_right h]
        change (algebraMap ℂ (CStarMatrix n n (A i)) c) j k = 0
        simp [CStarMatrix.algebraMap_apply, h]
    rw [he, CStarMatrix.algebraMap_apply]
    split
    · exact (mk A ω).commutes c
    · exact map_zero _
  map_star' := by
    intro M
    induction M using Quotient.inductionOn with | h M =>
      apply CStarMatrix.ext
      intro j k
      change mk A ω (star (matrixEntry A n M k j)) = star (mk A ω (matrixEntry A n M k j))
      exact map_star _ _

@[simp] theorem matrixQuotient_mk (M : Seq (fun i => CStarMatrix n n (A i))) (j k : n) :
    matrixQuotient A ω n (mk _ ω M) j k = mk A ω (matrixEntry A n M j k) := rfl

/-- Fixed finite matrix amplification commutes with the quotient, entry by entry. -/
theorem matrixQuotient_injective : Function.Injective (matrixQuotient A ω n) := by
  intro M N h
  induction M using Quotient.inductionOn with | h M =>
    induction N using Quotient.inductionOn with | h N =>
      have he (j k : n) : Rel A ω (matrixEntry A n M j k) (matrixEntry A n N j k) := by
        change @Setoid.r _ (con A ω).toSetoid _ _
        apply Quotient.exact
        exact congrArg (fun q : CStarMatrix n n (Algebra A ω) => q j k) h
      apply Quotient.sound
      apply squeeze_zero (fun _ => norm_nonneg _) (fun i => matrix_norm_le_sum (M i - N i))
      have ht := tendsto_finsetSum Finset.univ (fun k _ =>
        tendsto_finsetSum Finset.univ (fun j _ => he j k))
      simpa only [Rel, matrixEntry_apply, Finset.sum_const_zero, CStarMatrix.sub_apply] using ht

theorem matrixQuotient_surjective : Function.Surjective (matrixQuotient A ω n) := by
  intro M
  have hex (j k : n) : ∃ x : Seq A, mk A ω x = M j k := by
    obtain ⟨x, hx⟩ := Quotient.exists_rep (M j k)
    exact ⟨x, hx⟩
  choose x hx using hex
  refine ⟨mk _ ω (matrixFamily A n (CStarMatrix.ofMatrix x)), ?_⟩
  apply CStarMatrix.ext
  intro j k
  change mk A ω (matrixEntry A n (matrixFamily A n (CStarMatrix.ofMatrix x)) j k) = _
  have he : matrixEntry A n (matrixFamily A n (CStarMatrix.ofMatrix x)) j k = x j k := by
    ext i
    rfl
  rw [he, hx]

/-- No matrix norm is lost in the entrywise quotient identification. -/
theorem matrixQuotient_norm (M : Algebra (fun i => CStarMatrix n n (A i)) ω) :
    ‖matrixQuotient A ω n M‖ = ‖M‖ :=
  NonUnitalStarAlgHom.norm_map _ (matrixQuotient_injective A ω n) M

/-- This is the norm-ultrafilter version of the fixed-size amplification
identity in the tensor-norm formulation. -/
def matrixQuotientEquiv : Algebra (fun i => CStarMatrix n n (A i)) ω ≃⋆ₐ[ℂ]
    CStarMatrix n n (Algebra A ω) :=
  StarAlgEquiv.ofBijective (matrixQuotient A ω n)
    ⟨matrixQuotient_injective A ω n, matrixQuotient_surjective A ω n⟩

end VariableUltra
end NuclearUltrapower

namespace NuclearUltrapower

/-- Entrywise amplification of a unital star homomorphism. -/
def matrixMap {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (n : Type*) [Fintype n] [DecidableEq n] (f : A →⋆ₐ[ℂ] B) :
    CStarMatrix n n A →⋆ₐ[ℂ] CStarMatrix n n B where
  toFun := CStarMatrix.mapₙₐ f.toNonUnitalStarAlgHom
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' := map_star _
  map_one' := by
    ext i j
    change f ((1 : CStarMatrix n n A) i j) = (1 : CStarMatrix n n B) i j
    simp only [CStarMatrix.one_apply]
    split <;> simp
  commutes' c := by
    ext i j
    change f ((algebraMap ℂ (CStarMatrix n n A) c) i j) =
      (algebraMap ℂ (CStarMatrix n n B) c) i j
    simp only [CStarMatrix.algebraMap_apply]
    split
    · exact f.commutes c
    · exact map_zero _

@[simp] theorem matrixMap_apply {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    {n : Type*} [Fintype n] [DecidableEq n] (f : A →⋆ₐ[ℂ] B)
    (M : CStarMatrix n n A) (i j : n) : matrixMap n f M i j = f (M i j) := rfl

namespace VariableUltra
variable {ι : Type u} (A : ι → Type v) [∀ i, CStarAlgebra (A i)]
  [∀ i, Nontrivial (A i)] (ω : Ultrafilter ι)
variable (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
local instance normEntryOrder (i : ι) : PartialOrder (A i) := CStarAlgebra.spectralOrder _
local instance normEntryStarOrder (i : ι) : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
local instance seqOrder : PartialOrder (Seq A) := CStarAlgebra.spectralOrder _
local instance seqStarOrder : StarOrderedRing (Seq A) := CStarAlgebra.spectralOrderedRing _
local instance normQuotientOrder : PartialOrder (Algebra A ω) := CStarAlgebra.spectralOrder _
local instance normQuotientStarOrder : StarOrderedRing (Algebra A ω) := CStarAlgebra.spectralOrderedRing _

@[simp] theorem matrixQuotient_matrixFamily (M : CStarMatrix n n (Seq A)) :
    matrixQuotient A ω n (mk _ ω (matrixFamily A n M)) = matrixMap n (mk A ω) M := by
  apply CStarMatrix.ext
  intro j k
  rfl

/-- The norm of each FIXED finite matrix over the quotient is its coordinate
ultralimit. The entry algebras and their dimensions are unrestricted. -/
theorem matrixMap_mk_norm (M : CStarMatrix n n (Seq A)) :
    ‖matrixMap n (mk A ω) M‖ =
      seqNorm (fun i => CStarMatrix n n (A i)) ω (matrixFamily A n M) := by
  rw [← matrixQuotient_matrixFamily, matrixQuotient_norm, mk_norm]

/-- Finite exceptional coordinates can be discarded before amplification. -/
theorem matrixMap_mk_norm_le (M : CStarMatrix n n (Seq A)) {C : ℝ}
    (h : ∀ᶠ i in (ω : Filter ι), ‖matrixFamily A n M i‖ ≤ C) :
    ‖matrixMap n (mk A ω) M‖ ≤ C := by
  rw [matrixMap_mk_norm]
  exact le_of_tendsto (seqNorm_tendsto _ ω _) h

end VariableUltra
end NuclearUltrapower

end
end
end
end

end OAI
