import OAI.Analysis.NumericalRange.MetricFeasibility

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_184 u_185 u_186 u_187

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
open Set Filter Metric Topology
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder Pointwise
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n]

local instance : ZeroLEOneClass (HermitianMatrix n) where
  zero_le_one := (zero_le_one : (0 : Matrix n n ℂ) ≤ 1)

local instance : PosSMulMono ℝ (HermitianMatrix n) where
  smul_le_smul_of_nonneg_left a ha b c hbc :=
    show a • (b : Matrix n n ℂ) ≤ a • (c : Matrix n n ℂ) from
      smul_le_smul_of_nonneg_left hbc ha

def StrictPositive (H : HermitianMatrix n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r • (1 : HermitianMatrix n) ≤ H

lemma hermitian_smul_one_le_iff (a b : ℝ) :
    a • (1 : HermitianMatrix n) ≤ b • (1 : HermitianMatrix n) ↔ a ≤ b := by
  change a • (1 : Matrix n n ℂ) ≤ b • (1 : Matrix n n ℂ) ↔ a ≤ b
  simpa only [Algebra.algebraMap_eq_smul_one] using scalarMatrix_le_iff (n := n) a b

lemma hermitian_lower_norm
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (H : HermitianMatrix n) :
    (-‖H‖) • (1 : HermitianMatrix n) ≤ H := by
  have h := IsSelfAdjoint.le_algebraMap_norm_self
    (-(H : Matrix n n ℂ)) H.property.neg
  rw [norm_neg] at h
  have hn := neg_le_neg h
  change (-‖(H : Matrix n n ℂ)‖) • (1 : Matrix n n ℂ) ≤ (H : Matrix n n ℂ)
  simpa only [map_neg, neg_neg, Algebra.algebraMap_eq_smul_one, neg_smul] using hn

lemma StrictPositive.nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H) : 0 ≤ H := by
  obtain ⟨r, hr, h⟩ := hH
  exact (smul_nonneg hr.le (zero_le_one : (0 : HermitianMatrix n) ≤ 1)).trans h

lemma strictPositive_one
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    StrictPositive (1 : HermitianMatrix n) := by
  exact ⟨1, zero_lt_one, by simp⟩

lemma StrictPositive.add_nonneg
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H K : HermitianMatrix n}
    (hH : StrictPositive H) (hK : 0 ≤ K) : StrictPositive (H + K) := by
  obtain ⟨r, hr, h⟩ := hH
  exact ⟨r, hr, h.trans (le_add_of_nonneg_right hK)⟩

lemma StrictPositive.smul
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {H : HermitianMatrix n}
    (hH : StrictPositive H)
    {a : ℝ} (ha : 0 < a) : StrictPositive (a • H) := by
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨a*r, mul_pos ha hr, ?_⟩
  simpa only [mul_smul] using smul_le_smul_of_nonneg_left h ha.le

lemma strictPositive_isOpen : IsOpen {H : HermitianMatrix n | StrictPositive H} := by
  rw [Metric.isOpen_iff]
  intro H hH
  obtain ⟨r, hr, h⟩ := hH
  refine ⟨r/2, by positivity, ?_⟩
  intro J hJ
  have hδ : ‖J-H‖ < r/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hJ
  refine ⟨r/2, by positivity, ?_⟩
  have hb := add_le_add h (hermitian_lower_norm (J-H))
  have he : H + (J-H) = J := by abel
  rw [he, ← add_smul] at hb
  apply le_trans _ hb
  apply (hermitian_smul_one_le_iff _ _).mpr
  linarith

lemma strictPositive_convex
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] :
    Convex ℝ {H : HermitianMatrix n | StrictPositive H} := by
  intro H hH K hK a b ha hb hab
  obtain ⟨r, hr, hH⟩ := hH
  obtain ⟨s, hs, hK⟩ := hK
  refine ⟨a*r+b*s, ?_, ?_⟩
  · have h₁ : 0 ≤ a*r := mul_nonneg ha hr.le
    have h₂ : 0 ≤ b*s := mul_nonneg hb hs.le
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      simpa [hb1]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hr) h₂
  · simpa only [add_smul, mul_smul] using
      add_le_add (smul_le_smul_of_nonneg_left hH ha) (smul_le_smul_of_nonneg_left hK hb)

def metricStein (T : Matrix n n ℂ) : HermitianMatrix n →ₗ[ℝ] HermitianMatrix n where
  toFun J := ⟨(J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T,
    J.property.sub (Matrix.isHermitian_conjTranspose_mul_mul T J.property)⟩
  map_add' J K := by
    apply Subtype.ext
    change (J : Matrix n n ℂ) + K - Tᴴ * ((J : Matrix n n ℂ) + K) * T =
      ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T) +
      ((K : Matrix n n ℂ) - Tᴴ * (K : Matrix n n ℂ) * T)
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a J := by
    apply Subtype.ext
    change a • (J : Matrix n n ℂ) - Tᴴ * (a • (J : Matrix n n ℂ)) * T =
      a • ((J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem exists_strict_metric {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1) :
    ∃ (τ : ℝ) (H : HermitianMatrix n),
      StrictPositive (H-1) ∧ StrictPositive (τ • 1-H) ∧ StrictPositive (metricStein T H) := by
  let J : HermitianMatrix n := ⟨steinMetric T, IsSelfAdjoint.of_nonneg (steinMetric_nonneg T)⟩
  let H : HermitianMatrix n := (2 : ℝ) • J
  have hJ : (1 : HermitianMatrix n) ≤ J := steinMetric_ge_one hT
  have hJ2 : (2 : ℝ) • (1 : HermitianMatrix n) ≤ H :=
    smul_le_smul_of_nonneg_left hJ (by norm_num)
  have hH : 1 ≤ H-1 := by
    rw [le_sub_iff_add_le]
    simpa only [two_smul ℝ] using hJ2
  have hnorm : H ≤ ‖H‖ • (1 : HermitianMatrix n) := by
    change (H : Matrix n n ℂ) ≤ ‖(H : Matrix n n ℂ)‖ • (1 : Matrix n n ℂ)
    simpa [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self (H : Matrix n n ℂ) H.property
  refine ⟨‖H‖+1, H, ⟨1, zero_lt_one, by simpa using hH⟩,
    ⟨1, zero_lt_one, ?_⟩, ?_⟩
  · rw [one_smul, le_sub_iff_add_le, add_smul, one_smul]
    simpa only [add_comm] using add_le_add_left hnorm 1
  · have hs : metricStein T H = (2 : ℝ) • (1 : HermitianMatrix n) := by
      rw [show H = (2:ℝ) • J from rfl, map_smul]
      congr 1
      apply Subtype.ext
      exact steinMetric_identity hT
    rw [hs]
    exact strictPositive_one.smul (by norm_num)

abbrev MetricDualSpace (n : Type u_185) [Fintype n] [DecidableEq n] :=
  ℝ × HermitianMatrix n × HermitianMatrix n × HermitianMatrix n

def metricLinear (T : Matrix n n ℂ) :
    (ℝ × HermitianMatrix n) →ₗ[ℝ] MetricDualSpace n where
  toFun x := (x.1, x.2, x.1 • 1-x.2, metricStein T x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk]
    congr 2
    abel_nf
  map_smul' a x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_smul,
      smul_eq_mul, Prod.smul_mk, RingHom.id_apply]

def metricOffset : MetricDualSpace n := (0,-1,0,0)
def metricAffine (T : Matrix n n ℂ) (x : ℝ × HermitianMatrix n) : MetricDualSpace n :=
  metricOffset + metricLinear T x

def metricOpen (τ : ℝ) : Set (MetricDualSpace n) :=
  {x | x.1 < τ ∧ StrictPositive x.2.1 ∧ StrictPositive x.2.2.1 ∧ StrictPositive x.2.2.2}

lemma metricOpen_isOpen (τ : ℝ) : IsOpen (metricOpen (n := n) τ) := by
  exact (isOpen_lt continuous_fst continuous_const).inter
    ((strictPositive_isOpen.preimage (continuous_fst.comp continuous_snd)).inter
      ((strictPositive_isOpen.preimage (continuous_fst.comp (continuous_snd.comp continuous_snd))).inter
        (strictPositive_isOpen.preimage (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

lemma metricOpen_convex (τ : ℝ) : Convex ℝ (metricOpen (n := n) τ) := by
  exact (convex_Iio τ).prod (strictPositive_convex.prod
    (strictPositive_convex.prod strictPositive_convex))

lemma metricAffine_range_convex
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (T : Matrix n n ℂ) :
    Convex ℝ (Set.range (metricAffine T)) := by
  have he : Set.range (metricAffine T) = (metricOffset (n := n)) +ᵥ
      ((metricLinear T).range : Set (MetricDualSpace n)) := by
    ext x
    simp only [Set.mem_range, Set.mem_vadd_set, metricAffine]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨metricLinear T y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  rw [he]
  exact (metricLinear T).range.convex.vadd _

lemma ray_slope_nonpos {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ t → a + t*b ≤ c) : b ≤ 0 := by
  by_contra hb
  have hb : 0 < b := lt_of_not_ge hb
  have ht : 0 ≤ (|c-a|+1)/b := div_nonneg (by positivity) hb.le
  have hh := h ((|c-a|+1)/b) ht
  rw [div_mul_cancel₀ _ hb.ne'] at hh
  have ha := le_abs_self (c-a)
  linarith

lemma affine_functional_constant {E : Type u_186} {F : Type u_187} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) (φ : F →ₗ[ℝ] ℝ)
    (b : F) (c : ℝ) (hc : ∀ x, c ≤ φ (b + L x)) :
    ∀ x, φ (L x) = 0 := by
  intro x
  have hn : -φ (L x) ≤ 0 := by
    apply ray_slope_nonpos (a := -φ b) (c := -c)
    intro t ht
    have hh := hc (t • x)
    simp only [map_add, map_smul, smul_eq_mul] at hh
    linarith
  have hp : φ (L x) ≤ 0 := by
    apply ray_slope_nonpos (a := -φ b) (c := -c)
    intro t ht
    have hh := hc (t • (-x))
    simp only [map_add, map_smul, map_neg, smul_eq_mul] at hh
    linarith
  linarith

lemma metricAffine_feasible
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {T : Matrix n n ℂ} {s : ℝ}
    {J : HermitianMatrix n}
    (hu : 0 ≤ (metricAffine T (s,J)).2.1)
    (hv : 0 ≤ (metricAffine T (s,J)).2.2.1)
    (hw : 0 ≤ (metricAffine T (s,J)).2.2.2) : MetricFeasible T s J := by
  change 0 ≤ -1 + J at hu
  change 0 ≤ 0 + (s • 1 - J) at hv
  rw [zero_add] at hv
  change 0 ≤ 0 + metricStein T J at hw
  rw [zero_add] at hw
  have hu' : 1 ≤ J := by
    rw [← sub_nonneg]
    simpa only [sub_eq_add_neg, add_comm] using hu
  have hv' : J ≤ s • (1 : HermitianMatrix n) := sub_nonneg.mp hv
  refine ⟨hu', ?_, ?_⟩
  · change (J : Matrix n n ℂ) ≤ s • (1 : Matrix n n ℂ) at hv'
    simpa only [Algebra.algebraMap_eq_smul_one] using hv'
  · change 0 ≤ (J : Matrix n n ℂ) - Tᴴ * (J : Matrix n n ℂ) * T at hw
    exact sub_nonneg.mp hw

lemma metric_sets_disjoint {T : Matrix n n ℂ} {τ : ℝ}
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    Disjoint (metricOpen (n := n) τ) (Set.range (metricAffine T)) := by
  rw [Set.disjoint_left]
  rintro a ha ⟨⟨s,J⟩, rfl⟩
  have hfeas := metricAffine_feasible ha.2.1.nonneg ha.2.2.1.nonneg ha.2.2.2.nonneg
  have hs : s < τ := by simpa [metricAffine, metricOffset, metricLinear] using ha.1
  exact (not_lt_of_ge (hmin s J hfeas)) hs

theorem metric_separator {T : Matrix n n ℂ} {τ : ℝ}
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ φ : StrongDual ℝ (MetricDualSpace n),
      (∀ x, φ (metricLinear T x) = 0) ∧
      (∀ o ∈ metricOpen τ, φ o < φ metricOffset) := by
  obtain ⟨φ, c, ho, ha⟩ := geometric_hahn_banach_open
    (metricOpen_convex (n := n) τ) (metricOpen_isOpen (n := n) τ) (metricAffine_range_convex T)
    (metric_sets_disjoint hmin)
  have hconst : ∀ x, φ (metricLinear T x) = 0 :=
    affine_functional_constant (metricLinear T) φ.toLinearMap metricOffset c
      (fun x => ha _ ⟨x, rfl⟩)
  refine ⟨φ, hconst, ?_⟩
  have hc : c ≤ φ metricOffset := by
    simpa only [metricAffine, map_add, hconst, add_zero] using ha _ ⟨(0,0), rfl⟩
  exact fun o ho' => (ho o ho').trans_le hc

def metricAxis0 : ℝ →ₗ[ℝ] MetricDualSpace n where
  toFun s := (s,0,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis1 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun U := (0,U,0,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis2 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun V := (0,0,V,0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def metricAxis3 : HermitianMatrix n →ₗ[ℝ] MetricDualSpace n where
  toFun W := (0,0,0,W)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma metric_functional_decompose
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (φ : StrongDual ℝ (MetricDualSpace n))
    (s : ℝ) (U V W : HermitianMatrix n) :
    φ (s,U,V,W) = s*φ (metricAxis0 1) + φ (metricAxis1 U) +
      φ (metricAxis2 V) + φ (metricAxis3 W) := by
  have he : (s,U,V,W) = s • metricAxis0 (n := n) 1 + metricAxis1 U +
      metricAxis2 V + metricAxis3 W := by
    simp [metricAxis0, metricAxis1, metricAxis2, metricAxis3]
  rw [he, map_add, map_add, map_add, map_smul, smul_eq_mul]

lemma metric_separator_nonpos {τ : ℝ} (φ : StrongDual ℝ (MetricDualSpace n))
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset)
    {U V W : HermitianMatrix n} (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    φ (0,U,V,W) ≤ 0 := by
  let b : MetricDualSpace n := (τ-1,1,1,1)
  apply ray_slope_nonpos (a := φ b) (c := φ metricOffset)
  intro t ht
  have hmem : b + t • (0,U,V,W) ∈ metricOpen τ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change τ-1 + t*0 < τ
      linarith
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hU)
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hV)
    · exact strictPositive_one.add_nonneg (smul_nonneg ht hW)
  simpa only [map_add, map_smul, smul_eq_mul] using (ho _ hmem).le

lemma metric_separator_scalar_pos {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s)
    (φ : StrongDual ℝ (MetricDualSpace n))
    (hc : ∀ x, φ (metricLinear T x) = 0)
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset) :
    0 < φ (metricAxis0 1) := by
  obtain ⟨s,H,hU,hV,hW⟩ := exists_strict_metric hT
  let U := H-1
  let V := s • (1 : HermitianMatrix n)-H
  let W := metricStein T H
  have ha : metricAffine T (s,H) = (s,U,V,W) := by
    simp [metricAffine, metricOffset, metricLinear, U, V, W, sub_eq_add_neg, add_comm]
  have hfeas : MetricFeasible T s H := by
    apply metricAffine_feasible <;> rw [ha]
    · exact hU.nonneg
    · exact hV.nonneg
    · exact hW.nonneg
  have hs : τ ≤ s := hmin s H hfeas
  have hh := ho (τ-1,U,V,W) ⟨by linarith, hU,hV,hW⟩
  have hf : φ (s,U,V,W) = φ metricOffset := by
    rw [← ha, metricAffine, map_add, hc, add_zero]
  rw [metric_functional_decompose φ] at hf hh
  have hdiff : 0 < (s-(τ-1)) * φ (metricAxis0 1) := by linarith
  have hsq : 0 < s-(τ-1) := by linarith
  exact (mul_pos_iff.mp hdiff).elim (fun h => h.2)
    (fun h => False.elim ((not_lt_of_ge hsq.le) h.1))

lemma metric_separator_limit {τ : ℝ} (φ : StrongDual ℝ (MetricDualSpace n))
    (ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset) :
    φ (τ,0,0,0) ≤ φ metricOffset := by
  have hc : Continuous (fun ε : ℝ => φ (τ-ε, ε • (1 : HermitianMatrix n),
      ε • (1 : HermitianMatrix n), ε • (1 : HermitianMatrix n))) := by fun_prop
  have ht := hc.continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      φ (τ-ε, ε • (1 : HermitianMatrix n), ε • (1 : HermitianMatrix n),
        ε • (1 : HermitianMatrix n)) ≤ φ metricOffset := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply (ho _ ?_).le
    exact ⟨sub_lt_self _ hε, strictPositive_one.smul hε,
      strictPositive_one.smul hε, strictPositive_one.smul hε⟩
  simpa using le_of_tendsto ht he

theorem metric_normalized_separator {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} {H : Matrix n n ℂ} (hfeas : MetricFeasible T τ H)
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ φ : StrongDual ℝ (MetricDualSpace n),
      φ (metricAxis0 1) = 1 ∧
      (∀ x, φ (metricLinear T x) = 0) ∧
      φ metricOffset = τ ∧
      (∀ U V W : HermitianMatrix n, 0 ≤ U → 0 ≤ V → 0 ≤ W → φ (0,U,V,W) ≤ 0) := by
  obtain ⟨ψ, hcψ, hoψ⟩ := metric_separator hmin
  have hcoeff := metric_separator_scalar_pos hT hmin ψ hcψ hoψ
  let φ : StrongDual ℝ (MetricDualSpace n) := (ψ (metricAxis0 1))⁻¹ • ψ
  have hφ (x) : φ x = (ψ (metricAxis0 1))⁻¹ * ψ x := rfl
  have hs : φ (metricAxis0 1) = 1 := by rw [hφ, inv_mul_cancel₀ hcoeff.ne']
  have hc : ∀ x, φ (metricLinear T x) = 0 := by
    intro x
    rw [hφ, hcψ, mul_zero]
  have ho : ∀ o ∈ metricOpen τ, φ o < φ metricOffset := by
    intro o ho
    rw [hφ, hφ]
    exact mul_lt_mul_of_pos_left (hoψ o ho) (inv_pos.mpr hcoeff)
  have hn : ∀ {U V W : HermitianMatrix n},
      0 ≤ U → 0 ≤ V → 0 ≤ W → φ (0,U,V,W) ≤ 0 := metric_separator_nonpos φ ho
  have hl : τ ≤ φ metricOffset := by
    have hh := metric_separator_limit φ ho
    have he : (τ,0,0,0) = τ • metricAxis0 (n := n) 1 := by simp [metricAxis0]
    simpa only [he, map_smul, hs, smul_eq_mul, mul_one] using hh
  let J : HermitianMatrix n := ⟨H, IsSelfAdjoint.of_nonneg (zero_le_one.trans hfeas.1)⟩
  have hU : 0 ≤ J-1 := by
    change (0 : Matrix n n ℂ) ≤ H-1
    exact sub_nonneg.mpr hfeas.1
  have hV : 0 ≤ τ • (1 : HermitianMatrix n)-J := by
    change 0 ≤ τ • (1 : Matrix n n ℂ) - H
    simpa only [Algebra.algebraMap_eq_smul_one, sub_nonneg] using hfeas.2.1
  have hW : 0 ≤ metricStein T J := by
    change (0 : Matrix n n ℂ) ≤ H-Tᴴ*H*T
    exact sub_nonneg.mpr hfeas.2.2
  have hneg := hn hU hV hW
  have ha : metricAffine T (τ,J) = τ • metricAxis0 1 +
      (0,J-1,τ • (1 : HermitianMatrix n)-J,metricStein T J) := by
    simp [metricAffine, metricOffset, metricLinear, metricAxis0,
      sub_eq_add_neg, add_comm]
  have hu : φ metricOffset ≤ τ := by
    have he : φ metricOffset = φ (metricAffine T (τ,J)) := by
      rw [metricAffine, map_add, hc, add_zero]
    rw [he, ha, map_add, map_smul, hs, smul_eq_mul, mul_one]
    linarith
  exact ⟨φ, hs, hc, le_antisymm hu hl, fun _ _ _ hU hV hW => hn hU hV hW⟩

@[simp] lemma hermTrace_zero_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (B : HermitianMatrix n) :
    hermTrace B 0 = 0 := by
  change (Matrix.trace ((B : Matrix n n ℂ) * 0)).re = 0
  simp
@[simp] lemma hermTrace_zero_left (B : HermitianMatrix n) : hermTrace 0 B = 0 := by
  rw [hermTrace_symm, hermTrace_zero_right]
lemma hermTrace_add_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (A B C : HermitianMatrix n) :
    hermTrace A (B+C) = hermTrace A B + hermTrace A C := by
  change (Matrix.trace ((A : Matrix n n ℂ) * ((B : Matrix n n ℂ)+(C : Matrix n n ℂ)))).re = _
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hermTrace]
lemma hermTrace_sub_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (A B C : HermitianMatrix n) :
    hermTrace A (B-C) = hermTrace A B - hermTrace A C := by
  change (Matrix.trace ((A : Matrix n n ℂ) * ((B : Matrix n n ℂ)-(C : Matrix n n ℂ)))).re = _
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hermTrace]
lemma hermTrace_smul_right
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (A B : HermitianMatrix n) (r : ℝ) :
    hermTrace A (r • B) = r * hermTrace A B := by
  change (Matrix.trace ((A : Matrix n n ℂ) * (r • (B : Matrix n n ℂ)))).re = _
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hermTrace]
lemma hermTrace_add_left (A B C : HermitianMatrix n) :
    hermTrace (A+B) C = hermTrace A C + hermTrace B C := by
  simpa only [hermTrace_symm] using hermTrace_add_right C A B
lemma hermTrace_sub_left (A B C : HermitianMatrix n) :
    hermTrace (A-B) C = hermTrace A C - hermTrace B C := by
  simpa only [hermTrace_symm] using hermTrace_sub_right C A B

lemma hermTrace_nondegenerate
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] {B : HermitianMatrix n}
    (h : ∀ A : HermitianMatrix n, hermTrace B A = 0) : B = 0 := by
  have hi : ‖toHS (B : Matrix n n ℂ)‖^2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hs_inner]
    rw [show (B : Matrix n n ℂ)ᴴ = B from B.property]
    exact h B
  have hz : toHS (B : Matrix n n ℂ) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  apply Subtype.ext
  exact congrArg fromHS hz

def metricPush (T : Matrix n n ℂ) (Z : HermitianMatrix n) : HermitianMatrix n :=
  ⟨T * (Z : Matrix n n ℂ) * Tᴴ, Matrix.isHermitian_mul_mul_conjTranspose T Z.property⟩

lemma hermTrace_stein
    {n : Type u_184} [Fintype n] [DecidableEq n] [Nonempty n] (T : Matrix n n ℂ)
    (Z J : HermitianMatrix n) :
    hermTrace Z (metricStein T J) = hermTrace (Z-metricPush T Z) J := by
  have ht : Matrix.trace ((Z : Matrix n n ℂ) * (Tᴴ * (J : Matrix n n ℂ) * T)) =
      Matrix.trace ((T * (Z : Matrix n n ℂ) * Tᴴ) * (J : Matrix n n ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  change (Matrix.trace ((Z : Matrix n n ℂ) *
    ((J : Matrix n n ℂ)-Tᴴ * (J : Matrix n n ℂ) * T))).re =
    (Matrix.trace (((Z : Matrix n n ℂ)-T*(Z : Matrix n n ℂ)*Tᴴ) * (J : Matrix n n ℂ))).re
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, ht]

theorem metric_dual_certificate {T : Matrix n n ℂ} (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} {H : HermitianMatrix n} (hfeas : MetricFeasible T τ H)
    (hmin : ∀ s J, MetricFeasible T s J → τ ≤ s) :
    ∃ X Y Z : HermitianMatrix n,
      0 ≤ (X : Matrix n n ℂ) ∧ 0 ≤ (Y : Matrix n n ℂ) ∧ 0 ≤ (Z : Matrix n n ℂ) ∧
      X-Y = Z-metricPush T Z ∧
      hermTrace X 1 = 1 ∧ hermTrace Y 1 = τ ∧
      hermTrace Y (H-1) = 0 ∧ hermTrace X (τ • 1-H) = 0 ∧
      hermTrace Z (metricStein T H) = 0 := by
  obtain ⟨φ, hs, hc, hval, hn⟩ := metric_normalized_separator hT hfeas hmin
  obtain ⟨Y,hY⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis1))
  obtain ⟨X,hX⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis2))
  obtain ⟨Z,hZ⟩ := exists_hermitian_trace_representative
    (-(φ.toLinearMap.comp metricAxis3))
  have hy (U) : φ (metricAxis1 U) = -hermTrace Y U := by
    have hh := hY U
    change -(φ (metricAxis1 U)) = _ at hh
    linarith
  have hx (V) : φ (metricAxis2 V) = -hermTrace X V := by
    have hh := hX V
    change -(φ (metricAxis2 V)) = _ at hh
    linarith
  have hz (W) : φ (metricAxis3 W) = -hermTrace Z W := by
    have hh := hZ W
    change -(φ (metricAxis3 W)) = _ at hh
    linarith
  have hYpos : 0 ≤ (Y : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff Y).mpr
    intro U hU
    have hh := hn U 0 0 hU le_rfl le_rfl
    change φ (metricAxis1 U) ≤ 0 at hh
    rw [hy] at hh
    linarith
  have hXpos : 0 ≤ (X : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff X).mpr
    intro V hV
    have hh := hn 0 V 0 le_rfl hV le_rfl
    change φ (metricAxis2 V) ≤ 0 at hh
    rw [hx] at hh
    linarith
  have hZpos : 0 ≤ (Z : Matrix n n ℂ) := by
    apply (hermTrace_nonneg_iff Z).mpr
    intro W hW
    have hh := hn 0 0 W le_rfl le_rfl hW
    change φ (metricAxis3 W) ≤ 0 at hh
    rw [hz] at hh
    linarith
  have hr (s : ℝ) (U V W : HermitianMatrix n) :
      φ (s,U,V,W) = s-hermTrace Y U-hermTrace X V-hermTrace Z W := by
    rw [metric_functional_decompose, hs, mul_one, hy, hx, hz]
    ring
  have hXone : hermTrace X 1 = 1 := by
    have hh := hc (1,0)
    change φ (1,0,(1:ℝ) • 1-0,metricStein T 0) = 0 at hh
    simp only [one_smul, sub_zero, map_zero] at hh
    rw [hr] at hh
    simp only [hermTrace_zero_right, sub_zero] at hh
    linarith
  have hYone : hermTrace Y 1 = τ := by
    change φ (0,-1,0,0) = τ at hval
    rw [hr] at hval
    have he : hermTrace Y (-1) = -hermTrace Y 1 := by
      simpa only [zero_sub, hermTrace_zero_right] using hermTrace_sub_right Y 0 1
    simp only [hermTrace_zero_right, sub_zero, he, zero_sub, neg_neg] at hval
    exact hval
  have hbalance : X-Y = Z-metricPush T Z := by
    apply sub_eq_zero.mp
    apply hermTrace_nondegenerate
    intro J
    have hh := hc (0,J)
    change φ (0,J,(0:ℝ) • 1-J,metricStein T J) = 0 at hh
    simp only [zero_smul, zero_sub] at hh
    rw [hr, hermTrace_stein] at hh
    have he : hermTrace X (-J) = -hermTrace X J := by
      simpa only [zero_sub, hermTrace_zero_right] using hermTrace_sub_right X 0 J
    rw [he] at hh
    simpa only [hermTrace_sub_left] using (show hermTrace X J-hermTrace Y J -
      (hermTrace Z J-hermTrace (metricPush T Z) J) = 0 by
        rw [hermTrace_sub_left] at hh
        linarith)
  have hU : 0 ≤ ((H-1 : HermitianMatrix n) : Matrix n n ℂ) := sub_nonneg.mpr hfeas.1
  have hV : 0 ≤ ((τ • 1-H : HermitianMatrix n) : Matrix n n ℂ) := by
    change (0 : Matrix n n ℂ) ≤ τ • 1 - (H : Matrix n n ℂ)
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hfeas.2.1
  have hW : 0 ≤ ((metricStein T H : HermitianMatrix n) : Matrix n n ℂ) :=
    sub_nonneg.mpr hfeas.2.2
  have hp := (hermTrace_nonneg_iff Y).mp hYpos (H-1) hU
  have hq := (hermTrace_nonneg_iff X).mp hXpos (τ • 1-H) hV
  have hrz := (hermTrace_nonneg_iff Z).mp hZpos (metricStein T H) hW
  have hh : φ (τ,H-1,τ • 1-H,metricStein T H) = τ := by
    have he : (τ,H-1,τ • 1-H,metricStein T H) = metricAffine T (τ,H) := by
      simp [metricAffine, metricOffset, metricLinear, sub_eq_add_neg, add_comm]
    rw [he, metricAffine, map_add, hc, add_zero, hval]
  rw [hr] at hh
  exact ⟨X,Y,Z,hXpos,hYpos,hZpos,hbalance,hXone,hYone,
    by linarith, by linarith, by linarith⟩


end CompleteCrouzeix

end

end OAI
