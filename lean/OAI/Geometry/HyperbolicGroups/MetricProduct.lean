import Mathlib
import OAI.Geometry.HyperbolicGroups.MetricHexagon

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction

namespace MetricProduct
universe u v
variable {ι : Type u} [Fintype ι] {X : ι → Type v} [∀ i, MetricSpace (X i)]

lemma dist_sq (x y : PiLp 2 X) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  have he : dist x y = Real.sqrt (∑ i, dist (x i) (y i) ^ 2) := by
    rw [PiLp.dist_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  rw [he, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

variable (h : ∀ i, CATZero (X i))

def segment (x y : PiLp 2 X) (t : ℝ) : PiLp 2 X :=
  WithLp.toLp 2 (fun i => CATZero.segment (h i) (x i) (y i) t)

omit [Fintype ι] in
lemma segment_apply (x y : PiLp 2 X) (t : ℝ) (i : ι) :
    segment h x y t i = CATZero.segment (h i) (x i) (y i) t := rfl

omit [Fintype ι] in
lemma segment_zero (x y : PiLp 2 X) : segment h x y 0 = x := by
  ext i
  exact (CATZero.segment_spec (h i) _ _).1

omit [Fintype ι] in
lemma segment_one (x y : PiLp 2 X) : segment h x y 1 = y := by
  ext i
  exact (CATZero.segment_spec (h i) _ _).2.1

lemma segment_dist (x y : PiLp 2 X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y s) (segment h x y t) = |s - t| * dist x y := by
  have he : dist (segment h x y s) (segment h x y t) ^ 2 =
      (|s - t| * dist x y) ^ 2 := by
    rw [dist_sq, mul_pow, dist_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [segment_apply, segment_apply, CATZero.segment_dist (h i) _ _ hs ht, mul_pow]
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)).mp he

lemma segment_cn (x y z : PiLp 2 X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist z (segment h x y t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  simp only [dist_sq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => CATZero.segment_cn (h i) _ _ _ ht

include h
/-- Finite L2 products preserve CAT(0), by summing the coordinate CN comparisons. -/
theorem catZero : CATZero (PiLp 2 X) := by
  intro x y
  exact ⟨segment h x y, ⟨segment_zero h x y, segment_one h x y,
    fun _ hs _ ht => segment_dist h x y hs ht⟩, fun z _ ht => segment_cn h x y z ht⟩

lemma apply_segment (x y : PiLp 2 X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    CATZero.segment (catZero h) x y t i = CATZero.segment (h i) (x i) (y i) t := by
  have he : segment h x y t = CATZero.segment (catZero h) x y t := by
    apply CATZero.eq_segment_of_dist (catZero h) ht
    · have hh := segment_dist h x y (s := 0) (by norm_num) ht
      rw [segment_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at hh
      exact hh
    · have hh := segment_dist h x y ht (t := 1) (by norm_num)
      rw [segment_one, abs_of_nonpos (sub_nonpos.mpr ht.2)] at hh
      simpa only [neg_sub] using hh
  exact congrArg (fun z : PiLp 2 X => z i) he.symm

end MetricProduct
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace MeanProduct
open scoped BigOperators
universe u v
variable (ι : Type u) [Fintype ι] [Nonempty ι]

def factor : ℝ := 1 / Real.sqrt (Fintype.card ι)

lemma factor_pos : 0 < factor ι := by
  unfold factor
  positivity

lemma factor_sq : factor ι ^ 2 = 1 / (Fintype.card ι : ℝ) := by
  rw [factor, div_pow, Real.sq_sqrt (by positivity), one_pow]

variable (X : ι → Type v) [∀ i, MetricSpace (X i)]

abbrev Space := MetricScale.Space (factor ι) (factor_pos ι) (PiLp 2 X)

def ofFn (x : ∀ i, X i) : Space ι X := ⟨WithLp.toLp 2 x⟩

variable {ι X}

def apply (x : Space ι X) (i : ι) : X i := x.val i

omit [∀ index, MetricSpace (X index)] in
lemma ofFn_apply (x : ∀ i, X i) (i : ι) : apply (ofFn ι X x) i = x i := rfl

lemma dist_sq (x y : Space ι X) : dist x y ^ 2 = 𝔼 i, dist (apply x i) (apply y i) ^ 2 := by
  rw [MetricScale.dist_eq, mul_pow, factor_sq, MetricProduct.dist_sq,
    Fintype.expect_eq_sum_div_card]
  exact one_div_mul_eq_div _ _

lemma dist_le_of_forall (x y : Space ι X) {R : ℝ} (hR : 0 ≤ R)
    (hxy : ∀ i, dist (apply x i) (apply y i) ≤ R) : dist x y ≤ R := by
  have he : dist x y ^ 2 ≤ R ^ 2 := by
    rw [dist_sq]
    calc
      _ ≤ 𝔼 i : ι, R ^ 2 := Finset.expect_le_expect fun i _ =>
        (sq_le_sq₀ dist_nonneg hR).mpr (hxy i)
      _ = _ := Fintype.expect_const _
  exact (sq_le_sq₀ dist_nonneg hR).mp he

variable (h : ∀ i, CATZero (X i))
include h

theorem catZero : CATZero (Space ι X) :=
  MetricScale.catZero (MetricProduct.catZero h)

lemma apply_segment (x y : Space ι X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    apply (CATZero.segment (catZero h) x y t) i =
      CATZero.segment (h i) (apply x i) (apply y i) t := by
  unfold apply
  rw [MetricScale.val_segment (MetricProduct.catZero h) x y ht,
    MetricProduct.apply_segment h _ _ ht]

end MeanProduct
end HyperbolicObstruction


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace MetricLimit
universe u
variable (U : Ultrafilter ℕ) (X : ℕ → Type u) [∀ n, MetricSpace (X n)] (o : ∀ n, X n)

/-- Uniformly bounded pointed sections of the actual varying action spaces. -/
@[ext] structure Bounded (U : Ultrafilter ℕ) (X : ℕ → Type u)
    [∀ n, MetricSpace (X n)] (o : ∀ n, X n) where
  val : ∀ n, X n
  bound : ∃ R : ℝ, ∀ n, dist (o n) (val n) ≤ R

variable {U X o}

lemma bounded_dist (x y : Bounded U X o) :
    ∃ R : ℝ, ∀ n, dist (x.val n) (y.val n) ∈ Set.Icc 0 R := by
  obtain ⟨R, hR⟩ := x.bound
  obtain ⟨S, hS⟩ := y.bound
  exact ⟨R + S, fun n => ⟨dist_nonneg, (dist_triangle (x.val n) (o n) (y.val n)).trans
    (by rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))⟩⟩

/-- Real ultrafilter distance; boundedness proves convergence rather than
assuming existence of a limiting metric. -/
def preDist (x y : Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n => dist (x.val n) (y.val n))

lemma tendsto_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) (U : Filter ℕ) (𝓝 (preDist x y)) := by
  obtain ⟨R, hR⟩ := bounded_dist x y
  have hh := isCompact_Icc.ultrafilter_le_nhds' (U.map (fun n => dist (x.val n) (y.val n)))
    (show Set.Icc (0 : ℝ) R ∈ U.map (fun n => dist (x.val n) (y.val n)) from
      by
        change ∀ᶠ n in (U : Filter ℕ), dist (x.val n) (y.val n) ∈ Set.Icc (0 : ℝ) R
        exact Filter.Eventually.of_forall hR)
  obtain ⟨a, ha, ht⟩ := hh
  exact tendsto_nhds_limUnder ⟨a, ht⟩

instance : PseudoMetricSpace (Bounded U X o) where
  dist := preDist
  dist_self x := by
    exact tendsto_nhds_unique (tendsto_dist x x) (by simpa only [dist_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) U (𝓝 0)))
  dist_comm x y := by simp only [preDist, dist_comm]
  dist_triangle x y z := le_of_tendsto_of_tendsto (tendsto_dist x z)
    ((tendsto_dist x y).add (tendsto_dist y z))
    (Filter.Eventually.of_forall fun n => dist_triangle (x.val n) (y.val n) (z.val n))

/-- The separated metric ultralimit. Completeness is not needed for the finite
obstruction; all segment and CN comparisons are established below. -/
abbrev Space := SeparationQuotient (Bounded U X o)

def point (x : Bounded U X o) : Space (U := U) (X := X) (o := o) := SeparationQuotient.mk x

lemma tendsto_point_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) U (𝓝 (dist (point x) (point y))) :=
  tendsto_dist x y

variable (h : ∀ n, CATZero (X n))

/-- Coordinate segments are clamped outside the parameter interval, so the
boundedness obligation never relies on the arbitrary extension of a segment. -/
def segment (x y : Bounded U X o) (t : ℝ) : Bounded U X o :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨fun n => CATZero.segment (h n) (x.val n) (y.val n) t, by
      obtain ⟨R, hR⟩ := x.bound
      obtain ⟨S, hS⟩ := y.bound
      refine ⟨2 * R + S, fun n => ?_⟩
      have hd : dist (x.val n) (y.val n) ≤ R + S :=
        (dist_triangle (x.val n) (o n) (y.val n)).trans (by
          rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))
      calc
        _ ≤ dist (o n) (x.val n) + dist (x.val n)
          (CATZero.segment (h n) (x.val n) (y.val n) t) := dist_triangle _ _ _
        _ = dist (o n) (x.val n) + t * dist (x.val n) (y.val n) := by
          rw [CATZero.segment_left (h n) _ _ ht]
        _ ≤ R + dist (x.val n) (y.val n) := add_le_add (hR n)
          (mul_le_of_le_one_left dist_nonneg ht.2)
        _ ≤ 2 * R + S := by linarith⟩
  else x

lemma segment_val (x y : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (segment h x y t).val n = CATZero.segment (h n) (x.val n) (y.val n) t := by
  simp only [segment, dite_eq_left ht]

lemma segment_zero (x y : Bounded U X o) : segment h x y 0 = x := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).1

lemma segment_one (x y : Bounded U X o) : segment h x y 1 = y := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).2.1

lemma segment_dist (x y : Bounded U X o) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point (segment h x y s)) (point (segment h x y t)) =
      |s - t| * dist (point x) (point y) := by
  apply tendsto_nhds_unique (tendsto_point_dist _ _)
  convert (tendsto_point_dist x y).const_mul |s - t| using 1
  funext n
  rw [segment_val h x y hs, segment_val h x y ht, CATZero.segment_dist (h n) _ _ hs ht]

lemma segment_cn (x y z : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point z) (point (segment h x y t)) ^ 2 ≤
      (1 - t) * dist (point z) (point x) ^ 2 + t * dist (point z) (point y) ^ 2 -
        t * (1 - t) * dist (point x) (point y) ^ 2 := by
  apply le_of_tendsto_of_tendsto ((tendsto_point_dist z (segment h x y t)).pow 2)
    ((((tendsto_point_dist z x).pow 2).const_mul (1 - t)).add
      (((tendsto_point_dist z y).pow 2).const_mul t) |>.sub
        (((tendsto_point_dist x y).pow 2).const_mul (t * (1 - t))))
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [segment_val h x y ht]
  exact CATZero.segment_cn (h n) _ _ _ ht

include h

/-- CAT(0) comparison survives this metric ultralimit, proved directly from CN
and the convergence of every bounded pair of coordinate sections. -/
theorem catZero : CATZero (Space (U := U) (X := X) (o := o)) := by
  intro x y
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  refine ⟨fun t => point (segment h x y t), ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [segment_zero]
    rfl
  · dsimp only
    rw [segment_one]
    rfl
  · exact fun s hs t ht => segment_dist h x y hs ht
  · intro z t ht
    obtain ⟨z, rfl⟩ := SeparationQuotient.surjective_mk z
    exact segment_cn h x y z ht

/-- Uniqueness identifies actual chosen limit segments, not just their endpoints. -/
lemma point_segment (x y : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    point (segment h x y t) = CATZero.segment (catZero h) (point x) (point y) t := by
  apply CATZero.eq_segment_of_dist (catZero h) ht
  · have he := segment_dist h x y (s := 0) (by norm_num) ht
    rw [segment_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at he
    exact he
  · have he := segment_dist h x y ht (t := 1) (by norm_num)
    rw [segment_one, abs_of_nonpos (sub_nonpos.mpr ht.2)] at he
    simpa only [neg_sub] using he

end MetricLimit
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology

/-- A one-sided error estimate suffices; the action-dependent errors need not
converge, and no illicit interchange of angle and ultralimit is used. -/
theorem le_of_tendsto_upper_error {α : Type*} {l : Filter α} [l.NeBot]
    {f g e : α → ℝ} {a b : ℝ} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b))
    (he : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, e n < ε)
    (hfg : ∀ᶠ n in l, f n ≤ g n + e n) : a ≤ b := by
  by_contra hab
  have hab' : b < a := lt_of_not_ge hab
  have hε : 0 < (a - b) / 2 := by linarith
  have hb : a ≤ b + (a - b) / 2 :=
    le_of_tendsto_of_tendsto hf (hg.add_const ((a - b) / 2)) (by
      filter_upwards [he _ hε, hfg] with n hn hfn
      exact hfn.trans (add_le_add_right hn.le _))
  linarith

namespace MetricLimit
universe u
variable {U : Ultrafilter ℕ} {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}

lemma tendsto_point_dist_sq (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n) ^ 2) U (𝓝 (dist (point x) (point y) ^ 2)) :=
  (tendsto_point_dist x y).pow 2

lemma dist_sq_eq_of_tendsto (hU : (U : Filter ℕ) ≤ atTop) (x y : Bounded U X o)
    {a : ℝ} (ha : Tendsto (fun n => dist (x.val n) (y.val n) ^ 2) atTop (𝓝 a)) :
    dist (point x) (point y) ^ 2 = a :=
  tendsto_nhds_unique (tendsto_point_dist_sq x y) (ha.mono_left hU)

lemma lower_of_eventually (hU : (U : Filter ℕ) ≤ atTop) (x y : Bounded U X o) {a : ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a - ε ≤ dist (x.val n) (y.val n) ^ 2) :
    a ≤ dist (point x) (point y) ^ 2 := by
  by_contra hn
  have he : 0 < (a - dist (point x) (point y) ^ 2) / 2 := by linarith
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_point_dist_sq x y) (hU (ha _ he))
  linarith

end MetricLimit
end HyperbolicObstruction



noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace MetricScale
universe u
variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

def isometryEquiv (e : X ≃ᵢ X) : Space r hr X ≃ᵢ Space r hr X where
  toFun x := ⟨e x.val⟩
  invFun x := ⟨e.symm x.val⟩
  left_inv x := by ext; exact e.symm_apply_apply _
  right_inv x := by ext; exact e.apply_symm_apply _
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change r * dist (e x.val) (e y.val) = r * dist x.val y.val
    rw [e.isometry.dist_eq]

def action {G : Type*} [Group G] (A : G →* (X ≃ᵢ X)) :
    G →* (Space r hr X ≃ᵢ Space r hr X) where
  toFun g := isometryEquiv (A g)
  map_one' := by ext x; change A 1 x.val = x.val; simp
  map_mul' g k := by
    ext x
    change A (g * k) x.val = A g (A k x.val)
    rw [map_mul, IsometryEquiv.mul_apply]

lemma action_val {G : Type*} [Group G] (A : G →* (X ≃ᵢ X)) (g : G) (x : Space r hr X) :
    (action A g x).val = A g x.val := rfl

end MetricScale

namespace IsometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

theorem displacement_inv (A : G →* (X ≃ᵢ X)) (x : X) (g : G) :
    dist x (A g⁻¹ x) = dist x (A g x) := by
  have hh := (A g).isometry.dist_eq x (A g⁻¹ x)
  have he : A g (A g⁻¹ x) = x := by
    rw [← IsometryEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he, dist_comm] at hh
  exact hh.symm

theorem displacement_mul_le (A : G →* (X ≃ᵢ X)) (x : X) (g k : G) :
    dist x (A (g * k) x) ≤ dist x (A g x) + dist x (A k x) := by
  calc
    _ ≤ dist x (A g x) + dist (A g x) (A (g * k) x) := dist_triangle _ _ _
    _ = _ := by rw [map_mul, IsometryEquiv.mul_apply, (A g).isometry.dist_eq]

theorem displacement_prod_le (A : G →* (X ≃ᵢ X)) (x : X) (w : List G) :
    dist x (A w.prod x) ≤ (w.map (fun g => dist x (A g x))).sum := by
  induction w with
  | nil => simp
  | cons g w ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
      (displacement_mul_le A x g w.prod).trans (add_le_add le_rfl ih)

theorem six_letter_displacement_bound {α ι : Type*} [Fintype α] [Fintype ι]
    [Nonempty ι] (A : G →* (X ≃ᵢ X)) (x : X) (letter : ι → G)
    (hen : (𝔼 i, dist x (A (letter i) x) ^ 2) = 1)
    (a : G) (κ : FiniteLaw α) (row : α → Fin 5 → ι)
    (hrow : ∀ b, (List.ofFn (letter ∘ row b)).prod = a⁻¹)
    {R : ℝ} (hmarg : ∀ j i, (κ.map (fun b => row b j)).mass i ≤ R / Fintype.card ι) :
    dist x (A a x) ^ 2 ≤ 25 * R := by
  have hb : ∀ b, dist x (A a x) ^ 2 ≤ 5 * ∑ j, dist x (A (letter (row b j)) x) ^ 2 := by
    intro b
    have hp := displacement_prod_le A x (List.ofFn (letter ∘ row b))
    rw [hrow b, displacement_inv A x a, List.map_ofFn, List.sum_ofFn] at hp
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin 5 => dist x (A (letter (row b j)) x))
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hc
    have hs := (sq_le_sq₀ dist_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))).mpr hp
    exact hs.trans hc
  have hh := κ.expect_mono hb
  rw [κ.expect_const, κ.expect_mul, κ.expect_sum] at hh
  have hj : ∀ j : Fin 5, κ.expect (fun b => dist x (A (letter (row b j)) x) ^ 2) ≤ R := by
    intro j
    have he := κ.expect_map_le_uniform (fun b => row b j) (hmarg j)
      (fun i => dist x (A (letter i) x) ^ 2) (fun _ => sq_nonneg _)
    simpa only [Function.comp_def, hen, mul_one] using he
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at hs
  linarith

/-- Exact normalized displacement minimum obtained by rescaling the actual action. -/
theorem normalized_minimum [Nonempty X] [ProperSpace X] [Infinite G]
    {ι : Type*} [Fintype ι] [Nonempty ι] (A : GeometricAction G X) (letter : ι → G)
    (hgen : Subgroup.closure (Set.range letter) = ⊤) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ o : MetricScale.Space r hr X,
      (𝔼 i, dist o (MetricScale.action A.act (letter i) o) ^ 2) = 1 ∧
      ∀ y : MetricScale.Space r hr X,
        (∑ i, dist o (MetricScale.action A.act (letter i) o) ^ 2) ≤
        ∑ i, dist y (MetricScale.action A.act (letter i) y) ^ 2 := by
  obtain ⟨x, hx⟩ := A.energy_minimum letter
  let E : ℝ := 𝔼 i, dist x (A.act (letter i) x) ^ 2
  have hE : 0 < E := by
    dsimp only [E]
    rw [Fintype.expect_eq_sum_div_card]
    exact div_pos (A.energy_pos letter hgen x) (by positivity)
  let r : ℝ := 1 / Real.sqrt E
  have hr : 0 < r := one_div_pos.mpr (Real.sqrt_pos.mpr hE)
  have hrsq : r ^ 2 = 1 / E := by
    dsimp only [r]
    rw [div_pow, one_pow, Real.sq_sqrt hE.le]
  refine ⟨r, hr, ⟨x⟩, ?_, ?_⟩
  · simp only [MetricScale.dist_eq, MetricScale.action_val, mul_pow]
    rw [← Finset.mul_expect, hrsq]
    exact one_div_mul_cancel hE.ne'
  · intro y
    simp only [MetricScale.dist_eq, MetricScale.action_val, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hx y.val) (sq_nonneg r)

end IsometricAction
end HyperbolicObstruction


noncomputable section
open scoped BigOperators
open Filter Topology

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
