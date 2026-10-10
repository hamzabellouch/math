import Mathlib

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

abbrev E := algebraicClosure ℚ ℂ

def K : Subgroup Circle where
  carrier := {u | IsAlgebraic ℚ (u : ℂ)}
  one_mem' := by simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  mul_mem' := by intro a b ha hb; exact ha.mul hb
  inv_mem' := by intro a ha; exact ha.inv

theorem K_pow_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun u : K => u ^ n) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.val : ℂ) (Nat.pos_of_ne_zero hn)
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) (by
    rw [hz]; exact u.property)
  have hnrm : ‖z‖ = 1 := by
    have hpow : ‖z‖ ^ n = (1 : ℝ) ^ n := by
      simp only [← norm_pow, hz, Circle.norm_coe, one_pow]
    exact (pow_left_inj₀ (norm_nonneg z) zero_le_one hn).mp hpow
  refine ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hnrm⟩, ha⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hz

instance K_rootable : RootableBy K ℕ := rootableByOfPowLeftSurj K ℕ (fun {n} hn => K_pow_surjective n hn)

/-- The group-theoretic step behind the zero-mass coset argument. -/
theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

/-- A separate synonym ensures that the dual uses the discrete topology,
not the Euclidean topology inherited by the embedded algebraic field. -/
def DiscreteE := Multiplicative E deriving CommGroup
instance : TopologicalSpace DiscreteE := ⊥
instance : DiscreteTopology DiscreteE := ⟨rfl⟩
instance : IsTopologicalGroup DiscreteE := inferInstance
abbrev D := PontryaginDual DiscreteE

example : CompactSpace D := inferInstance
example : CommGroup D := inferInstance

instance E_countable : Countable E := by
  apply Set.Countable.to_subtype
  have heq : (algebraicClosure ℚ ℂ : Set ℂ) = {x | IsAlgebraic ℚ x} := by
    ext z; exact mem_algebraicClosure_iff
  rw [heq]
  exact Algebraic.countable ℚ ℂ

instance : Countable DiscreteE := inferInstanceAs (Countable E)

instance : SecondCountableTopology D :=
  ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.secondCountableTopology

/-- The inclusion into the usual complex plane, with no continuity assertion
needed on its discrete domain. -/
def embed (z : DiscreteE) : ℂ := ((Multiplicative.toAdd z : E) : ℂ)

@[simp] theorem embed_one : embed 1 = 0 := rfl
@[simp] theorem embed_mul (z w : DiscreteE) : embed (z * w) = embed z + embed w := rfl

/-- The manuscript's ordinary character parametrization. -/
def j (ξ : ℂ) : D where
  toFun z := Circle.exp (inner ℝ ξ (embed z))
  map_one' := by simp
  map_mul' z w := by simp only [embed_mul, inner_add_right, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem j_apply (ξ : ℂ) (z : DiscreteE) :
    j ξ z = Circle.exp (inner ℝ ξ (embed z)) := rfl

@[simp] theorem j_zero : j 0 = 1 := by
  apply PontryaginDual.ext
  intro z
  simp

@[simp] theorem j_add (ξ η : ℂ) : j (ξ + η) = j ξ * j η := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ (ξ + η) (embed z)) =
    Circle.exp (inner ℝ ξ (embed z)) * Circle.exp (inner ℝ η (embed z))
  rw [inner_add_left, Circle.exp_add]

def jHom : Multiplicative ℂ →* D where
  toFun ξ := j (Multiplicative.toAdd ξ)
  map_one' := j_zero
  map_mul' ξ η := j_add (Multiplicative.toAdd ξ) (Multiplicative.toAdd η)

/-- The subgroup C is not replaced by its closure. -/
def C : Subgroup D := jHom.range

theorem continuous_j : Continuous j := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.inner continuous_const)

/-- A divisible group cannot act nontrivially on a finite orbit. -/
theorem fixed_of_finite_orbit {G X : Type*} [Group G] [MulAction G X]
    [RootableBy G ℕ] (x : X) (hf : (MulAction.orbit G x).Finite) (g : G) :
    g • x = x := by
  let := hf.fintype
  have h := finite_image_trivial (MulAction.toPermHom G (MulAction.orbit G x)) g
  have h' := congrArg (fun p : Equiv.Perm (MulAction.orbit G x) =>
    (p ⟨x, MulAction.mem_orbit_self x⟩).val) h
  exact h'

instance : MeasurableSpace D := borel D
instance : BorelSpace D := ⟨rfl⟩

theorem measurableSet_C : MeasurableSet (C : Set D) := by
  change MeasurableSet (Set.range j)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℂ) (n : ℝ)).image continuous_j).measurableSet

/-- Multiplication of the argument of a character. -/
def scaleE (a : E) : DiscreteE →ₜ* DiscreteE where
  toFun z := Multiplicative.ofAdd (a * Multiplicative.toAdd z)
  map_one' := by change Multiplicative.ofAdd (a * 0) = 1; simp
  map_mul' z w := by
    change Multiplicative.ofAdd (a * (_ + _)) = _
    rw [mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

def scalar (a : E) (d : D) : D := d.comp (scaleE a)

@[simp] theorem scalar_apply (a : E) (d : D) (z : DiscreteE) :
    scalar a d z = d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)) := rfl

@[simp] theorem scalar_one (d : D) : scalar 1 d = d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (1 * Multiplicative.toAdd z)) = d z
  rw [one_mul]
  rfl

@[simp] theorem scalar_mul (a b : E) (d : D) :
    scalar a (scalar b d) = scalar (a * b) d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (b * (a * Multiplicative.toAdd z))) =
    d (Multiplicative.ofAdd ((a * b) * Multiplicative.toAdd z))
  rw [mul_left_comm, ← mul_assoc]

@[simp] theorem scalar_add (a b : E) (d : D) :
    scalar (a + b) d = scalar a d * scalar b d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((a + b) * Multiplicative.toAdd z)) = _
  rw [add_mul]
  exact map_mul d _ _

@[simp] theorem scalar_j (a : E) (ξ : ℂ) :
    scalar a (j ξ) = j (conj (a : ℂ) * ξ) := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ ξ ((a : ℂ) * embed z)) = _
  rw [j_apply]
  congr 1
  simp only [Complex.inner, map_mul, starRingEnd_self_apply]
  congr 1
  ring

theorem scalar_mem_C (a : E) {d : D} (hd : d ∈ C) : scalar a d ∈ C := by
  obtain ⟨ξ, rfl⟩ := hd
  exact ⟨Multiplicative.ofAdd (conj (a : ℂ) * Multiplicative.toAdd ξ), scalar_j a _ |>.symm⟩

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a

/-- Positive fibers of an equivariant partition have finite orbit. This uses
only finite measure and measurability of the fibers, not a measurable quotient. -/
theorem fixed_of_positive_fiber {G X Y : Type*} [Group G] [RootableBy G ℕ]
    [MulAction G X] [MulAction G Y] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (π : X → Y) (heq : ∀ (g : G) (x : X), π (g • x) = g • π x)
    (hmeas : ∀ y, MeasurableSet (π ⁻¹' {y}))
    (hinv : ∀ g : G, MeasureTheory.MeasurePreserving (fun x : X => g • x) μ μ)
    (y : Y) (hpos : 0 < μ (π ⁻¹' {y})) (g : G) : g • y = y := by
  classical
  let A (z : MulAction.orbit G y) : Set X := π ⁻¹' {z.val}
  have hm (z : MulAction.orbit G y) : μ (A z) = μ (π ⁻¹' {y}) := by
    obtain ⟨g, hg⟩ := z.property
    have hs : (fun x : X => g • x) ⁻¹' A z = π ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, A, heq, ← hg]
      constructor
      · intro h
        have h' := congrArg (fun z : Y => g⁻¹ • z) h
        simpa only [inv_smul_smul] using h'
      · exact congrArg (fun z : Y => g • z)
    rw [← (hinv g).measure_preimage ((hmeas z.val).nullMeasurableSet), hs]
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro z w hzw
    change Disjoint (A z) (A w)
    rw [Set.disjoint_left]
    intro x hz hw
    exact hzw (Subtype.ext (hz.symm.trans hw))
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion μ hpos (As := A)
    (fun z => hmeas z.val) hd (MeasureTheory.measure_ne_top μ _)
  have hu : {z : MulAction.orbit G y | μ (π ⁻¹' {y}) ≤ μ (A z)} = Set.univ := by
    ext z
    simp [hm]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  exact fixed_of_finite_orbit y (Set.toFinite _) g

def kCoeff (u : K) : E := ⟨(u.val : ℂ), mem_algebraicClosure_iff.mpr u.property⟩

@[simp] theorem kCoeff_one : kCoeff 1 = 1 := rfl
@[simp] theorem kCoeff_mul (u v : K) : kCoeff (u * v) = kCoeff u * kCoeff v := rfl

def scalarHom (a : E) : D →* D where
  toFun := scalar a
  map_one' := by apply PontryaginDual.ext; intro z; rfl
  map_mul' d e := by apply PontryaginDual.ext; intro z; rfl

instance : MulAction K D where
  smul u d := scalar (kCoeff u) d
  one_smul d := scalar_one d
  mul_smul u v d := (scalar_mul (kCoeff u) (kCoeff v) d).symm

abbrev Cosets := D ⧸ C

def cosetScalar (u : K) : Cosets →* Cosets :=
  QuotientGroup.map C C (scalarHom (kCoeff u)) (fun _ h => scalar_mem_C _ h)

instance : MulAction K Cosets where
  smul u q := cosetScalar u q
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar 1 d) = QuotientGroup.mk d
      rw [scalar_one]
  mul_smul u v q := by
    induction q using QuotientGroup.induction_on with
    | H d =>
      change QuotientGroup.mk (scalar (kCoeff (u * v)) d) =
        QuotientGroup.mk (scalar (kCoeff u) (scalar (kCoeff v) d))
      rw [scalar_mul, kCoeff_mul]

@[simp] theorem quotient_equivariant (u : K) (d : D) :
    QuotientGroup.mk (u • d) = u • (QuotientGroup.mk d : Cosets) := rfl

theorem measurableSet_coset (q : Cosets) :
    MeasurableSet ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    have h : (QuotientGroup.mk : D → Cosets) ⁻¹' {QuotientGroup.mk d} =
        (fun x => x / d) ⁻¹' (C : Set D) := by
      ext x
      exact QuotientGroup.eq_iff_div_mem
    rw [h]
    exact measurableSet_C.preimage (continuous_id.div_const d).measurable

@[simp] theorem scalar_neg (a : E) (d : D) : scalar (-a) d = (scalar a d)⁻¹ := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((-a) * Multiplicative.toAdd z)) =
    (d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)))⁻¹
  rw [neg_mul]
  exact map_inv d _

@[simp] theorem scalar_sub (a b : E) (d : D) :
    scalar (a - b) d = scalar a d / scalar b d := by
  rw [sub_eq_add_neg, scalar_add, scalar_neg, div_eq_mul_inv]

def minusOne : K := ⟨-1, by
  change IsAlgebraic ℚ (-1 : ℂ)
  exact isAlgebraic_one.neg⟩

@[simp] theorem kCoeff_minusOne : kCoeff minusOne = -1 := rfl

theorem coset_fixed_minusOne (q : Cosets) (h : minusOne • q = q) : q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    change QuotientGroup.mk (scalar (-1) d) = QuotientGroup.mk d at h
    have hm : scalar ((-1 : E) - 1) d ∈ C := by
      rw [scalar_sub, scalar_one]
      exact QuotientGroup.eq_iff_div_mem.mp h
    exact (QuotientGroup.eq_one_iff d).mpr ((scalar_mem_C_iff (by norm_num) d).mp hm)

/-- The source's wild-law condition; probability is provided as a measure instance. -/
def IsWild (ν : MeasureTheory.Measure D) : Prop :=
  (∀ u : K, MeasureTheory.MeasurePreserving (fun d : D => u • d) ν ν) ∧
    ν (C : Set D) = 0

theorem wild_coset_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (q : Cosets) :
    ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) = 0 := by
  by_contra hn
  have hp : 0 < ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := pos_iff_ne_zero.mpr hn
  have hfix := fixed_of_positive_fiber ν (QuotientGroup.mk : D → Cosets)
    quotient_equivariant measurableSet_coset hν.1 q hp minusOne
  have hq := coset_fixed_minusOne q hfix
  subst q
  have hs : (QuotientGroup.mk : D → Cosets) ⁻¹' {1} = C := by
    ext d
    exact QuotientGroup.eq_one_iff d
  rw [hs, hν.2] at hn
  exact hn rfl

theorem wild_div_mem_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (d : D) : ν {x | x / d ∈ C} = 0 := by
  convert wild_coset_null ν hν (QuotientGroup.mk d) using 1
  congr 1
  ext x
  exact (QuotientGroup.eq_iff_div_mem (N := C) (x := x) (y := d)).symm

theorem wild_independent_difference (ν : MeasureTheory.Measure D)
    [MeasureTheory.IsProbabilityMeasure ν] (hν : IsWild ν) :
    (ν.prod ν) {p : D × D | p.1 / p.2 ∈ C} = 0 := by
  have hm : MeasurableSet {p : D × D | p.1 / p.2 ∈ C} :=
    measurableSet_C.preimage (continuous_fst.div' continuous_snd).measurable
  rw [MeasureTheory.Measure.prod_apply_symm hm]
  have h (d : D) : ν ((fun x => (x, d)) ⁻¹' {p : D × D | p.1 / p.2 ∈ C}) = 0 :=
    wild_div_mem_null ν hν d
  simp_rw [h]
  simp

theorem continuous_scalar (a : E) : Continuous (scalar a) :=
  (scaleE a).continuous_comp_left

/-- Rational tests identify the frequency of a real continuous character. -/
theorem frequency_zero_of_rational_tests (a : ℝ)
    (h : ∀ q : ℚ, Circle.exp (a * (q : ℝ)) = 1) : a = 0 := by
  have heq : (fun t : ℝ => Circle.exp (a * t)) = fun _ => 1 :=
    Rat.denseRange_cast.equalizer
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
      continuous_const (funext h)
  have hpi : Circle.exp Real.pi ≠ 1 := by
    intro hone
    have ha := congrArg (fun u : Circle => (u : ℂ).arg) hone
    rw [Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl] at ha
    simp at ha
  by_contra ha
  have ht := congrFun heq (Real.pi / a)
  have hmul : a * (Real.pi / a) = Real.pi := by field_simp
  rw [hmul] at ht
  exact hpi ht

def imagUnit : E := ⟨Complex.I, mem_algebraicClosure_iff.mpr
  (IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]
    exact isAlgebraic_one.neg))⟩

@[simp] theorem coe_imagUnit : (imagUnit : ℂ) = Complex.I := rfl

theorem j_eq_one_iff (ξ : ℂ) : j ξ = 1 ↔ ξ = 0 := by
  constructor
  · intro h
    have hre : ξ.re = 0 := frequency_zero_of_rational_tests ξ.re (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd (q : E))) h
      change Circle.exp (inner ℝ ξ ((q : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    have him : ξ.im = 0 := frequency_zero_of_rational_tests ξ.im (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd ((q : E) * imagUnit))) h
      change Circle.exp (inner ℝ ξ (((q : E) * imagUnit : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    exact Complex.ext hre him
  · rintro rfl
    exact j_zero

@[simp] theorem j_neg (ξ : ℂ) : j (-ξ) = (j ξ)⁻¹ :=
  map_inv jHom (Multiplicative.ofAdd ξ)

@[simp] theorem j_sub (ξ η : ℂ) : j (ξ - η) = j ξ / j η := by
  rw [sub_eq_add_neg, j_add, j_neg, div_eq_mul_inv]

theorem j_injective : Function.Injective j := by
  intro ξ η h
  apply sub_eq_zero.mp
  apply (j_eq_one_iff _).mp
  rw [j_sub, h, div_self']

theorem j_measurableEmbedding : MeasurableEmbedding j :=
  continuous_j.measurableEmbedding j_injective

/-- The complex algebraic closure used above is precisely F(i) from the source,
not a different countable plane. -/
theorem algebraic_complex_iff_coordinates (z : ℂ) :
    IsAlgebraic ℚ z ↔ IsAlgebraic ℚ z.re ∧ IsAlgebraic ℚ z.im := by
  have hi : IsAlgebraic ℚ Complex.I := mem_algebraicClosure_iff.mp imagUnit.property
  have hhalf : IsAlgebraic ℚ ((2 : ℂ)⁻¹) := (isAlgebraic_natCast 2).inv
  constructor
  · intro hz
    have hc : IsAlgebraic ℚ (conj z) :=
      IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom hz
    constructor
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := (hz.add hc).mul hhalf
      convert h using 1
      first | rfl | (apply Complex.ext <;> simp; ring)
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := ((hz.sub hc).mul hhalf).mul hi.inv
      convert h using 1
      first | rfl | (apply Complex.ext <;> simp; ring)
  · rintro ⟨hr, hi'⟩
    have hr' : IsAlgebraic ℚ (z.re : ℂ) := hr.algebraMap
    have hi'' : IsAlgebraic ℚ (z.im : ℂ) := hi'.algebraMap
    simpa only [Complex.re_add_im] using hr'.add (hi''.mul hi)

/-- Ordinary one-dimensional characters, proved from the covering property of exp. -/
theorem real_character (f : ℝ → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t, f t = Circle.exp (a * t) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  obtain ⟨F, ⟨hFzero, hFexp⟩, hFuniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨f, hf⟩ 0 0 (by simpa using hzero.symm)
  have hF (t : ℝ) : Circle.exp (F t) = f t := congrFun hFexp t
  have hadd (x y : ℝ) : F (x + y) = F x + F y := by
    let G : C(ℝ, ℝ) := ⟨fun t => F (t + y) - F y,
      (F.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
    have hG : G = F := hFuniq G ⟨by simp [G], by
      funext t
      change Circle.exp (F (t + y) - F y) = f t
      rw [Circle.exp_sub, hF, hF, hmul, mul_div_cancel_right]⟩
    have hh := congrArg (fun g : C(ℝ, ℝ) => g x) hG
    dsimp [G] at hh
    linarith
  let Fadd : ℝ →+ ℝ := { toFun := F, map_zero' := hFzero, map_add' := hadd }
  have hrat (q : ℚ) : F (q : ℝ) = (q : ℝ) * F 1 := by
    simpa [Fadd, Rat.smul_def] using map_rat_smul Fadd q (1 : ℝ)
  have hlinear : (fun t : ℝ => F t) = fun t => t * F 1 :=
    Rat.denseRange_cast.equalizer F.continuous
      (continuous_id.mul continuous_const) (funext hrat)
  refine ⟨F 1, fun t => ?_⟩
  rw [← hF, congrFun hlinear t, mul_comm]
abbrev F := algebraicClosure ℚ ℝ

theorem dense_F : Dense (F : Set ℝ) :=
  Dense.mono (Set.range_subset_iff.mpr fun q : ℚ =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_ratCast ℚ q))
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))

/-- The source's exact ordinary-character description on the dense real algebraic field. -/
theorem algebraic_real_character (f : F → Circle) (hf : Continuous f)
    (hmul : ∀ x y, f (x + y) = f x * f y) :
    ∃ a : ℝ, ∀ t : F, f t = Circle.exp (a * (t : ℝ)) := by
  have hzero : f 0 = 1 := by
    have h := hmul 0 0
    exact (mul_left_cancel (show f 0 * 1 = f 0 * f 0 by simpa using h)).symm
  let fHom : Multiplicative F →* Circle := {
    toFun := fun t => f t.toAdd
    map_one' := hzero
    map_mul' := fun _ _ => hmul _ _ }
  have hu : UniformContinuous f :=
    uniformContinuous_monoidHom_of_continuous (f := fHom) hf
  let g := dense_F.extend f
  have hg : Continuous g := (dense_F.uniformContinuous_extend hu).continuous
  have hext (t : F) : g (t : ℝ) = f t := dense_F.extend_eq hf t
  have hgmul : ∀ x y : ℝ, g (x + y) = g x * g y := by
    intro x y
    refine dense_F.denseRange_val.induction_on₂
      (p := fun x y => g (x + y) = g x * g y) ?_ ?_ x y
    · exact isClosed_eq (hg.comp (continuous_fst.add continuous_snd))
        ((hg.comp continuous_fst).mul (hg.comp continuous_snd))
    · intro x y
      change g ((x + y : F) : ℝ) = g (x : ℝ) * g (y : ℝ)
      simp only [hext, hmul]
  obtain ⟨a, ha⟩ := real_character g hg hgmul
  exact ⟨a, fun t => (hext t).symm.trans (ha t)⟩

/-- The real-algebraic inclusion into the algebraic plane. -/
def ofF : F →+* E where
  toFun t := ⟨(t : ℝ), mem_algebraicClosure_iff.mpr
    ((mem_algebraicClosure_iff.mp t.property).algebraMap (A := ℂ))⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp] theorem coe_ofF (t : F) : (ofF t : ℂ) = (t : ℝ) := rfl

def DiscreteF := Multiplicative F deriving CommGroup
instance : TopologicalSpace DiscreteF := ⊥
instance : DiscreteTopology DiscreteF := ⟨rfl⟩
instance : IsTopologicalGroup DiscreteF := inferInstance
abbrev DF := PontryaginDual DiscreteF
instance : MeasurableSpace DF := borel DF
instance : BorelSpace DF := ⟨rfl⟩

def embedF (t : DiscreteF) : ℝ := (Multiplicative.toAdd t : F)
@[simp] theorem embedF_one : embedF 1 = 0 := rfl
@[simp] theorem embedF_mul (t s : DiscreteF) : embedF (t * s) = embedF t + embedF s := rfl

/-- Standard frequencies for the real algebraic line; again use the actual image. -/
def jF (l : ℝ) : DF where
  toFun t := Circle.exp (l * embedF t)
  map_one' := by simp
  map_mul' t s := by simp only [embedF_mul, mul_add, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem jF_apply (l : ℝ) (t : DiscreteF) :
    jF l t = Circle.exp (l * (Multiplicative.toAdd t : F)) := rfl

def CF : Set DF := Set.range jF

theorem continuous_jF : Continuous jF := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.mul continuous_const)

theorem measurableSet_CF : MeasurableSet CF := by
  change MeasurableSet (Set.range jF)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℝ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℝ) (n : ℝ)).image continuous_jF).measurableSet

/-- The dual restriction to the line aF. -/
def lineHom (a : E) : DiscreteF →ₜ* DiscreteE where
  toFun t := Multiplicative.ofAdd (a * ofF (Multiplicative.toAdd t))
  map_one' := by change Multiplicative.ofAdd (a * ofF 0) = 1; simp
  map_mul' t s := by
    change Multiplicative.ofAdd (a * ofF (_ + _)) = _
    rw [map_add, mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

def restrictLine (a : E) (d : D) : DF := d.comp (lineHom a)

theorem continuous_restrictLine (a : E) : Continuous (restrictLine a) :=
  (lineHom a).continuous_comp_left

def L (a : E) : Set D := {d | Continuous (fun t : F =>
  d (Multiplicative.ofAdd (a * ofF t)))}

theorem mem_L_iff (a : E) (d : D) : d ∈ L a ↔ restrictLine a d ∈ CF := by
  constructor
  · intro hd
    obtain ⟨l, hl⟩ := algebraic_real_character
      (fun t : F => d (Multiplicative.ofAdd (a * ofF t))) hd (by
        intro t s
        rw [map_add, mul_add]
        exact map_mul d _ _)
    use l
    apply PontryaginDual.ext
    intro t
    exact (hl (Multiplicative.toAdd t)).symm
  · rintro ⟨l, hl⟩
    have h (t : F) : d (Multiplicative.ofAdd (a * ofF t)) = Circle.exp (l * (t : ℝ)) :=
      (congrArg (fun χ : DF => χ (Multiplicative.ofAdd t)) hl).symm
    change Continuous (fun t : F => d (Multiplicative.ofAdd (a * ofF t)))
    simp_rw [h]
    exact Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)

theorem measurableSet_L (a : E) : MeasurableSet (L a) := by
  have h : L a = restrictLine a ⁻¹' CF := by ext d; exact mem_L_iff a d
  rw [h]
  exact measurableSet_CF.preimage (continuous_restrictLine a).measurable

def reF (z : E) : F := ⟨(z : ℂ).re, mem_algebraicClosure_iff.mpr
  ((algebraic_complex_iff_coordinates _).mp (mem_algebraicClosure_iff.mp z.property)).1⟩
def imF (z : E) : F := ⟨(z : ℂ).im, mem_algebraicClosure_iff.mpr
  ((algebraic_complex_iff_coordinates _).mp (mem_algebraicClosure_iff.mp z.property)).2⟩

@[simp] theorem coe_reF (z : E) : (reF z : ℝ) = (z : ℂ).re := rfl
@[simp] theorem coe_imF (z : E) : (imF z : ℝ) = (z : ℂ).im := rfl

theorem reF_add_imF (z : E) : ofF (reF z) + imagUnit * ofF (imF z) = z := by
  apply Subtype.ext
  change ((z : ℂ).re : ℂ) + Complex.I * (z : ℂ).im = (z : ℂ)
  rw [mul_comm, Complex.re_add_im]

theorem line_add {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a + b) := by
  have h (t : F) : d (Multiplicative.ofAdd ((a + b) * ofF t)) =
      d (Multiplicative.ofAdd (a * ofF t)) * d (Multiplicative.ofAdd (b * ofF t)) := by
    rw [add_mul]; exact map_mul d _ _
  change Continuous _
  simp_rw [h]
  exact ha.mul hb

theorem line_mul_real {a : E} {d : D} (ha : d ∈ L a) (t : F) :
    d ∈ L (a * ofF t) := by
  change Continuous _ at ha ⊢
  convert ha.comp (continuous_const.mul continuous_id : Continuous (fun s : F => t * s)) using 1
  funext s
  simp only [Function.comp_apply, Pi.mul_apply, map_mul, mul_assoc]

theorem line_sub {a b : E} {d : D} (ha : d ∈ L a) (hb : d ∈ L b) :
    d ∈ L (a - b) := by
  have hn : d ∈ L (-b) := by simpa using line_mul_real hb (-1)
  simpa only [sub_eq_add_neg] using line_add ha hn

theorem orthogonal_lines {d : D} (h1 : d ∈ L 1) (hi : d ∈ L imagUnit) : d ∈ C := by
  obtain ⟨l, hl⟩ := (mem_L_iff 1 d).mp h1
  obtain ⟨e, he⟩ := (mem_L_iff imagUnit d).mp hi
  refine ⟨Multiplicative.ofAdd ((l : ℂ) + (e : ℂ) * Complex.I), ?_⟩
  apply PontryaginDual.ext
  intro z
  have hr (t : F) : d (Multiplicative.ofAdd (ofF t)) = Circle.exp (l * (t : ℝ)) := by
    have hh := congrArg (fun f : DF => f (Multiplicative.ofAdd t)) hl
    change Circle.exp (l * (t : ℝ)) = d (Multiplicative.ofAdd (1 * ofF t)) at hh
    simpa only [one_mul] using hh.symm
  have hi' (t : F) : d (Multiplicative.ofAdd (imagUnit * ofF t)) = Circle.exp (e * (t : ℝ)) :=
    (congrArg (fun f : DF => f (Multiplicative.ofAdd t)) he).symm
  change Circle.exp (inner ℝ ((l : ℂ) + (e : ℂ) * Complex.I) (embed z)) = d z
  have hd : d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)))) *
      d (Multiplicative.ofAdd (imagUnit * ofF (imF (Multiplicative.toAdd z)))) := by
    calc
      d z = d (Multiplicative.ofAdd (ofF (reF (Multiplicative.toAdd z)) +
        imagUnit * ofF (imF (Multiplicative.toAdd z)))) :=
          congrArg d (congrArg Multiplicative.ofAdd (reF_add_imF (Multiplicative.toAdd z))).symm
      _ = _ := map_mul d _ _
  rw [hd, hr, hi', ← Circle.exp_add]
  congr 1
  simp [Complex.inner, embed, Complex.mul_re, Complex.mul_im, mul_comm]

/-- Two genuinely independent algebraic directions force an ordinary character. -/
theorem line_one_and_nonreal {d : D} (h1 : d ∈ L 1) {w : E}
    (hw : d ∈ L w) (hn : imF w ≠ 0) : d ∈ C := by
  have hr : d ∈ L (ofF (reF w)) := by simpa using line_mul_real h1 (reF w)
  have hsub := line_sub hw hr
  have him := line_mul_real hsub (imF w)⁻¹
  have heq : (w - ofF (reF w)) * ofF (imF w)⁻¹ = imagUnit := by
    have hz := reF_add_imF w
    have hzero : ofF (imF w) ≠ 0 := fun h => hn (ofF.injective (by simpa using h))
    rw [map_inv₀]
    calc
      (w - ofF (reF w)) * (ofF (imF w))⁻¹ =
        (imagUnit * ofF (imF w)) * (ofF (imF w))⁻¹ := by congr 1; linear_combination -hz
      _ = imagUnit := by rw [mul_assoc, mul_inv_cancel₀ hzero, mul_one]
  rw [heq] at him
  exact orthogonal_lines h1 him

@[simp] theorem scalar_line (a b : E) (d : D) : scalar a d ∈ L b ↔ d ∈ L (a * b) := by
  change Continuous (fun t : F => d (Multiplicative.ofAdd (a * (b * ofF t)))) ↔ _
  simp only [← mul_assoc]
  rfl

theorem independent_lines {a b : E} (ha : a ≠ 0) (hn : imF (a⁻¹ * b) ≠ 0)
    {d : D} (hda : d ∈ L a) (hdb : d ∈ L b) : d ∈ C := by
  apply (scalar_mem_C_iff ha d).mp
  apply line_one_and_nonreal (w := a⁻¹ * b) (by simpa using hda) _ hn
  simpa [← mul_assoc, ha] using hdb

@[simp] theorem kCoeff_inv (u : K) : kCoeff u⁻¹ = (kCoeff u)⁻¹ := by
  apply Subtype.ext
  change ((u.val)⁻¹ : Circle).val = (u.val : ℂ)⁻¹
  exact Circle.coe_inv u.val

@[simp] theorem kCoeff_ne_zero (u : K) : kCoeff u ≠ 0 := by
  intro h
  have hz : (u.val : ℂ) = 0 := congrArg (fun x : E => (x : ℂ)) h
  exact u.val.coe_ne_zero hz

theorem real_rotation_square (u : K) (hi : imF (kCoeff u) = 0) : u ^ 2 = 1 := by
  have him : (u.val : ℂ).im = 0 := congrArg (fun x : F => (x : ℝ)) hi
  have hn : (u.val : ℂ).re * (u.val : ℂ).re = 1 := by
    have hh := Complex.sq_norm (u.val : ℂ)
    rw [Circle.norm_coe] at hh
    simpa [Complex.normSq_apply, him] using hh.symm
  apply Subtype.ext
  apply Subtype.ext
  change (u.val : ℂ) ^ 2 = 1
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him, hn]

/-- Squared rotations index the distinct unoriented algebraic lines. -/
theorem rotated_directions_independent {a : E} (ha : a ≠ 0) {u v : K}
    (huv : u ^ 2 ≠ v ^ 2) : imF ((a * kCoeff u)⁻¹ * (a * kCoeff v)) ≠ 0 := by
  intro h
  have heq : (a * kCoeff u)⁻¹ * (a * kCoeff v) = kCoeff (u⁻¹ * v) := by
    simp [mul_inv_rev, mul_assoc, ha]
  rw [heq] at h
  have hp := real_rotation_square (u⁻¹ * v) h
  apply huv
  have hp' : (u ^ 2)⁻¹ * (v ^ 2) = 1 := by simpa only [mul_pow, inv_pow] using hp
  exact inv_mul_eq_one.mp hp'

/-- Complete line-event conclusion of the source's null-events lemma. -/
theorem wild_line_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) {a : E} (ha : a ≠ 0) : ν (L a) = 0 := by
  classical
  by_contra hn
  have hp : 0 < ν (L a) := pos_iff_ne_zero.mpr hn
  let root : K → K := fun u => Classical.choose (K_pow_surjective 2 (by norm_num) u)
  have hroot (u : K) : (root u) ^ 2 = u := Classical.choose_spec (K_pow_surjective 2 (by norm_num) u)
  let B (u : K) : Set D := L (a * kCoeff (root u)) \ (C : Set D)
  have hBm (u : K) : MeasurableSet (B u) := (measurableSet_L _).diff measurableSet_C
  have hpre (u : K) : (fun d : D => (root u) • d) ⁻¹' L a = L (a * kCoeff (root u)) := by
    ext d
    change scalar (kCoeff (root u)) d ∈ L a ↔ _
    rw [scalar_line, mul_comm]
  have hmass (u : K) : ν (B u) = ν (L a) := by
    change ν (L (a * kCoeff (root u)) \ (C : Set D)) = _
    rw [MeasureTheory.measure_sdiff_null hν.2, ← hpre]
    exact (hν.1 (root u)).measure_preimage (measurableSet_L a).nullMeasurableSet
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro u v huv
    change Disjoint (B u) (B v)
    rw [Set.disjoint_left]
    rintro d ⟨hdu, hdc⟩ ⟨hdv, _⟩
    apply hdc
    apply independent_lines (mul_ne_zero ha (kCoeff_ne_zero _))
      (rotated_directions_independent ha _) hdu hdv
    simpa only [hroot] using huv
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion ν hp (As := B)
    hBm hd (MeasureTheory.measure_ne_top ν _)
  have hu : {u : K | ν (L a) ≤ ν (B u)} = Set.univ := by ext u; simp [hmass]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  have hm := finite_image_trivial (MonoidHom.id K) minusOne
  have hb := congrArg (fun u : K => (u.val : ℂ)) hm
  norm_num [minusOne] at hb

end PlaneFiveColor.Spectral

end

end OAI
