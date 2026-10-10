import OAI.MathematicalPhysics.Boltzmann.Branching.DatumBounds
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Collision.TransverseAverage
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace OAI

section

/-! # The cold-jet annuli and opposite stripe enlargements

These are the actual spatial masks of Section 4. The geometric scale is
indexed from zero here, representing the manuscript's first positive index.
-/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.DatumBounds

namespace BoltzmannNonuniqueness.JetGeometry

def gapCoefficient (η : ℝ) : ℝ := (Real.exp η - 1) / 16

def jetScale (s₀ η : ℝ) (j : ℕ) : ℝ := scale s₀ η (j + 1)

def enlargementWidth (η s : ℝ) : ℝ := gapCoefficient η / 4 * s ^ 2

def annularCore (η s : ℝ) : Set Transverse :=
  {y | s + gapCoefficient η * s ^ 2 < ‖y‖ ∧
    ‖y‖ < Real.exp η * s - gapCoefficient η * s ^ 2}

def stripe (s : ℝ) (positive : Bool) : Set Transverse :=
  {y | ∃ k : ℤ, ((k : ℝ) + if positive then 0 else 1 / 2) * s ^ 2 < y 0 ∧
    y 0 < ((k : ℝ) + (if positive then 0 else 1 / 2) + 1 / 4) * s ^ 2}

def mask (η s : ℝ) (positive : Bool) : Set Transverse := annularCore η s ∩ stripe s positive

def enlargement (η s : ℝ) (positive : Bool) : Set Transverse :=
  cthickening (enlargementWidth η s) (mask η s positive)

theorem gapCoefficient_pos {η : ℝ} (hη : 0 < η) : 0 < gapCoefficient η := by
  have h := Real.one_lt_exp_iff.mpr hη
  unfold gapCoefficient
  linarith

theorem gapCoefficient_le {η : ℝ} (hη : η ≤ Real.log 2) : gapCoefficient η ≤ 1 / 16 := by
  have h := Real.exp_le_exp.mpr hη
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  unfold gapCoefficient
  linarith

theorem enlargementWidth_pos {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    0 < enlargementWidth η s := by
  have := gapCoefficient_pos hη
  unfold enlargementWidth
  positivity

theorem enlargement_witness {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    {positive : Bool} {y : Transverse} (hy : y ∈ enlargement η s positive) :
    ∃ x ∈ mask η s positive, dist y x ≤ 2 * enlargementWidth η s := by
  have hδ := enlargementWidth_pos hη hs
  obtain ⟨x, hx, hd⟩ := mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (mask η s positive)
    (by positivity : 0 < 2 * enlargementWidth η s) (by linarith) hy)
  exact ⟨x, hx, mem_closedBall.mp hd⟩

theorem enlargement_subset_annulus {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (positive : Bool) :
    enlargement η s positive ⊆ {y : Transverse | s < ‖y‖ ∧ ‖y‖ < Real.exp η * s} := by
  intro y hy
  obtain ⟨x, hx, hdist⟩ := enlargement_witness hη hs hy
  have h₁ := norm_sub_norm_le y x
  have h₂ := norm_sub_norm_le x y
  rw [← dist_eq_norm] at h₁ h₂
  rw [dist_comm x y] at h₂
  have hgap : 0 < gapCoefficient η * s ^ 2 := mul_pos (gapCoefficient_pos hη) (sq_pos_of_pos hs)
  have hcore := hx.1
  change s + gapCoefficient η * s ^ 2 < ‖x‖ ∧
    ‖x‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at hcore
  dsimp only [enlargementWidth] at hdist
  constructor <;> linarith [hcore.1, hcore.2]

theorem scale_antitone {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η) :
    Antitone (scale s₀ η) := by
  intro i j hij
  unfold scale
  apply mul_le_mul_of_nonneg_left _ hs₀
  apply Real.exp_le_exp.mpr
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem outerRadius_eq (s₀ η : ℝ) (j : ℕ) :
    Real.exp η * jetScale s₀ η j = scale s₀ η j := by
  unfold jetScale scale
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem ordered_annuli {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i < j) :
    Real.exp η * jetScale s₀ η j ≤ jetScale s₀ η i := by
  rw [outerRadius_eq]
  exact scale_antitone hs₀ hη (Nat.succ_le_iff.mpr hij)

theorem distinct_scale_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i j : ℕ} (hij : i ≠ j) (a b : Bool) :
    Disjoint (enlargement η (jetScale s₀ η i) a) (enlargement η (jetScale s₀ η j) b) := by
  apply disjoint_left.mpr
  intro y hyi hyj
  have hi := enlargement_subset_annulus hη (scale_pos hs₀ _) a hyi
  have hj := enlargement_subset_annulus hη (scale_pos hs₀ _) b hyj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := ordered_annuli hs₀.le hη.le hij
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hi.1.trans hj.2)
  · have h := ordered_annuli hs₀.le hη.le hji
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hj.1.trans hi.2)

theorem stripe_distance {s : ℝ} (hs : 0 < s) {x y : Transverse}
    (hx : x ∈ stripe s true) (hy : y ∈ stripe s false) : s ^ 2 / 4 < dist x y := by
  obtain ⟨k, hk₁, hk₂⟩ := hx
  obtain ⟨l, hl₁, hl₂⟩ := hy
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hk₁ hk₂ hl₁ hl₂
  have hcoord : |x 0 - y 0| ≤ dist x y := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using PiLp.norm_apply_le (x - y) 0
  have hp : 0 < s ^ 2 := sq_pos_of_pos hs
  rcases le_or_gt k l with hkl | hlk
  · have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < y 0 - x 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans (by simpa only [abs_sub_comm] using hcoord))
  · have hcast : (l : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hlk)
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < x 0 - y 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans hcoord)

theorem opposite_enlargements_disjoint {η s : ℝ} (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hs : 0 < s) :
    Disjoint (enlargement η s true) (enlargement η s false) := by
  apply disjoint_left.mpr
  intro y hy₁ hy₂
  obtain ⟨x, hx, hxy⟩ := enlargement_witness hη hs hy₁
  obtain ⟨z, hz, hzy⟩ := enlargement_witness hη hs hy₂
  have hsep := stripe_distance hs hx.2 hz.2
  have hdist := dist_triangle x y z
  rw [dist_comm x y] at hdist
  have hc := mul_le_mul_of_nonneg_right (gapCoefficient_le hηmax) (sq_nonneg s)
  unfold enlargementWidth at hxy hzy
  nlinarith

theorem enlargement_inside_baseBall {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (j : ℕ) (a : Bool) : enlargement η (jetScale s₀ η j) a ⊆ ball 0 s₀ := by
  intro y hy
  have h := (enlargement_subset_annulus hη (scale_pos hs₀ _) a hy).2
  change ‖y‖ < Real.exp η * jetScale s₀ η j at h
  rw [outerRadius_eq] at h
  have hj := scale_antitone hs₀.le hη.le (Nat.zero_le j)
  have hzero : scale s₀ η 0 = s₀ := by simp [scale]
  rw [hzero] at hj
  simpa only [mem_ball, dist_zero_right] using h.trans_le hj

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Pairwise disjoint periodic cold-jet spatial enlargements -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetLattice

abbrev Lattice := Fin 3 → ℤ

structure Label where
  annulus : ℕ
  positive : Bool
  lattice : Lattice
  deriving DecidableEq

def transverseShift (n : Lattice) : Transverse :=
  WithLp.toLp 2 (fun i : Fin 2 => (n i.castSucc : ℝ))

def axialShift (n : Lattice) : ℝ := (n (Fin.last 2) : ℝ)

def spatialEnlargement (s₀ η t : ℝ) (i : Label) : Set Velocity :=
  {x | transverse x - transverseShift i.lattice ∈
      enlargement η (jetScale s₀ η i.annulus) i.positive ∧
    |axial x - axialShift i.lattice| ≤ 1 / 8 + 2 * t + 1 / 16}

theorem integer_distance {m n : ℤ} (h : m ≠ n) : (1 : ℝ) ≤ |(m : ℝ) - n| := by
  have h' := Int.one_le_abs (sub_ne_zero.mpr h)
  exact_mod_cast h'

theorem distinct_transverse_shifts {m n : Lattice}
    (h : ∃ k : Fin 2, m k.castSucc ≠ n k.castSucc) :
    1 ≤ ‖transverseShift m - transverseShift n‖ := by
  obtain ⟨k, hk⟩ := h
  have hn := PiLp.norm_apply_le (transverseShift m - transverseShift n) k
  change ‖(m k.castSucc : ℝ) - n k.castSucc‖ ≤ _ at hn
  rw [Real.norm_eq_abs] at hn
  exact (integer_distance hk).trans hn

theorem common_point_transverse_lattice {s₀ η : ℝ} (hs₀ : 0 < s₀)
    (hsmax : s₀ ≤ 1 / 8) (hη : 0 < η) {t : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    ∀ k : Fin 2, i.lattice k.castSucc = j.lattice k.castSucc := by
  by_contra! h
  have hsep := distinct_transverse_shifts h
  have hi' := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hi.1
  have hj' := enlargement_inside_baseBall hs₀ hη j.annulus j.positive hj.1
  rw [mem_ball, dist_zero_right] at hi' hj'
  have htri := norm_sub_le (transverse x - transverseShift j.lattice)
    (transverse x - transverseShift i.lattice)
  have he : transverse x - transverseShift j.lattice - (transverse x - transverseShift i.lattice) =
      transverseShift i.lattice - transverseShift j.lattice := by abel
  rw [he] at htri
  linarith

theorem common_point_axial_lattice {t : ℝ} (ht : t ≤ 1 / 32)
    {s₀ η : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice (Fin.last 2) = j.lattice (Fin.last 2) := by
  by_contra h
  have hsep := integer_distance h
  have htri := abs_sub_le (axialShift i.lattice) (axial x) (axialShift j.lattice)
  rw [abs_sub_comm (axialShift i.lattice) (axial x)] at htri
  have hi' := hi.2
  have hj' := hj.2
  change |axial x - axialShift i.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hi'
  change |axial x - axialShift j.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hj'
  change 1 ≤ |axialShift i.lattice - axialShift j.lattice| at hsep
  linarith

theorem common_point_lattice {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice = j.lattice := by
  have htrans := common_point_transverse_lattice hs₀ hsmax hη hi hj
  have haxial := common_point_axial_lattice ht hi hj
  funext k
  refine Fin.lastCases haxial htrans k

theorem common_point_label {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) : i = j := by
  have hn := common_point_lattice hs₀ hsmax hη ht hi hj
  have hi' := hi.1
  have hj' := hj.1
  rw [← hn] at hj'
  have ha : i.annulus = j.annulus := by
    by_contra h
    exact (disjoint_left.mp (distinct_scale_disjoint hs₀ hη h i.positive j.positive)) hi' hj'
  have hs : i.positive = j.positive := by
    rw [← ha] at hj'
    by_contra h
    have hd := opposite_enlargements_disjoint hη hηmax
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus + 1))
    cases hiBool : i.positive <;> cases hjBool : j.positive
    · exact h (hiBool.trans hjBool.symm)
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hj' hi'
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hi' hj'
    · exact h (hiBool.trans hjBool.symm)
  cases i
  cases j
  simp_all

/-- The disjointness statement of manuscript Lemma `jet:geometry`. -/
theorem pairwise_spatialEnlargement {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (ht : t ≤ 1 / 32) :
    Pairwise (fun i j : Label => Disjoint (spatialEnlargement s₀ η t i)
      (spatialEnlargement s₀ η t j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  exact hij (common_point_label hs₀ hsmax hη hηmax ht hi hj)

end BoltzmannNonuniqueness.JetLattice

end

end

section

/-! # Area bounds for the original striped cold-jet masks -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskMeasure

theorem measurableSet_stripe (s : ℝ) (a : Bool) : MeasurableSet (stripe s a) := by
  unfold stripe
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_lt measurable_const (by fun_prop : Measurable (fun y : Transverse => y 0))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun y : Transverse => y 0)) measurable_const)

theorem measurableSet_annularCore (η s : ℝ) : MeasurableSet (annularCore η s) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem measurableSet_mask (η s : ℝ) (a : Bool) : MeasurableSet (mask η s a) :=
  (measurableSet_annularCore η s).inter (measurableSet_stripe s a)

theorem mask_subset_ball {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    mask η s a ⊆ ball 0 (Real.exp η * s) := by
  intro y hy
  have hc : 0 ≤ gapCoefficient η := by
    unfold gapCoefficient
    have := Real.one_le_exp hη
    positivity
  have h := hy.1.2
  change ‖y‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at h
  rw [mem_ball, dist_zero_right]
  exact h.trans_le (sub_le_self _ (mul_nonneg hc (sq_nonneg s)))

theorem mask_finite {η s : ℝ} (hη : 0 ≤ η) (a : Bool) : volume (mask η s a) < ∞ :=
  (measure_mono (mask_subset_ball (s := s) hη a)).trans_lt (measure_ball_lt_top ..)

theorem mask_area_le {η s : ℝ} (hη : 0 ≤ η) (hs : 0 ≤ s) (a : Bool) :
    volume.real (mask η s a) ≤ Real.pi * (Real.exp η * s) ^ 2 := by
  have h := measureReal_mono (μ := (volume : Measure Transverse)) (mask_subset_ball (s := s) hη a)
  rw [TransverseDisk.disk_volume_real 0 (mul_nonneg (Real.exp_pos η).le hs)] at h
  exact h

theorem mask_area_uniform {η s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hs : 0 ≤ s) (a : Bool) : volume.real (mask η s a) ≤ 4 * Real.pi * s ^ 2 := by
  apply (mask_area_le hη hs a).trans
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have hp := mul_le_mul_of_nonneg_right he hs
  have hsq : (Real.exp η * s) ^ 2 ≤ (2 * s) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hp
  nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

theorem indicator_integrable {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    Integrable ((mask η s a).indicator (fun _ => (1 : ℝ))) :=
  integrable_indicator_iff (measurableSet_mask η s a) |>.mpr
    (integrableOn_const (mask_finite hη a).ne)

end BoltzmannNonuniqueness.JetMaskMeasure

end

end

section

/-! # A fixed smooth compactly supported thermal probability kernel -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetThermalKernel

def bump : ContDiffBump (0 : Velocity) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def J : Velocity → ℝ := bump.normed volume

theorem J_nonneg (v : Velocity) : 0 ≤ J v := bump.nonneg_normed v

theorem J_smooth : ContDiff ℝ (⊤ : ℕ∞) J := bump.contDiff_normed

theorem J_integrable : Integrable J := bump.integrable_normed

theorem J_integral : ∫ v, J v = 1 := bump.integral_normed

theorem J_support : Function.support J = ball 0 1 := bump.support_normed_eq

theorem J_zero {v : Velocity} (hv : 1 ≤ ‖v‖) : J v = 0 := by
  by_contra h
  have hs : v ∈ Function.support J := h
  rw [J_support, mem_ball, dist_zero_right] at hs
  exact not_lt_of_ge hv hs

theorem J_compact : HasCompactSupport J := bump.hasCompactSupport_normed

def bound : ℝ := (∫ v, bump v)⁻¹

theorem bound_pos : 0 < bound := inv_pos.mpr bump.integral_pos

theorem J_le (v : Velocity) : J v ≤ bound := by
  unfold J ContDiffBump.normed bound
  exact (div_le_div_of_nonneg_right bump.le_one bump.integral_pos.le).trans_eq (one_div _)

end BoltzmannNonuniqueness.JetThermalKernel

end

end

section

/-! # Mass, support and integrability of translated thermal profiles -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel

namespace BoltzmannNonuniqueness.JetThermalLaw

def scaled (d : ℝ) (a : Velocity) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  (d ^ 3)⁻¹ * f (d⁻¹ • (v - a))

def density (d : ℝ) (a : Velocity) : Velocity → ℝ := scaled d a J

theorem integrable_scaled {f : Velocity → ℝ} (hf : Integrable f) {d : ℝ}
    (hd : 0 < d) (a : Velocity) : Integrable (scaled d a f) :=
  ((hf.comp_smul (inv_ne_zero hd.ne')).comp_sub_right a).const_mul _

theorem integral_scaled (f : Velocity → ℝ) {d : ℝ} (hd : 0 < d) (a : Velocity) :
    (∫ v, scaled d a f v) = ∫ v, f v := by
  unfold scaled
  rw [integral_const_mul]
  change (d ^ 3)⁻¹ * (∫ v, (fun w => f (d⁻¹ • w)) (v - a)) = _
  rw [integral_sub_right_eq_self (fun w => f (d⁻¹ • w)) a,
    Measure.integral_comp_inv_smul_of_nonneg volume f hd.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp

theorem density_nonneg {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) : 0 ≤ density d a v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hd _)) (J_nonneg _)

theorem density_integrable {d : ℝ} (hd : 0 < d) (a : Velocity) : Integrable (density d a) :=
  integrable_scaled J_integrable hd a

theorem density_mass {d : ℝ} (hd : 0 < d) (a : Velocity) : ∫ v, density d a v = 1 := by
  rw [density, integral_scaled J hd a, J_integral]

theorem density_smooth (d : ℝ) (a : Velocity) : ContDiff ℝ (⊤ : ℕ∞) (density d a) := by
  unfold density scaled
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun v : Velocity => d⁻¹ • (v - a)) :=
    (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Velocity => d⁻¹)).smul
      (contDiff_id.sub contDiff_const)
  exact contDiff_const.mul (J_smooth.comp harg)

theorem density_zero {d : ℝ} (hd : 0 < d) (a v : Velocity) (hv : d ≤ ‖v - a‖) :
    density d a v = 0 := by
  have h : 1 ≤ ‖d⁻¹ • (v - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact (one_le_inv_mul₀ hd).mpr hv
  simp only [density, scaled, J_zero h, mul_zero]

theorem density_velocity_bound {d : ℝ} (hd : 0 < d) {a v : Velocity}
    (hv : density d a v ≠ 0) : ‖v‖ < ‖a‖ + d := by
  have hdist : ‖v - a‖ < d := lt_of_not_ge (fun h => hv (density_zero hd a v h))
  have hnorm := norm_add_le (v - a) a
  rw [sub_add_cancel] at hnorm
  linarith

theorem density_le {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) :
    density d a v ≤ (d ^ 3)⁻¹ * bound :=
  mul_le_mul_of_nonneg_left (J_le _) (inv_nonneg.mpr (pow_nonneg hd _))

theorem integrable_J_entropy : Integrable (fun v => J v * |Real.log (J v)|) := by
  have hc : Continuous (fun v => |J v * Real.log (J v)|) :=
    (Real.continuous_mul_log.comp J_smooth.continuous).abs
  have hs : HasCompactSupport (fun v => |J v * Real.log (J v)|) := by
    apply J_compact.mono
    intro v hv
    by_contra hj
    have hz : J v = 0 := by simpa only [Function.mem_support, not_not] using hj
    simp only [Function.mem_support, hz, zero_mul, abs_zero, ne_eq, not_true_eq_false] at hv
  have hi : Integrable (fun v => |J v * Real.log (J v)|) :=
    hc.integrable_of_hasCompactSupport hs
  convert hi using 1
  funext v
  rw [abs_mul, abs_of_nonneg (J_nonneg v)]

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # A narrow thermal kernel converges to its center against Lipschitz tests -/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace BoltzmannNonuniqueness.JetThermalLaw

theorem test_error_integrable_le {d : ℝ} (hd : 0 < d) (a : Velocity)
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Integrable (fun v => |φ v-φ a| *density d a v) ∧
      (∫ v, |φ v-φ a| *density d a v) ≤ (L:ℝ)*d := by
  have hn (v) : 0 ≤ density d a v := density_nonneg hd.le a v
  have hb (v) : |φ v-φ a| *density d a v ≤ ((L:ℝ)*d)*density d a v := by
    by_cases hz : density d a v = 0
    · simp only [hz,mul_zero,le_refl]
    have hdist : ‖v-a‖ < d := lt_of_not_ge (fun h => hz (density_zero hd a v h))
    have ht : |φ v-φ a| ≤ (L:ℝ)*‖v-a‖ := by
      simpa only [dist_eq_norm,Real.norm_eq_abs] using hφ.dist_le_mul v a
    exact mul_le_mul_of_nonneg_right (ht.trans (mul_le_mul_of_nonneg_left hdist.le L.coe_nonneg)) (hn v)
  have hi : Integrable (fun v => |φ v-φ a| *density d a v) := by
    apply ((density_integrable hd a).const_mul ((L:ℝ)*d)).mono'
      ((hφ.continuous.measurable.sub measurable_const).abs.mul
        (density_smooth d a).continuous.measurable).aestronglyMeasurable
    filter_upwards [] with v
    change ‖|φ v-φ a| * density d a v‖ ≤ (L:ℝ)*d*density d a v
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hn v))]
    exact hb v
  refine ⟨hi,?_⟩
  have h := integral_mono hi ((density_integrable hd a).const_mul ((L:ℝ)*d)) hb
  simpa only [integral_const_mul,density_mass hd,mul_one] using h

theorem test_integrable {d : ℝ} (hd : 0 < d) (a : Velocity)
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Integrable (fun v => φ v*density d a v) := by
  have he := (test_error_integrable_le hd a hφ).1
  apply (he.add ((density_integrable hd a).const_mul |φ a|)).mono'
    (hφ.continuous.measurable.mul (density_smooth d a).continuous.measurable).aestronglyMeasurable
  filter_upwards [] with v
  change ‖φ v*density d a v‖ ≤ |φ v-φ a| * density d a v+|φ a| * density d a v
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (density_nonneg hd.le a v)]
  calc
    _ ≤ (|φ v-φ a|+|φ a|)*density d a v :=
      mul_le_mul_of_nonneg_right (by simpa only [sub_add_cancel] using abs_add_le (φ v-φ a) (φ a))
        (density_nonneg hd.le a v)
    _ = _ := by ring

theorem test_average_error_le {d : ℝ} (hd : 0 < d) (a : Velocity)
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |(∫ v, φ v*density d a v)-φ a| ≤ (L:ℝ)*d := by
  have hi := test_integrable hd a hφ
  have hc := (density_integrable hd a).const_mul (φ a)
  have hEq : (∫ v, φ v*density d a v)-φ a =
      ∫ v, (φ v-φ a)*density d a v := by
    simp_rw [sub_mul]
    rw [integral_sub hi hc,integral_const_mul,density_mass hd,mul_one]
  rw [hEq]
  have hnorm := norm_integral_le_integral_norm (μ := volume) (fun v => (φ v-φ a)*density d a v)
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (density_nonneg hd.le a _)] at hnorm
  exact hnorm.trans (test_error_integrable_le hd a hφ).2

theorem test_average_tendsto {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (hdlim : Tendsto d atTop (𝓝 0)) (a : Velocity)
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Tendsto (fun n => ∫ v, φ v*density (d n) a v) atTop (𝓝 (φ a)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using test_average_error_le (hd n) a hφ)
  simpa only [mul_zero] using hdlim.const_mul (L:ℝ)

theorem test_average_center_error_le {d : ℝ} (hd : 0 < d) (a v : Velocity)
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    |(∫ w, φ w*density d a w)-φ v| ≤ (L:ℝ)*(d+‖a-v‖) := by
  have hv : |φ a-φ v| ≤ (L:ℝ)*‖a-v‖ := by
    simpa only [dist_eq_norm,Real.norm_eq_abs] using hφ.dist_le_mul a v
  calc
    _ ≤ |(∫ w, φ w*density d a w)-φ a|+|φ a-φ v| := abs_sub_le _ _ _
    _ ≤ (L:ℝ)*d+(L:ℝ)*‖a-v‖ := add_le_add (test_average_error_le hd a hφ) hv
    _ = _ := by ring

theorem test_average_moving_center_tendsto {d : ℕ → ℝ} {a : ℕ → Velocity}
    (hd : ∀ n, 0 < d n) (hdlim : Tendsto d atTop (𝓝 0))
    {v : Velocity} (halim : Tendsto a atTop (𝓝 v))
    {φ : Velocity → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Tendsto (fun n => ∫ w, φ w*density (d n) (a n) w) atTop (𝓝 (φ v)) := by
  have hdist : Tendsto (fun n => ‖a n-v‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (halim.sub (tendsto_const_nhds (x := v))).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using test_average_center_error_le (hd n) (a n) v hφ)
  simpa only [zero_add,mul_zero] using (hdlim.add hdist).const_mul (L:ℝ)

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # Absolute-entropy bounds under thermal scaling and translation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetThermalEntropy

def entropy (x : ℝ) : ℝ := x * |Real.log x|

theorem entropy_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ entropy x :=
  mul_nonneg hx (abs_nonneg _)

theorem entropy_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropy (x * y) ≤ y * entropy x + x * entropy y := by
  obtain rfl | hx := hx.eq_or_lt
  · simp [entropy]
  obtain rfl | hy := hy.eq_or_lt
  · simp [entropy]
  have h := mul_le_mul_of_nonneg_left (abs_add_le (Real.log x) (Real.log y))
    (mul_nonneg hx.le hy.le)
  rw [← Real.log_mul hx.ne' hy.ne'] at h
  unfold entropy
  nlinarith only [h]

theorem continuous_entropy_comp {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) : Continuous (fun x => entropy (f x)) := by
  have he : (fun x => entropy (f x)) = fun x => |f x * Real.log (f x)| := by
    funext x
    simp only [entropy, abs_mul, abs_of_nonneg (hpos x)]
  rw [he]
  exact (Real.continuous_mul_log.comp hf).abs

/-- Pointwise bound with a constant independent of the profile center. -/
theorem density_entropy_bound {d : ℝ} (hd : 0 < d) (a v : Velocity) :
    entropy (density d a v) ≤ (3 * |Real.log d|) * density d a v +
      scaled d a (fun w => entropy (J w)) v := by
  have he := entropy_mul_le (inv_nonneg.mpr (pow_nonneg hd.le 3)) (J_nonneg (d⁻¹ • (v - a)))
  have hlog : |Real.log ((d ^ 3)⁻¹)| = 3 * |Real.log d| := by
    rw [Real.log_inv, Real.log_pow, abs_neg, abs_mul]
    norm_num
  unfold density scaled
  unfold entropy at he
  rw [hlog] at he
  unfold entropy
  nlinarith only [he]

def entropyConstant : ℝ := ∫ w, entropy (J w)

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun w => entropy_nonneg (J_nonneg w))

theorem density_entropy_integrable {d : ℝ} (hd : 0 < d) (a : Velocity) :
    Integrable (fun v => entropy (density d a v)) := by
  have hi := ((density_integrable hd a).const_mul (3 * |Real.log d|)).add
    (integrable_scaled integrable_J_entropy hd a)
  apply hi.mono'
  · exact (continuous_entropy_comp (density_smooth d a).continuous
      (density_nonneg hd.le a)).aestronglyMeasurable
  · filter_upwards [] with v
    rw [Real.norm_of_nonneg (entropy_nonneg (density_nonneg hd.le a v))]
    exact density_entropy_bound hd a v

theorem density_entropy_integral {d : ℝ} (hd : 0 < d) (a : Velocity) :
    (∫ v, entropy (density d a v)) ≤ 3 * |Real.log d| + entropyConstant := by
  have hi₁ := (density_integrable hd a).const_mul (3 * |Real.log d|)
  have hi₂ := integrable_scaled integrable_J_entropy hd a
  apply (integral_mono (density_entropy_integrable hd a) (hi₁.add hi₂)
    (density_entropy_bound hd a)).trans_eq
  dsimp only [Pi.add_apply]
  rw [integral_add hi₁ hi₂, integral_const_mul, density_mass hd, integral_scaled _ hd]
  simp only [mul_one, entropyConstant, entropy]

end BoltzmannNonuniqueness.JetThermalEntropy

end

end

section

/-! # The integrable hyperbolic axial weight of the cold datum -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetAxialWeight

/-- The manuscript's `S(ℓ) = sech² ℓ`. -/
def S (x : ℝ) : ℝ := (Real.cosh x)⁻¹ ^ 2

theorem S_pos (x : ℝ) : 0 < S x := by unfold S; positivity

theorem S_le_one (x : ℝ) : S x ≤ 1 := by
  have hc := Real.one_le_cosh x
  have hi : (Real.cosh x)⁻¹ ≤ 1 := (inv_le_one₀ (Real.cosh_pos x)).mpr hc
  unfold S
  nlinarith [inv_nonneg.mpr (Real.cosh_pos x).le]

theorem continuous_S : Continuous S := by
  unfold S
  exact (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 2

theorem tanh_derivative (x : ℝ) : HasDerivAt Real.tanh (S x) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 = S x := by
    have hid := Real.cosh_sq_sub_sinh_sq x
    unfold S
    rw [← pow_two, ← pow_two, hid]
    field_simp
  rw [he] at h
  have ht : Real.tanh = fun z => Real.sinh z / Real.cosh z :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [ht]
  exact h

theorem intervalIntegral_S (a b : ℝ) :
    (∫ x in a..b, S x) = Real.tanh b - Real.tanh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => tanh_derivative x)
    (continuous_S.intervalIntegrable a b)

theorem intervalIntegral_S_le_two (a b : ℝ) : (∫ x in a..b, S x) ≤ 2 := by
  rw [intervalIntegral_S]
  linarith [Real.tanh_lt_one b, Real.neg_one_lt_tanh a]

theorem integrable_S : Integrable S := by
  apply integrable_of_intervalIntegral_norm_bounded (2 : ℝ)
    (a := fun r : ℝ => -r) (b := fun r : ℝ => r)
    (l := atTop)
    (fun r => (continuous_S.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    tendsto_neg_atTop_atBot tendsto_id
  apply Eventually.of_forall
  intro r
  have he : (fun x : ℝ => ‖S x‖) = S := by
    funext x
    exact Real.norm_of_nonneg (S_pos x).le
  rw [he]
  exact intervalIntegral_S_le_two _ _

theorem scaled_derivative (γ s x : ℝ) :
    HasDerivAt (fun z => Real.tanh (γ * z / s)) ((γ / s) * S (γ * x / s)) x := by
  have h := (tanh_derivative (γ * x / s)).comp x
    (((hasDerivAt_id x).const_mul γ).div_const s)
  have he : S (γ * x / s) * (γ * 1 / s) = (γ / s) * S (γ * x / s) := by ring
  rw [he] at h
  exact h

theorem scaled_intervalIntegral {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) =
      (s / γ) * (Real.tanh (γ * b / s) - Real.tanh (γ * a / s)) := by
  have hc : Continuous (fun z : ℝ => S (γ * z / s)) :=
    continuous_S.comp ((continuous_const.mul continuous_id).div_const s)
  have hd (x : ℝ) : HasDerivAt (fun z => (s / γ) * Real.tanh (γ * z / s))
      (S (γ * x / s)) x := by
    have h := (scaled_derivative γ s x).const_mul (s / γ)
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  ring

theorem scaled_intervalIntegral_le {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) ≤ 2 * s / γ := by
  rw [scaled_intervalIntegral hγ hs]
  have hb : Real.tanh (γ * b / s) - Real.tanh (γ * a / s) ≤ 2 := by
    linarith [Real.tanh_lt_one (γ * b / s), Real.neg_one_lt_tanh (γ * a / s)]
  have h := mul_le_mul_of_nonneg_left hb (div_pos hs hγ).le
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness.JetAxialWeight

end

end

section

/-! # Exponential control of the cold datum's axial entropy -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetAxialEntropy

theorem integrable_exp_neg_abs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx
    dsimp only
    change x ≤ 0 at hx
    rw [abs_of_nonpos hx, neg_neg]
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos hx]
  have h := hneg.union hpos
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem cosh_lower (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|x|)]

theorem cosh_upper (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -|x| ≤ |x| by linarith [abs_nonneg x])
  linarith

theorem S_exp_bound (x : ℝ) : S x ≤ 4 * Real.exp (-2 * |x|) := by
  have hi := (inv_le_inv₀ (Real.cosh_pos x) (by positivity : 0 < Real.exp |x| / 2)).mpr
    (cosh_lower x)
  have he : (Real.exp |x| / 2)⁻¹ = 2 * Real.exp (-|x|) := by
    rw [inv_div, Real.exp_neg]
    ring
  rw [he] at hi
  have hs := (sq_le_sq₀ (inv_nonneg.mpr (Real.cosh_pos x).le) (by positivity)).mpr hi
  change S x ≤ (2 * Real.exp (-|x|)) ^ 2 at hs
  convert hs using 1
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num

theorem log_S_bound (x : ℝ) : |Real.log (S x)| ≤ 2 * |x| := by
  have hlog : 0 ≤ Real.log (Real.cosh x) := Real.log_nonneg (Real.one_le_cosh x)
  have hb : Real.log (Real.cosh x) ≤ |x| := by
    have h := Real.log_le_log (Real.cosh_pos x) (cosh_upper x)
    simpa only [Real.log_exp] using h
  simp only [S, Real.log_pow, Real.log_inv, abs_mul, abs_neg,
    abs_of_nonneg hlog]
  norm_num
  linarith

theorem entropy_exp_bound (x : ℝ) : S x * |Real.log (S x)| ≤ 8 * Real.exp (-|x|) := by
  have hb := mul_le_mul (S_exp_bound x) (log_S_bound x)
    (abs_nonneg _) (by positivity : 0 ≤ 4 * Real.exp (-2 * |x|))
  have he : |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
    have hh : |x| ≤ Real.exp |x| :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |x|)
    have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-2 * |x|)).le
    rw [← Real.exp_add] at h
    convert h using 1
    congr 1
    ring
  nlinarith

theorem integrable_axial_entropy : Integrable (fun x : ℝ => S x * |Real.log (S x)|) := by
  apply (integrable_exp_neg_abs.const_mul 8).mono'
  · exact (continuous_S.mul ((continuous_S.log (fun x => (S_pos x).ne')).abs)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (S_pos x).le (abs_nonneg _))]
    exact entropy_exp_bound x

end BoltzmannNonuniqueness.JetAxialEntropy

end

end

section

/-! # Dilated annular margins vanish away from the limiting interfaces -/

noncomputable section

open Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem mem_annularCore_dilation {r : ℝ} (hr : 0 < r) (η s : ℝ) (y : Transverse) :
    r • y ∈ annularCore η (r*s) ↔
      s+gapCoefficient η*r*s^2 < ‖y‖ ∧ ‖y‖ < Real.exp η*s-gapCoefficient η*r*s^2 := by
  change r*s+gapCoefficient η*(r*s)^2 < ‖r • y‖ ∧
    ‖r • y‖ < Real.exp η*(r*s)-gapCoefficient η*(r*s)^2 ↔ _
  rw [norm_smul,Real.norm_of_nonneg hr.le]
  rw [show r*s+gapCoefficient η*(r*s)^2 = r*(s+gapCoefficient η*r*s^2) by ring,
    show Real.exp η*(r*s)-gapCoefficient η*(r*s)^2 =
      r*(Real.exp η*s-gapCoefficient η*r*s^2) by ring]
  simp only [mul_lt_mul_iff_right₀ hr]

theorem eventually_annularCore_dilation {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (y w : Transverse)
    (hy : ‖y‖ ≠ μ) (hy' : ‖y‖ ≠ Real.exp η*μ) :
    ∀ᶠ n in atTop,
      (r n • (y-t • (d n • w)) ∈ annularCore η (r n*s n) ↔
        μ < ‖y‖ ∧ ‖y‖ < Real.exp η*μ) := by
  have hnorm : Tendsto (fun n => ‖y-t • (d n • w)‖) atTop (𝓝 ‖y‖) := by
    simpa only [zero_smul,smul_zero,sub_zero] using
      ((tendsto_const_nhds (x := y)).sub ((hdlim.smul_const w).const_smul t)).norm
  have hmargin : Tendsto (fun n => gapCoefficient η*r n*s n^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hrlim.const_mul (gapCoefficient η)).mul (hslim.pow 2)
  have hlo : Tendsto (fun n => s n+gapCoefficient η*r n*s n^2) atTop (𝓝 μ) := by
    simpa only [add_zero] using hslim.add hmargin
  have hhi : Tendsto (fun n => Real.exp η*s n-gapCoefficient η*r n*s n^2) atTop
      (𝓝 (Real.exp η*μ)) := by simpa only [sub_zero] using (hslim.const_mul (Real.exp η)).sub hmargin
  by_cases hl : μ < ‖y‖
  · by_cases hu : ‖y‖ < Real.exp η*μ
    · filter_upwards [hlo.eventually_lt hnorm hl,hnorm.eventually_lt hhi hu] with n hn hn'
      rw [mem_annularCore_dilation (hr n)]
      exact iff_of_true ⟨hn,hn'⟩ ⟨hl,hu⟩
    · have hu' : Real.exp η*μ < ‖y‖ := lt_of_le_of_ne (le_of_not_gt hu) (Ne.symm hy')
      filter_upwards [hhi.eventually_lt hnorm hu'] with n hn
      rw [mem_annularCore_dilation (hr n)]
      exact iff_of_false (fun h => (not_lt_of_ge hn.le) h.2) (fun h => hu h.2)
  · have hl' : ‖y‖ < μ := lt_of_le_of_ne (le_of_not_gt hl) hy
    filter_upwards [hnorm.eventually_lt hlo hl'] with n hn
    rw [mem_annularCore_dilation (hr n)]
    exact iff_of_false (fun h => (not_lt_of_ge hn.le) h.1) (fun h => hl h.1)

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Uniform mass and centered first moment of the barrier Gaussian -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGaussianMoments

def kernel (b : ℝ) (v : Velocity) : ℝ := Real.exp (-b * ‖v‖ ^ 2)

private theorem radial_integrable {b r : ℝ} (hb : 0 < b) (hr : -3 < r) :
    Integrable (fun v : Velocity => ‖v‖ ^ r * kernel b v) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Velocity)
    (f := fun t : ℝ => t ^ r * Real.exp (-b * t ^ 2))).mpr
  have hi : IntegrableOn (fun t : ℝ => t ^ (r + 2) * Real.exp (-b * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  rw [Real.rpow_add ht' r 2, Real.rpow_two]
  ring

theorem kernel_integrable {b : ℝ} (hb : 0 < b) : Integrable (kernel b) := by
  simpa only [Real.rpow_zero, one_mul] using radial_integrable (r := 0) hb (by norm_num)

theorem moment_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Velocity => ‖v‖ * kernel b v) := by
  simpa only [Real.rpow_one] using radial_integrable (r := 1) hb (by norm_num)

def mass : ℝ := ∫ v, kernel 1 v
def moment : ℝ := ∫ v : Velocity, ‖v‖ * kernel 1 v

theorem mass_nonneg : 0 ≤ mass := integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem moment_nonneg : 0 ≤ moment := integral_nonneg (fun _ => by
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

theorem kernel_le {b : ℝ} (hb : 1 ≤ b) (v : Velocity) : kernel b v ≤ kernel 1 v := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem integral_kernel_le {b : ℝ} (hb : 1 ≤ b) : (∫ v, kernel b v) ≤ mass :=
  integral_mono (kernel_integrable (lt_of_lt_of_le zero_lt_one hb))
    (kernel_integrable zero_lt_one) (kernel_le hb)

theorem integral_moment_le {b : ℝ} (hb : 1 ≤ b) :
    (∫ v : Velocity, ‖v‖ * kernel b v) ≤ moment :=
  integral_mono (moment_integrable (lt_of_lt_of_le zero_lt_one hb))
    (moment_integrable zero_lt_one)
    (fun v => mul_le_mul_of_nonneg_left (kernel_le hb v) (norm_nonneg v))

theorem centered_scaled_eq {d : ℝ} (hd : 0 < d) (b : ℝ) (u v : Velocity) :
    ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v =
      d * JetThermalLaw.scaled d u (fun w => ‖w‖ * kernel b w) v := by
  unfold JetThermalLaw.scaled
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  field_simp

theorem centered_scaled_integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (u : Velocity) :
    Integrable (fun v => ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) := by
  simpa only [centered_scaled_eq hd b u] using
    (JetThermalLaw.integrable_scaled (moment_integrable hb) hd u).const_mul d

theorem integral_centered_scaled {d : ℝ} (hd : 0 < d) (b : ℝ) (u : Velocity) :
    (∫ v, ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) =
      d * (∫ v : Velocity, ‖v‖ * kernel b v) := by
  simp_rw [centered_scaled_eq hd b u]
  rw [integral_const_mul, JetThermalLaw.integral_scaled _ hd u]

end BoltzmannNonuniqueness.JetGaussianMoments

end

end

section

/-! # Explicit points in both stripe-annulus masks -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskNonempty

def first (s : ℝ) (a : Bool) : ℝ := (if a then 1 / 8 else 5 / 8) * s ^ 2

def radius (η s : ℝ) : ℝ := (s + Real.exp η * s) / 2

def point (η s : ℝ) (a : Bool) : Transverse :=
  WithLp.toLp 2 ![first s a, Real.sqrt ((radius η s) ^ 2 - (first s a) ^ 2)]

theorem first_bounds {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    0 ≤ first s a ∧ first s a ≤ s := by
  have hsq : s ^ 2 ≤ s / 8 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsmax)]
  cases a <;> simp only [first, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith [sq_nonneg s]

theorem radius_gt {η s : ℝ} (hη : 0 < η) (hs : 0 < s) : s < radius η s := by
  have he := mul_lt_mul_of_pos_right (Real.one_lt_exp_iff.mpr hη) hs
  unfold radius
  linarith

theorem point_norm {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    ‖point η s a‖ = radius η s := by
  have hfirst := first_bounds hs hsmax a
  have hr := radius_gt hη hs
  have hsqrt : 0 ≤ (radius η s) ^ 2 - (first s a) ^ 2 := by nlinarith
  have hn : ‖point η s a‖ ^ 2 = (radius η s) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [point, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.sq_sqrt hsqrt]
    ring
  nlinarith [norm_nonneg (point η s a)]

theorem point_mem {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    point η s a ∈ mask η s a := by
  have he : 0 < Real.exp η - 1 := by linarith [Real.one_lt_exp_iff.mpr hη]
  have hwidth : gapCoefficient η * s ^ 2 < (Real.exp η - 1) * s / 2 := by
    unfold gapCoefficient
    have hp : 0 < (Real.exp η - 1) * s := mul_pos he hs
    have hm := mul_le_mul_of_nonneg_left hsmax hp.le
    nlinarith
  constructor
  · change s + gapCoefficient η * s ^ 2 < ‖point η s a‖ ∧
      ‖point η s a‖ < Real.exp η * s - gapCoefficient η * s ^ 2
    rw [point_norm hη hs hsmax]
    unfold radius
    constructor <;> linarith
  · change ∃ k : ℤ, ((k : ℝ) + if a then 0 else 1 / 2) * s ^ 2 < (point η s a) 0 ∧
      (point η s a) 0 < ((k : ℝ) + (if a then 0 else 1 / 2) + 1 / 4) * s ^ 2
    refine ⟨0, ?_⟩
    have hs2 := sq_pos_of_pos hs
    cases a <;> simp only [point, first, PiLp.toLp_apply, Matrix.cons_val_zero, Int.cast_zero,
      Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith

theorem mask_nonempty {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    (mask η s a).Nonempty := ⟨point η s a, point_mem hη hs hsmax a⟩

end BoltzmannNonuniqueness.JetMaskNonempty

end

end

section

/-! # A uniform Gaussian sum over integer copies in the fundamental cell -/

noncomputable section

open scoped BigOperators

namespace BoltzmannNonuniqueness.JetLatticeGaussian

def exponential (n : ℤ) : ℝ := Real.exp (-|(n : ℝ)|)

theorem summable_exponential : Summable exponential := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [exponential, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      Real.summable_exp_neg_nat
  · simpa only [exponential, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      Real.summable_exp_neg_nat

def gaussian (b R ξ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-b * (max (|ξ - (n : ℝ)| - R) 0) ^ 2)

def constant : ℝ := Real.exp 3 * ∑' n : ℤ, exponential n

theorem pointwise_bound {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) (n : ℤ) :
    gaussian b R ξ n ≤ Real.exp 3 * exponential n := by
  have hr : 0 ≤ max (|ξ - (n : ℝ)| - R) 0 := le_max_right _ _
  have hnr : |(n : ℝ)| ≤ max (|ξ - (n : ℝ)| - R) 0 + 2 := by
    have htri := abs_add_le ((n : ℝ) - ξ) ξ
    rw [sub_add_cancel, abs_sub_comm (n : ℝ) ξ] at htri
    have hm := le_max_left (|ξ - (n : ℝ)| - R) 0
    linarith
  have hsq : |(n : ℝ)| ≤ (max (|ξ - (n : ℝ)| - R) 0) ^ 2 + 3 := by
    nlinarith [sq_nonneg (max (|ξ - (n : ℝ)| - R) 0 - 1 / 2)]
  unfold gaussian exponential
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (max (|ξ - (n : ℝ)| - R) 0))]

theorem summable_gaussian {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) :
    Summable (gaussian b R ξ) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (pointwise_bound hb hR hξ)
    (summable_exponential.mul_left _)

theorem sum_le {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) :
    (∑' n : ℤ, gaussian b R ξ n) ≤ constant := by
  unfold constant
  rw [← tsum_mul_left]
  exact (summable_gaussian hb hR hξ).tsum_le_tsum (pointwise_bound hb hR hξ)
    (summable_exponential.mul_left _)

end BoltzmannNonuniqueness.JetLatticeGaussian

end

end

section

/-! # The three-dimensional integer-copy Gaussian bound -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetLatticeGaussian

namespace BoltzmannNonuniqueness.JetLatticeProduct

def coordinates : Lattice ≃ ℤ × (ℤ × ℤ) where
  toFun n := (n 0, n 1, n 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

def product (b R : ℝ) (x : Fin 3 → ℝ) (n : Lattice) : ℝ :=
  JetLatticeGaussian.gaussian b R (x 0) (n 0) * JetLatticeGaussian.gaussian b R (x 1) (n 1) * JetLatticeGaussian.gaussian b R (x 2) (n 2)

theorem product_nonneg (b R : ℝ) (x : Fin 3 → ℝ) (n : Lattice) : 0 ≤ product b R x n := by
  unfold product JetLatticeGaussian.gaussian
  positivity


theorem product_eq_exp (b R : ℝ) (x : Fin 3 → ℝ) (n : Lattice) :
    product b R x n = Real.exp (-b * ∑ k : Fin 3, (max (|x k - (n k : ℝ)| - R) 0) ^ 2) := by
  simp only [product, JetLatticeGaussian.gaussian, Fin.sum_univ_three]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sum_eq (b R : ℝ) (x : Fin 3 → ℝ) :
    (∑' n : Lattice, ENNReal.ofReal (product b R x n)) =
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) n)) *
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 1) n)) *
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 2) n)) := by
  rw [← coordinates.symm.tsum_eq (fun n => ENNReal.ofReal (product b R x n))]
  change (∑' p : ℤ × (ℤ × ℤ), ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1 *
    JetLatticeGaussian.gaussian b R (x 1) p.2.1 * JetLatticeGaussian.gaussian b R (x 2) p.2.2)) = _
  have he (p : ℤ × (ℤ × ℤ)) :
      ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1 *
        JetLatticeGaussian.gaussian b R (x 1) p.2.1 * JetLatticeGaussian.gaussian b R (x 2) p.2.2) =
      ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1) *
        ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 1) p.2.1) *
        ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 2) p.2.2) := by
    have h0 : 0 ≤ JetLatticeGaussian.gaussian b R (x 0) p.1 := Real.exp_nonneg _
    have h1 : 0 ≤ JetLatticeGaussian.gaussian b R (x 1) p.2.1 := Real.exp_nonneg _
    rw [ENNReal.ofReal_mul (mul_nonneg h0 h1), ENNReal.ofReal_mul h0]
  simp_rw [he, ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

theorem sum_le {b R : ℝ} {x : Fin 3 → ℝ} (hb : 1 ≤ b) (hR : R ≤ 1)
    (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, ENNReal.ofReal (product b R x n)) ≤ ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hsum (k : Fin 3) : (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x k) n)) ≤
      ENNReal.ofReal JetLatticeGaussian.constant := by
    have hn : ∀ n, 0 ≤ JetLatticeGaussian.gaussian b R (x k) n := fun _ => (Real.exp_pos _).le
    rw [← ENNReal.ofReal_tsum_of_nonneg hn (summable_gaussian hb hR (hx k))]
    exact ENNReal.ofReal_le_ofReal (JetLatticeGaussian.sum_le hb hR (hx k))
  have hC : 0 ≤ JetLatticeGaussian.constant := by
    unfold JetLatticeGaussian.constant exponential
    positivity
  rw [sum_eq, ENNReal.ofReal_pow hC]
  calc
    _ ≤ ENNReal.ofReal JetLatticeGaussian.constant * ENNReal.ofReal JetLatticeGaussian.constant *
        ENNReal.ofReal JetLatticeGaussian.constant := mul_le_mul' (mul_le_mul' (hsum 0) (hsum 1)) (hsum 2)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetLatticeProduct

end

end

section

/-! # The vanishing stripe period and relative thermal shift -/

noncomputable section

open Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def stripeAtPeriod (p : ℝ) (a : Bool) : Set Transverse :=
  {y | ∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*p < y 0 ∧
    y 0 < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*p}

theorem stripe_dilation {r : ℝ} (hr : 0 < r) (s : ℝ) (a : Bool) (y : Transverse) :
    r • y ∈ stripe (r*s) a ↔ y ∈ stripeAtPeriod (r*s^2) a := by
  change (∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*(r*s)^2 < r*y 0 ∧
    r*y 0 < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*(r*s)^2) ↔ _
  have he (b : ℝ) : b*(r*s)^2 = r*(b*(r*s^2)) := by ring
  simp_rw [he,mul_lt_mul_iff_right₀ hr]
  rfl

theorem stripe_period_tendsto_zero {r s : ℕ → ℝ} {μ : ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hs : Tendsto s atTop (𝓝 μ)) :
    Tendsto (fun n => r n*s n^2) atTop (𝓝 0) := by
  simpa only [zero_mul] using hr.mul (hs.pow 2)

theorem relative_thermal_shift_eq {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) (d₀ : ℝ) :
    d₀*(r*s)^10/(r*s^2) = d₀*r^9*s^8 := by
  field_simp

theorem relative_thermal_shift_tendsto_zero {r s : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, r n ≠ 0) (hs : ∀ n, s n ≠ 0)
    (hrlim : Tendsto r atTop (𝓝 0)) (hslim : Tendsto s atTop (𝓝 μ)) (d₀ : ℝ) :
    Tendsto (fun n => d₀*(r n*s n)^10/(r n*s n^2)) atTop (𝓝 0) := by
  simp_rw [relative_thermal_shift_eq (hr _) (hs _)]
  simpa only [zero_pow (by decide : (9:ℕ) ≠ 0),mul_zero,zero_mul] using
    ((hrlim.pow 9).const_mul d₀).mul (hslim.pow 8)

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
