import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import OAI.AlgebraicGeometry.PlaneCurves.MultiplierBundles

namespace OAI

/-!
# Common charts and compactness of the multiplicative torus; Local charts and chart coverage of the multiplicative torus; Holomorphic fibre charts of multiplier line bundles; Connectedness of the multiplicative torus
-/

section

/-! Fixed chart bounds in §3: genuine complex exponential and logarithmic
period lattice. Quotient and marked-point bridges are proved from these bounds. -/
namespace Nagata.Workers.W05
open Filter
open scoped Topology

/-- The distance to every integer is at least the smaller endpoint distance. -/
theorem integer_gap_lower {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hδa : δ ≤ a) (hδ1 : δ ≤ 1 - a) (k : ℤ) : δ ≤ |(k : ℝ) - a| := by
  by_cases hk : k ≤ 0
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith : (k : ℝ) - a ≤ 0)]
    linarith
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - a)]
    linarith

/-- A positive real period larger than the disk diameter forces the deck index to vanish. -/
theorem integer_mul_small {R L : ℝ} (hR : 0 < R) (hL : 2 * R < |L|)
    (k : ℤ) (hk : |(k : ℝ) * L| < 2 * R) : k = 0 := by
  rw [abs_mul] at hk
  have habs : |(k : ℝ)| < 1 := by
    by_contra hh
    have hge : 1 ≤ |(k : ℝ)| := le_of_not_gt hh
    nlinarith [abs_nonneg (k : ℝ)]
  have hkI : |k| < 1 := by exact_mod_cast habs
  have hkIbound := abs_lt.mp hkI
  omega

/-- Real and imaginary parts of a difference between two points in the disk. -/
theorem disk_difference_bounds {R : ℝ} {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ < R) :
    |(y - x).re| < 2 * R ∧ |(y - x).im| < 2 * R := by
  have hnorm : ‖y - x‖ < 2 * R := lt_of_le_of_lt (norm_sub_le y x) (by linarith)
  exact ⟨(Complex.abs_re_le_norm _).trans_lt hnorm,
    (Complex.abs_im_le_norm _).trans_lt hnorm⟩

/-- No nonzero logarithmic period can join two points in the fixed disk. -/
theorem common_disk_lattice_unique {R L : ℝ} (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hL : 2 * R < |L|) {x y : ℂ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (a b : ℤ)
    (hxy : y - x = (a : ℂ) * (L : ℂ) + (b : ℂ) * (2 * Real.pi * Complex.I)) :
    a = 0 ∧ b = 0 ∧ y = x := by
  obtain ⟨hre, him⟩ := disk_difference_bounds hx hy
  have heqre : (y - x).re = (a : ℝ) * L := by
    simpa using congrArg Complex.re hxy
  have heqim : (y - x).im = (b : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hxy
  have ha : a = 0 := integer_mul_small hR hL a (heqre ▸ hre)
  have hpiper : 2 * R < |2 * Real.pi| := by
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos : 0 < 2 * Real.pi)]
    linarith [Real.pi_pos]
  have hb : b = 0 := integer_mul_small hR hpiper b (heqim ▸ him)
  refine ⟨ha, hb, ?_⟩
  apply sub_eq_zero.mp
  simpa [ha, hb] using hxy

/-- The fibre exponential is injective on the same fixed disk. -/
theorem exp_injective_on_disk {R : ℝ} (hRpi : R < Real.pi / 2) :
    Set.InjOn Complex.exp {x : ℂ | ‖x‖ < R} := by
  intro x hx y hy heq
  have hxabs := (Complex.abs_im_le_norm x).trans_lt hx
  have hyabs := (Complex.abs_im_le_norm y).trans_lt hy
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ heq <;>
    linarith [abs_le.mp (le_of_lt hxabs), abs_le.mp (le_of_lt hyabs), Real.pi_pos]

/-- Explicit small-parameter requirements eventually hold as tau tends to zero positively. -/
theorem eventually_common_chart_bounds {R δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
      2 * R < |Real.log τ| ∧ R < δ * |Real.log τ| := by
  have hlog : ∀ᶠ τ : ℝ in 𝓝[>] 0, Real.log τ < - max (2 * R) (R / δ) :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have hpos : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ := self_mem_nhdsWithin
  have hone : ∀ᶠ τ : ℝ in 𝓝[>] 0, τ < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hpos, hone] with τ hlog hpos hone
  have habs : max (2 * R) (R / δ) < |Real.log τ| := by
    have h := neg_le_abs (Real.log τ)
    linarith
  have hR : R / δ < |Real.log τ| := (le_max_right _ _).trans_lt habs
  exact ⟨hpos, hone, (le_max_left _ _).trans_lt habs,
    by nlinarith [(div_lt_iff₀ hδ).mp hR]⟩

/-- A positive real period as an actual nonzero complex number. -/
noncomputable def positivePeriod (τ : ℝ) (hτ : 0 < τ) : ℂˣ :=
  Units.mk0 (τ : ℂ) (by exact_mod_cast ne_of_gt hτ)

/-- The covering-space point tau^s, expressed through the genuine real logarithm. -/
noncomputable def rayPoint (τ s : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp ((s * Real.log τ : ℝ) : ℂ)) (Complex.exp_ne_zero _)

/-- The actual covering-space chart x ↦ tau^x0 exp x. -/
noncomputable def chartPoint (τ x0 : ℝ) (x : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp ((x0 * Real.log τ : ℝ) : ℂ) * Complex.exp x)
    (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))

/-- The common chart into the genuine set quotient of nonzero complex points. -/
noncomputable def torusChart (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (x : ℂ) :
    Nagata.W21.TorusPoint (positivePeriod τ hτ) :=
  Nagata.W21.torusPointMk (positivePeriod τ hτ) (chartPoint τ x0 x)

/-- Exponential orbit equality gives precisely the manuscript's logarithmic lattice. -/
theorem exp_orbit_lattice {τ : ℝ} (hτ : 0 < τ) (x y : ℂ) (a : ℤ)
    (h : Complex.exp y = (τ : ℂ) ^ a * Complex.exp x) :
    ∃ b : ℤ, y - x = (a : ℂ) * (Real.log τ : ℂ) +
      (b : ℂ) * (2 * Real.pi * Complex.I) := by
  have hexp : Complex.exp y = Complex.exp ((a : ℂ) * (Real.log τ : ℂ) + x) := by
    rw [Complex.exp_add, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hτ]
    exact h
  obtain ⟨b, hb⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨b, ?_⟩
  rw [hb]
  ring

/-- The same fixed disk maps injectively to the multiplicative torus quotient. -/
theorem torusChart_injective_on_disk {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|) (x0 : ℝ) :
    Set.InjOn (torusChart τ hτ x0) {x : ℂ | ‖x‖ < R} := by
  intro x hx y hy hxy
  have horbit : Nagata.W21.torusOrbitSetoid (positivePeriod τ hτ)
      (chartPoint τ x0 x) (chartPoint τ x0 y) := Quotient.exact hxy
  obtain ⟨a, ha⟩ := (Nagata.W21.torusOrbitSetoid_iff_coe _ _ _).mp horbit
  have he : Complex.exp y = (τ : ℂ) ^ a * Complex.exp x := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((x0 * Real.log τ : ℝ) : ℂ))
    simpa only [chartPoint, positivePeriod, Units.val_mk0, mul_assoc, mul_left_comm] using ha
  obtain ⟨b, hb⟩ := exp_orbit_lattice hτ x y a he
  exact (common_disk_lattice_unique hR hRpi hlog hx hy a b hb).2.2.symm

/-- A disk point cannot represent a marked point when the endpoint gap dominates its radius. -/
theorem torusChart_avoids_mark {τ R δ x0 xi : ℝ} (hτ : 0 < τ)
    (ha0 : 0 < x0 - xi) (ha1 : x0 - xi < 1)
    (hδa : δ ≤ x0 - xi) (hδ1 : δ ≤ 1 - (x0 - xi))
    (hmargin : R < δ * |Real.log τ|) {x : ℂ} (hx : ‖x‖ < R) :
    torusChart τ hτ x0 x ≠
      Nagata.W21.torusPointMk (positivePeriod τ hτ) (rayPoint τ xi) := by
  intro hq
  have horbit : Nagata.W21.torusOrbitSetoid (positivePeriod τ hτ)
      (chartPoint τ x0 x) (rayPoint τ xi) := Quotient.exact hq
  obtain ⟨a, ha⟩ := (Nagata.W21.torusOrbitSetoid_iff_coe _ _ _).mp horbit
  have hexp : Complex.exp ((xi * Real.log τ : ℝ) : ℂ) =
      (τ : ℂ) ^ a * Complex.exp (((x0 * Real.log τ : ℝ) : ℂ) + x) := by
    simpa only [chartPoint, positivePeriod, rayPoint, Units.val_mk0, Complex.exp_add] using ha
  obtain ⟨b, hb⟩ := exp_orbit_lattice hτ
    (((x0 * Real.log τ : ℝ) : ℂ) + x) ((xi * Real.log τ : ℝ) : ℂ) a hexp
  have hre : xi * Real.log τ - (x0 * Real.log τ + x.re) = (a : ℝ) * Real.log τ := by
    simpa using congrArg Complex.re hb
  have hxre : x.re = ((-a : ℤ) - (x0 - xi)) * Real.log τ := by
    push_cast
    nlinarith [hre]
  have hgap := integer_gap_lower ha0 ha1 hδa hδ1 (-a)
  have habs : δ * |Real.log τ| ≤ |x.re| := by
    rw [hxre, abs_mul]
    exact mul_le_mul_of_nonneg_right hgap (abs_nonneg _)
  have hsmall := (Complex.abs_re_le_norm x).trans_lt hx
  linarith

noncomputable def markedGapValues (x0 : ℝ) (xi : Fin 9 → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i => min (x0 - xi i) (1 - (x0 - xi i)))

theorem markedGapValues_nonempty (x0 : ℝ) (xi : Fin 9 → ℝ) :
    (markedGapValues x0 xi).Nonempty := by
  classical
  exact ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- The actual finite minimum δ_P used in the manuscript. -/
noncomputable def markedGap (x0 : ℝ) (xi : Fin 9 → ℝ) : ℝ :=
  (markedGapValues x0 xi).min' (markedGapValues_nonempty x0 xi)

theorem markedGap_pos (x0 : ℝ) (xi : Fin 9 → ℝ)
    (h : ∀ i, 0 < x0 - xi i ∧ x0 - xi i < 1) : 0 < markedGap x0 xi := by
  classical
  have hmem := Finset.min'_mem (markedGapValues x0 xi) (markedGapValues_nonempty x0 xi)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  change 0 < (markedGapValues x0 xi).min' _
  rw [← hi]
  exact lt_min (h i).1 (by linarith [(h i).2])

theorem markedGap_le (x0 : ℝ) (xi : Fin 9 → ℝ) (i : Fin 9) :
    markedGap x0 xi ≤ x0 - xi i ∧ markedGap x0 xi ≤ 1 - (x0 - xi i) := by
  classical
  have hi : min (x0 - xi i) (1 - (x0 - xi i)) ∈ markedGapValues x0 xi :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hmin : markedGap x0 xi ≤ min (x0 - xi i) (1 - (x0 - xi i)) :=
    Finset.min'_le _ _ hi
  exact ⟨hmin.trans (min_le_left _ _), hmin.trans (min_le_right _ _)⟩

theorem exists_eventual_common_chart (x0 : ℝ) (xi : Fin 9 → ℝ)
    (hxi : ∀ i, 0 < x0 - xi i ∧ x0 - xi i < 1) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧
      0 < markedGap x0 xi ∧
      Set.InjOn Complex.exp {y : ℂ | ‖y‖ < R} ∧
      ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
        2 * R < |Real.log τ| ∧ R < markedGap x0 xi * |Real.log τ| ∧
        ∀ hτ : 0 < τ,
          Set.InjOn (torusChart τ hτ x0) {x : ℂ | ‖x‖ < R} ∧
          ∀ i : Fin 9, ∀ x : ℂ, ‖x‖ < R →
            torusChart τ hτ x0 x ≠
              Nagata.W21.torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)) := by
  let R : ℝ := Real.pi / 4
  have hR : 0 < R := div_pos Real.pi_pos (by norm_num)
  have hRpi : R < Real.pi / 2 := by dsimp [R]; linarith [Real.pi_pos]
  have hδ := markedGap_pos x0 xi hxi
  refine ⟨R, hR, hRpi, hδ, exp_injective_on_disk hRpi, ?_⟩
  filter_upwards [eventually_common_chart_bounds (R := R) hδ] with τ hτ
  refine ⟨hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2, ?_⟩
  intro hpos
  refine ⟨torusChart_injective_on_disk hpos hR hRpi hτ.2.2.1 x0, ?_⟩
  intro i x hx
  exact torusChart_avoids_mark hpos (hxi i).1 (hxi i).2
    (markedGap_le x0 xi i).1 (markedGap_le x0 xi i).2 hτ.2.2.2 hx

end Nagata.Workers.W05

end

section

namespace Nagata.Workers.W05

/-- The logarithmic ray is literally the positive real power used in the source. -/
theorem rayPoint_eq_real_rpow {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    (rayPoint τ s : ℂ) = ((τ ^ s : ℝ) : ℂ) := by
  simp only [rayPoint, Units.val_mk0, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
  congr 2
  ring

/-- The covering chart has exactly the source scalar tau^x0 exp x. -/
theorem chartPoint_eq_real_rpow {τ : ℝ} (hτ : 0 < τ) (x0 : ℝ) (x : ℂ) :
    (chartPoint τ x0 x : ℂ) = ((τ ^ x0 : ℝ) : ℂ) * Complex.exp x := by
  change (rayPoint τ x0 : ℂ) * Complex.exp x = _
  rw [rayPoint_eq_real_rpow hτ]

end Nagata.Workers.W05

end

section

namespace Nagata.Workers.W05

/-- The disk bounds identify the actual integer deck translate, not just the quotient point. -/
theorem chartPoint_deck_unique {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|) (x0 : ℝ)
    {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ < R) (k : ℤ)
    (hk : positivePeriod τ hτ ^ k * chartPoint τ x0 x = chartPoint τ x0 y) :
    k = 0 ∧ x = y := by
  have hscalar := congrArg (fun z : ℂˣ => (z : ℂ)) hk
  have he : Complex.exp y = (τ : ℂ) ^ k * Complex.exp x := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((x0 * Real.log τ : ℝ) : ℂ))
    simpa only [chartPoint, positivePeriod, Units.val_mk0, Units.val_mul,
      Units.val_zpow_eq_zpow_val, mul_assoc, mul_left_comm] using hscalar.symm
  obtain ⟨b, hb⟩ := exp_orbit_lattice hτ x y k he
  have h := common_disk_lattice_unique hR hRpi hlog hx hy k b hb
  exact ⟨h.1, h.2.2.symm⟩

/-- The source formulas into the genuine multiplier-bundle set quotient. -/
noncomputable def multiplierChart (τ : ℝ) (hτ : 0 < τ) (γ : ℂˣ) (n : ℤ)
    (x0 : ℝ) (p : ℂ × ℂ) : Nagata.W21.MultiplierQuotient (positivePeriod τ hτ) γ n :=
  Quotient.mk _ (chartPoint τ x0 p.1, Complex.exp p.2)

/-- For every multiplier and degree, the common polydisk injects into the actual
cyclic total-space quotient; degree zero specializes to the source bundle A. -/
theorem multiplierChart_injective_on_polydisk {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|)
    (γ : ℂˣ) (n : ℤ) (x0 : ℝ) :
    Set.InjOn (multiplierChart τ hτ γ n x0)
      {p : ℂ × ℂ | ‖p.1‖ < R ∧ ‖p.2‖ < R} := by
  intro p hp q hq heq
  obtain ⟨k, hk⟩ : ∃ k : ℤ,
      Nagata.W21.multiplierIterate (positivePeriod τ hτ) γ n k
        (chartPoint τ x0 p.1, Complex.exp p.2) =
        (chartPoint τ x0 q.1, Complex.exp q.2) := Quotient.exact heq
  have hbase : positivePeriod τ hτ ^ k * chartPoint τ x0 p.1 = chartPoint τ x0 q.1 := by
    simpa only [Nagata.W21.multiplierIterate_base] using congrArg Prod.fst hk
  obtain ⟨hk0, hxy⟩ := chartPoint_deck_unique hτ hR hRpi hlog x0 hp.1 hq.1 k hbase
  rw [hk0, Nagata.W21.multiplierIterate_zero] at hk
  have hexp : Complex.exp p.2 = Complex.exp q.2 := congrArg Prod.snd hk
  exact Prod.ext hxy (exp_injective_on_disk hRpi hp.2 hq.2 hexp)

open Filter
open scoped Topology

/-- One fixed polydisk injects into every multiplier total-space quotient for
all sufficiently small positive periods, and its base avoids the nine marks. -/
theorem exists_eventual_common_polydisk (x0 : ℝ) (xi : Fin 9 → ℝ)
    (hxi : ∀ i, 0 < x0 - xi i ∧ x0 - xi i < 1) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧
      ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ ∧ τ < 1 ∧
        ∀ (hτ : 0 < τ) (γ : ℂˣ) (n : ℤ),
          Set.InjOn (multiplierChart τ hτ γ n x0)
            {p : ℂ × ℂ | ‖p.1‖ < R ∧ ‖p.2‖ < R} ∧
          ∀ i : Fin 9, ∀ p : ℂ × ℂ, (‖p.1‖ < R ∧ ‖p.2‖ < R) →
            torusChart τ hτ x0 p.1 ≠
              Nagata.W21.torusPointMk (positivePeriod τ hτ) (rayPoint τ (xi i)) := by
  obtain ⟨R, hR, hRpi, _, _, hevent⟩ := exists_eventual_common_chart x0 xi hxi
  refine ⟨R, hR, hRpi, ?_⟩
  filter_upwards [hevent] with τ hτ
  obtain ⟨hpos, hone, hlog, _, hcharts⟩ := hτ
  refine ⟨hpos, hone, ?_⟩
  intro hperiod γ n
  refine ⟨multiplierChart_injective_on_polydisk hperiod hR hRpi hlog γ n x0, ?_⟩
  intro i p hp
  exact (hcharts hperiod).2 i p.1 hp.1

end Nagata.Workers.W05

end

section

/-! Actual local homeomorphisms for injective open pieces of the period quotient. -/
namespace Nagata.W21

/-- Saturation under the period action, expressed with actual inverse images. -/
theorem torusPointMk_preimage_image {G : Type*} [CommGroup G] (τ : G) (U : Set G) :
    torusPointMk τ ⁻¹' (torusPointMk τ '' U) =
      ⋃ k : ℤ, (fun z : G ↦ τ ^ k * z) ⁻¹' U := by
  ext z
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨k, hk⟩ := (torusPointMk_eq_iff τ z u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨k, by simpa only [Set.mem_preimage, hk] using hu⟩
  · intro hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    exact ⟨τ ^ k * z, hk, ((torusPointMk_eq_iff τ z (τ ^ k * z)).mpr ⟨k, rfl⟩).symm⟩

/-- The period quotient map is open, proved from continuous translations. -/
theorem isOpenMap_torusPointMk {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] (τ : G) : IsOpenMap (torusPointMk τ) := by
  intro U hU
  apply (isQuotientMap_torusPointMk τ).isOpen_preimage.mp
  rw [torusPointMk_preimage_image]
  exact isOpen_iUnion fun k : ℤ ↦ hU.preimage (continuous_const.mul continuous_id)

/-- Every genuinely injective open piece supplies an actual local homeomorphism
onto its image in the torus quotient. The chart injectivity must be proved by the caller. -/
noncomputable def torusLocalChart {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] (τ : G) (U : Set G) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) : OpenPartialHomeomorph G (TorusPoint τ) :=
  OpenPartialHomeomorph.ofContinuousOpen
    (Set.InjOn.toPartialEquiv (torusPointMk τ) U hinj)
    (by change ContinuousOn (torusPointMk τ) U; exact (continuous_torusPointMk τ).continuousOn)
    (by change IsOpenMap (torusPointMk τ); exact isOpenMap_torusPointMk τ)
    (by change IsOpen U; exact hU)

@[simp] theorem torusLocalChart_source {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] (τ : G) (U : Set G) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) : (torusLocalChart τ U hU hinj).source = U := rfl

@[simp] theorem torusLocalChart_target {G : Type*} [CommGroup G] [TopologicalSpace G]
    [ContinuousMul G] (τ : G) (U : Set G) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    (torusLocalChart τ U hU hinj).target = torusPointMk τ '' U := rfl

end Nagata.W21

end

section

/-! Genuine topological local charts for the explicit fixed exponential disk,
using canonical units and quotient topologies. -/
namespace Nagata.Workers.W05

/-- The fixed coordinate disk is open in the complex plane. -/
theorem isOpen_chartDisk (R : ℝ) : IsOpen {x : ℂ | ‖x‖ < R} :=
  isOpen_lt continuous_norm continuous_const

/-- Every disk under consideration lies inside the canonical exponential branch. -/
theorem chartDisk_subset_exp_source {R : ℝ} (hRpi : R < Real.pi / 2) :
    {x : ℂ | ‖x‖ < R} ⊆ Complex.expOpenPartialHomeomorph.source := by
  intro x hx
  have habs := (Complex.abs_im_le_norm x).trans_lt hx
  change -Real.pi < x.im ∧ x.im < Real.pi
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  constructor <;> linarith [Real.pi_pos]

/-- The explicit covering-space chart is continuous for the canonical units topology. -/
theorem continuous_chartPoint (τ x0 : ℝ) : Continuous (chartPoint τ x0) := by
  have hc : Continuous (fun x => (chartPoint τ x0 x : ℂ)) := by
    exact continuous_const.mul Complex.continuous_exp
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  change Continuous (fun x => (chartPoint τ x0 x : ℂ))⁻¹
  exact hc.inv₀ (fun x => Units.ne_zero _)

/-- The image of every open subset of the disk is open among actual nonzero complex points. -/
theorem isOpen_chartPoint_image {R : ℝ} (hRpi : R < Real.pi / 2)
    (τ x0 : ℝ) {U : Set ℂ} (hU : IsOpen U) (hUD : U ⊆ {x : ℂ | ‖x‖ < R}) :
    IsOpen (chartPoint τ x0 '' U) := by
  have hexp : IsOpen (Complex.exp '' U) :=
    Complex.expOpenPartialHomeomorph.isOpen_image_of_subset_source hU
      (hUD.trans (chartDisk_subset_exp_source hRpi))
  have hm : IsOpen ((fun z : ℂ => Complex.exp ((x0 * Real.log τ : ℝ) : ℂ) * z) ''
      (Complex.exp '' U)) :=
    (Homeomorph.mulLeft₀ _ (Complex.exp_ne_zero _)).isOpenMap _ hexp
  have hc : IsOpen ((fun x => (chartPoint τ x0 x : ℂ)) '' U) := by
    simpa only [Set.image_image, chartPoint, Units.val_mk0] using hm
  have heq : chartPoint τ x0 '' U =
      (fun z : ℂˣ => (z : ℂ)) ⁻¹' ((fun x => (chartPoint τ x0 x : ℂ)) '' U) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, Units.ext he⟩
  rw [heq]
  exact hc.preimage Units.continuous_val

/-- The explicit torus chart is continuous for the canonical quotient topology. -/
theorem continuous_torusChart (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) :
    Continuous (torusChart τ hτ x0) :=
  (Nagata.W21.continuous_torusPointMk _).comp (continuous_chartPoint τ x0)

/-- The actual local torus image is open; this is stronger than set injectivity. -/
theorem isOpen_torusChart_image {R : ℝ} (hRpi : R < Real.pi / 2)
    (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) {U : Set ℂ}
    (hU : IsOpen U) (hUD : U ⊆ {x : ℂ | ‖x‖ < R}) :
    IsOpen (torusChart τ hτ x0 '' U) := by
  have hh := Nagata.W21.isOpenMap_torusPointMk (positivePeriod τ hτ)
    (chartPoint τ x0 '' U) (isOpen_chartPoint_image hRpi τ x0 hU hUD)
  change IsOpen ((fun x => Nagata.W21.torusPointMk (positivePeriod τ hτ)
    (chartPoint τ x0 x)) '' U)
  simpa only [Set.image_image] using hh

/-- The disk-restricted quotient chart is an open map. -/
theorem isOpenMap_torusChart_restrict {R : ℝ} (hRpi : R < Real.pi / 2)
    (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) :
    IsOpenMap (({x : ℂ | ‖x‖ < R} : Set ℂ).domRestrict (torusChart τ hτ x0)) := by
  intro V hV
  have hU := (isOpen_chartDisk R).isOpenMap_subtype_val V hV
  have hs : Subtype.val '' V ⊆ {x : ℂ | ‖x‖ < R} := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  have hopen := isOpen_torusChart_image hRpi τ hτ x0 hU hs
  change IsOpen ((fun x : {x : ℂ | ‖x‖ < R} => torusChart τ hτ x0 x) '' V)
  simpa only [Set.image_image] using hopen

/-- The fixed exponential disk is a genuine local homeomorphism into the torus.
Its inverse is continuous on the actual open quotient image. -/
noncomputable def commonTorusOpenPartialHomeomorph {τ R : ℝ}
    (hτ : 0 < τ) (hR : 0 < R) (hRpi : R < Real.pi / 2)
    (hlog : 2 * R < |Real.log τ|) (x0 : ℝ) :
    OpenPartialHomeomorph ℂ (Nagata.W21.TorusPoint (positivePeriod τ hτ)) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    (Set.InjOn.toPartialEquiv (torusChart τ hτ x0) {x : ℂ | ‖x‖ < R}
      (torusChart_injective_on_disk hτ hR hRpi hlog x0))
    (continuous_torusChart τ hτ x0).continuousOn
    (isOpenMap_torusChart_restrict hRpi τ hτ x0)
    (isOpen_chartDisk R)

@[simp] theorem commonTorusOpenPartialHomeomorph_source {τ R : ℝ}
    (hτ : 0 < τ) (hR : 0 < R) (hRpi : R < Real.pi / 2)
    (hlog : 2 * R < |Real.log τ|) (x0 : ℝ) :
    (commonTorusOpenPartialHomeomorph hτ hR hRpi hlog x0).source =
      {x : ℂ | ‖x‖ < R} := rfl

@[simp] theorem commonTorusOpenPartialHomeomorph_target {τ R : ℝ}
    (hτ : 0 < τ) (hR : 0 < R) (hRpi : R < Real.pi / 2)
    (hlog : 2 * R < |Real.log τ|) (x0 : ℝ) :
    (commonTorusOpenPartialHomeomorph hτ hR hRpi hlog x0).target =
      torusChart τ hτ x0 '' {x : ℂ | ‖x‖ < R} := rfl

end Nagata.Workers.W05

end

section

/-! Genuine full-fibre local charts for the multiplier quotient. -/
namespace Nagata.W21

variable {R : Type*} [CommMonoid R]

/-- A base slice for a free period action is a slice for the whole fibre,
including the zero vector. -/
theorem multiplierQuotientMk_injOn_fibre (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (U : Set Rˣ)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    Set.InjOn (multiplierQuotientMk τ γ n) (U ×ˢ (Set.univ : Set R)) := by
  intro p hp q hq he
  obtain ⟨k, hk⟩ := (multiplierQuotientMk_eq_iff τ γ n p q).mp he
  have hb : p.1 = q.1 := hinj hp.1 hq.1
    ((torusPointMk_eq_iff τ p.1 q.1).mpr
      ⟨k, by rw [← multiplierIterate_base τ γ n k p, hk]⟩)
  have hk1 : τ ^ k = 1 := by
    apply mul_right_cancel (b := p.1)
    rw [one_mul, ← multiplierIterate_base τ γ n k p, hk, hb]
  have hk0 := hfree k hk1
  simpa only [hk0, multiplierIterate_zero] using hk

/-- Every point above a base slice has a representative in the full fibre over
that slice; this proves that the local chart covers complete fibres. -/
theorem multiplierQuotientMk_image_fibre (τ γ : Rˣ) (n : ℤ) (U : Set Rˣ) :
    multiplierQuotientMk τ γ n '' (U ×ˢ (Set.univ : Set R)) =
      multiplierQuotientProjection τ γ n ⁻¹' (torusPointMk τ '' U) := by
  ext q
  refine Quotient.inductionOn q ?_
  intro p
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨v.1, hv.1, congrArg (multiplierQuotientProjection τ γ n) he⟩
  · rintro ⟨z, hz, he⟩
    obtain ⟨k, hk⟩ := (torusPointMk_eq_iff τ p.1 z).mp he.symm
    refine ⟨multiplierIterate τ γ n k p, ⟨?_, Set.mem_univ _⟩, ?_⟩
    · simpa only [multiplierIterate_base, hk] using hz
    · exact ((multiplierQuotientMk_eq_iff τ γ n p _).mpr ⟨k, rfl⟩).symm

section Topological
variable [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]

/-- An actual quotient local homeomorphism whose image covers every fibre above
the base slice, rather than a bounded portion of each fibre. -/
noncomputable def multiplierFibreChart (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (U : Set Rˣ) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    OpenPartialHomeomorph (MultiplicativeLineCover R) (MultiplierQuotient τ γ n) :=
  multiplierLocalChart τ γ n (U ×ˢ Set.univ) (hU.prod isOpen_univ)
    (multiplierQuotientMk_injOn_fibre τ γ n hfree U hinj)

@[simp] theorem multiplierFibreChart_source (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (U : Set Rˣ) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    (multiplierFibreChart τ γ n hfree U hU hinj).source = U ×ˢ Set.univ := rfl

@[simp] theorem multiplierFibreChart_target (τ γ : Rˣ) (n : ℤ)
    (hfree : ∀ k : ℤ, τ ^ k = 1 → k = 0) (U : Set Rˣ) (hU : IsOpen U)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    (multiplierFibreChart τ γ n hfree U hU hinj).target =
      multiplierQuotientProjection τ γ n ⁻¹' (torusPointMk τ '' U) :=
  multiplierQuotientMk_image_fibre τ γ n U

end Topological

end Nagata.W21

end

section

/-! Translating an actual identity slice gives charts covering the torus quotient. -/
namespace Nagata.W21
variable {G : Type*} [CommGroup G]

/-- Every translate of an injective base slice remains injective. -/
theorem torusPointMk_injOn_translate (τ c : G) (U : Set G)
    (hinj : Set.InjOn (torusPointMk τ) U) :
    Set.InjOn (torusPointMk τ) ((fun z : G ↦ c⁻¹ * z) ⁻¹' U) := by
  intro p hp q hq he
  obtain ⟨k, hk⟩ := (torusPointMk_eq_iff τ p q).mp he
  have h : c⁻¹ * p = c⁻¹ * q := hinj hp hq
    ((torusPointMk_eq_iff τ (c⁻¹ * p) (c⁻¹ * q)).mpr
      ⟨k, by rw [← mul_assoc, mul_comm (τ ^ k) c⁻¹, mul_assoc, hk]⟩)
  exact mul_left_cancel h

/-- An open identity slice supplies an injective open slice containing any point. -/
theorem exists_open_torus_slice [TopologicalSpace G] [ContinuousMul G]
    (τ : G) (U : Set G) (hU : IsOpen U) (h1 : 1 ∈ U)
    (hinj : Set.InjOn (torusPointMk τ) U) (z : G) :
    ∃ V : Set G, IsOpen V ∧ z ∈ V ∧ Set.InjOn (torusPointMk τ) V := by
  refine ⟨(fun w : G ↦ z⁻¹ * w) ⁻¹' U,
    hU.preimage (continuous_const.mul continuous_id), ?_,
    torusPointMk_injOn_translate τ z U hinj⟩
  simpa only [Set.mem_preimage, inv_mul_cancel] using h1

/-- The actual quotient is covered by the images of these open slices. -/
theorem torus_slice_covers [TopologicalSpace G] [ContinuousMul G]
    (τ : G) (U : Set G) (hU : IsOpen U) (h1 : 1 ∈ U)
    (hinj : Set.InjOn (torusPointMk τ) U) (q : TorusPoint τ) :
    ∃ V : Set G, IsOpen V ∧ Set.InjOn (torusPointMk τ) V ∧ q ∈ torusPointMk τ '' V := by
  refine Quotient.inductionOn q ?_
  intro z
  obtain ⟨V, ho, hz, hi⟩ := exists_open_torus_slice τ U hU h1 hinj z
  exact ⟨V, ho, hi, z, hz, rfl⟩

end Nagata.W21

end

section

/-! Compactness of the actual multiplicative torus for every real 0<tau<1.
The proof gives explicit orbit representatives in the genuine compact annulus. -/
namespace Nagata.Workers.W05

/-- An integer power of a contraction moves every positive real into [tau,1]. -/
theorem exists_int_scale_interval {τ a : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ha : 0 < a) :
    ∃ k : ℤ, τ ≤ τ ^ k * a ∧ τ ^ k * a ≤ 1 := by
  have hL : Real.log τ < 0 := Real.log_neg hτ hτ1
  let N : ℤ := ⌊Real.log a / Real.log τ⌋
  have hlo : (N : ℝ) ≤ Real.log a / Real.log τ := Int.floor_le _
  have hhi : Real.log a / Real.log τ < (N : ℝ) + 1 := Int.lt_floor_add_one _
  have hcancel : (Real.log a / Real.log τ) * Real.log τ = Real.log a :=
    div_mul_cancel₀ _ (ne_of_lt hL)
  have hupper := mul_le_mul_of_nonpos_right hlo (le_of_lt hL)
  have hlower := mul_lt_mul_of_neg_right hhi hL
  rw [hcancel] at hupper hlower
  have hscaled : 0 < τ ^ (-N) * a := mul_pos (zpow_pos hτ _) ha
  have hlog : Real.log (τ ^ (-N) * a) = -(N : ℝ) * Real.log τ + Real.log a := by
    rw [Real.log_mul (ne_of_gt (zpow_pos hτ _)) (ne_of_gt ha), Real.log_zpow]
    simp
  refine ⟨-N, ?_, ?_⟩
  · apply (Real.log_le_log_iff hτ hscaled).mp
    rw [hlog]
    linarith
  · apply (Real.log_le_log_iff hscaled zero_lt_one).mp
    rw [hlog, Real.log_one]
    linarith

/-- Every actual complex period orbit has a representative in the closed annulus. -/
theorem exists_zpow_in_annulus {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (z : ℂ) (hz : z ≠ 0) :
    ∃ k : ℤ, τ ≤ ‖(τ : ℂ) ^ k * z‖ ∧ ‖(τ : ℂ) ^ k * z‖ ≤ 1 := by
  obtain ⟨k, hklo, hkhi⟩ := exists_int_scale_interval hτ hτ1 (norm_pos_iff.mpr hz)
  refine ⟨k, ?_⟩
  simpa only [norm_mul, Complex.norm_zpow, Complex.norm_of_nonneg (le_of_lt hτ)]
    using And.intro hklo hkhi

/-- The genuine closed annulus in the complex plane. -/
def closedAnnulus (τ : ℝ) : Set ℂ := {z | τ ≤ ‖z‖ ∧ ‖z‖ ≤ 1}

theorem isCompact_closedAnnulus (τ : ℝ) : IsCompact (closedAnnulus τ) := by
  have hc : IsClosed (closedAnnulus τ) :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2

theorem closedAnnulus_ne_zero {τ : ℝ} (hτ : 0 < τ) (z : closedAnnulus τ) :
    (z : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hτ z.property.1)

/-- The annulus maps to actual nonzero complex points without a chosen surrogate. -/
noncomputable def annulusUnits {τ : ℝ} (hτ : 0 < τ) (z : closedAnnulus τ) : ℂˣ :=
  Units.mk0 (z : ℂ) (closedAnnulus_ne_zero hτ z)

theorem continuous_annulusUnits {τ : ℝ} (hτ : 0 < τ) : Continuous (annulusUnits hτ) := by
  apply Units.continuous_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  change Continuous (Subtype.val : closedAnnulus τ → ℂ)⁻¹
  exact continuous_subtype_val.inv₀ (closedAnnulus_ne_zero hτ)

/-- Every point of the genuine quotient is represented by an annulus point. -/
theorem annulus_torus_surjective {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    Function.Surjective (fun z : closedAnnulus τ =>
      Nagata.W21.torusPointMk (positivePeriod τ hτ) (annulusUnits hτ z)) := by
  intro q
  induction q using Quotient.inductionOn with
  | h z =>
    obtain ⟨k, hklo, hkhi⟩ := exists_zpow_in_annulus hτ hτ1 (z : ℂ) (Units.ne_zero z)
    let w : ℂˣ := positivePeriod τ hτ ^ k * z
    have hw : (w : ℂ) ∈ closedAnnulus τ := by
      simpa only [closedAnnulus, Set.mem_ofPred_eq, w, positivePeriod, Units.val_mul,
        Units.val_zpow_eq_zpow_val, Units.val_mk0] using And.intro hklo hkhi
    refine ⟨⟨(w : ℂ), hw⟩, ?_⟩
    have hwunits : annulusUnits hτ ⟨(w : ℂ), hw⟩ = w := Units.ext rfl
    dsimp only
    rw [hwunits]
    exact ((Nagata.W21.torusPointMk_eq_iff (positivePeriod τ hτ) z w).mpr ⟨k, rfl⟩).symm

/-- The actual torus quotient with its canonical quotient topology is compact. -/
theorem compactSpace_torusPoint {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    CompactSpace (Nagata.W21.TorusPoint (positivePeriod τ hτ)) := by
  let : CompactSpace (closedAnnulus τ) := isCompact_iff_compactSpace.mp (isCompact_closedAnnulus τ)
  have hc : Continuous (fun z : closedAnnulus τ =>
      Nagata.W21.torusPointMk (positivePeriod τ hτ) (annulusUnits hτ z)) :=
    (Nagata.W21.continuous_torusPointMk _).comp (continuous_annulusUnits hτ)
  have hcompact := isCompact_range hc
  rw [(annulus_torus_surjective hτ hτ1).range_eq] at hcompact
  exact ⟨hcompact⟩

end Nagata.Workers.W05

end

section

/-! Connectedness of the actual multiplicative torus for every nonzero period. -/
namespace Nagata.W21

/-- The exponential map surjects onto the actual complex units. -/
theorem chartPoint_zero_surjective :
    Function.Surjective (Nagata.Workers.W05.chartPoint 1 0) := by
  intro z
  refine ⟨Complex.log (z : ℂ), ?_⟩
  apply Units.ext
  simp [Nagata.Workers.W05.chartPoint, Complex.exp_log (Units.ne_zero z)]

/-- The canonical topology on the period quotient is connected, proved from the
continuous surjective exponential parametrization. -/
theorem torusPoint_connectedSpace (τ : ℂˣ) : ConnectedSpace (TorusPoint τ) := by
  have hc : Continuous (fun z : ℂ ↦
      torusPointMk τ (Nagata.Workers.W05.chartPoint 1 0 z)) :=
    (continuous_torusPointMk τ).comp (Nagata.Workers.W05.continuous_chartPoint 1 0)
  have hs : Function.Surjective (fun z : ℂ ↦
      torusPointMk τ (Nagata.Workers.W05.chartPoint 1 0 z)) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    obtain ⟨w, hw⟩ := chartPoint_zero_surjective z
    exact ⟨w, congrArg (torusPointMk τ) hw⟩
  exact hs.connectedSpace hc

end Nagata.W21

end

end OAI
