import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! The real-linear conductivity equation is solved in the actual complex
L2 space by contraction. The operator parameter is only the contraction
property of the Beurling operator; the fixed point and its support are
constructed here. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

abbrev ComplexPlaneL2 := Lp ℂ 2 (volume : Measure EuclideanPlane)

 def conductivityProduct (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) (k : ℝ≥0)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  ((Lp.memLp f).of_le_mul (c := (k : ℝ)) (hq.smul (Lp.aestronglyMeasurable f))
    (by filter_upwards [hb] with x hx
        change ‖q x • f x‖ ≤ (k : ℝ) * ‖f x‖
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))).toLp (fun x => q x • f x)

 theorem conductivityProduct_coe (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) (k : ℝ≥0)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) (f : ComplexPlaneL2) :
    conductivityProduct q hq k hb f =ᵐ[volume] fun x => q x • f x :=
  MemLp.coeFn_toLp _

 def conductivityConj (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLp f

 theorem conductivityConj_coe (f : ComplexPlaneL2) :
    conductivityConj f =ᵐ[volume] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

 def conductivitySource (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume) : ComplexPlaneL2 :=
  (hq.ofReal : MemLp (fun x => (q x : ℂ)) 2 volume).toLp (fun x => (q x : ℂ))

 theorem conductivitySource_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume) :
    conductivitySource q hq =ᵐ[volume] fun x => (q x : ℂ) :=
  MemLp.coeFn_toLp _

 def conductivityIteration (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (f : ComplexPlaneL2) : ComplexPlaneL2 :=
  conductivitySource q hq +
    conductivityProduct q hq.aestronglyMeasurable k hb (conductivityConj (S f))

 theorem conductivityIteration_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (f : ComplexPlaneL2) :
    conductivityIteration q hq k hb S f =ᵐ[volume]
      fun x => (q x : ℂ) * star (1 + S f x) := by
  filter_upwards [Lp.coeFn_add (conductivitySource q hq)
      (conductivityProduct q hq.aestronglyMeasurable k hb (conductivityConj (S f))),
    conductivitySource_coe q hq,
    conductivityProduct_coe q hq.aestronglyMeasurable k hb (conductivityConj (S f)),
    conductivityConj_coe (S f)] with x hx hq' hp hc
  rw [conductivityIteration, hx, Pi.add_apply, hq', hp, hc]
  simp only [Complex.real_smul, star_add, star_one]
  ring

 theorem conductivityIteration_contracting (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ContractingWith k (conductivityIteration q hq k hb S) := by
  refine ⟨hk, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have he : ‖conductivityIteration q hq k hb S f - conductivityIteration q hq k hb S g‖ ≤
      (k : ℝ) * ‖S (f - g)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [conductivityIteration_coe q hq k hb S f,
      conductivityIteration_coe q hq k hb S g,
      Lp.coeFn_sub (conductivityIteration q hq k hb S f) (conductivityIteration q hq k hb S g),
      Lp.coeFn_sub (S f) (S g), hb] with x hf hg hd hs hqx
    rw [Pi.sub_apply, hf, hg] at hd
    rw [hd, map_sub S, hs]
    have ha : (q x : ℂ) * star (1 + S f x) - (q x : ℂ) * star (1 + S g x) =
        (q x : ℂ) * star (S f x - S g x) := by
      simp only [star_add, star_sub, star_one]
      ring
    rw [ha, norm_mul, norm_star, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right hqx (norm_nonneg _)
  exact he.trans (mul_le_mul_of_nonneg_left (hS (f - g)) k.2)

 theorem exists_conductivity_density (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + S g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  let A := conductivityIteration q hq k hb S
  have hA : ContractingWith k A := conductivityIteration_contracting q hq k hk hb S hS
  let g := hA.fixedPoint A
  have hg : A g = g := hA.fixedPoint_isFixedPt
  refine ⟨g, ?_, ?_⟩
  · have hh := conductivityIteration_coe q hq k hb S g
    change conductivityIteration q hq k hb S g = g at hg
    rw [hg] at hh
    exact hh
  · have h := hA.dist_fixedPoint_le (0 : ComplexPlaneL2)
    have hz : A 0 = conductivitySource q hq := by
      apply Lp.ext
      filter_upwards [conductivityIteration_coe q hq k hb S 0,
        conductivitySource_coe q hq, Lp.coeFn_zero ℂ 2 (volume : Measure EuclideanPlane)] with x hx hq' h0
      rw [hx, map_zero, h0, Pi.zero_apply, add_zero, star_one, mul_one, hq']
    simpa only [g, dist_zero_left, hz] using h

 theorem conductivity_density_support {q : EuclideanPlane → ℝ}
    {S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2} {g : ComplexPlaneL2}
    (hg : ∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + S g x))
    {F : Set EuclideanPlane} (hq : ∀ x ∉ F, q x = 0) :
    ∀ᵐ x ∂volume, x ∉ F → g x = 0 := by
  filter_upwards [hg] with x hx hF
  rw [hx, hq x hF, Complex.ofReal_zero, zero_mul]

end CircleDomainRigidity

end

end OAI
