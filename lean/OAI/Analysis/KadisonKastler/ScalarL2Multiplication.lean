import OAI.Analysis.KadisonKastler.ScalarWeakLimit

namespace OAI

/-! # Bounded scalar multiplication on L2

This supplies weak continuity of multiplication by a fixed boundary
function when passing the averaging module identity to the limit.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarL2Mul (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp b).mul (Lp.memLp f)).toLp (fun x => b x * f x)

theorem scalarL2Mul_ae (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    scalarL2Mul b f =ᵐ[μ] fun x => b x * f x := MemLp.coeFn_toLp _

theorem norm_scalarL2Mul_le (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    ‖scalarL2Mul b f‖ ≤ ‖b‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarL2Mul_ae b f, scalarInfinity_ae_norm_le b] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem scalarL2Mul_add (b : ScalarLInfinity μ) (f g : Lp ℂ 2 μ) :
    scalarL2Mul b (f + g) = scalarL2Mul b f + scalarL2Mul b g := by
  apply Lp.ext
  filter_upwards [scalarL2Mul_ae b (f + g), scalarL2Mul_ae b f, scalarL2Mul_ae b g,
    Lp.coeFn_add f g, Lp.coeFn_add (scalarL2Mul b f) (scalarL2Mul b g)]
    with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc, mul_add]

theorem scalarL2Mul_smul (b : ScalarLInfinity μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    scalarL2Mul b (c • f) = c • scalarL2Mul b f := by
  apply Lp.ext
  filter_upwards [scalarL2Mul_ae b (c • f), scalarL2Mul_ae b f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarL2Mul b f)] with x ha hb hc hd
  simp only [Pi.smul_apply, smul_eq_mul] at hc hd
  rw [ha, hc, hd, hb, mul_left_comm]

def scalarL2MulL (b : ScalarLInfinity μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarL2Mul b
      map_add' := scalarL2Mul_add b
      map_smul' := scalarL2Mul_smul b }
    ‖b‖ (norm_scalarL2Mul_le b)

@[simp]
theorem scalarL2MulL_apply (b : ScalarLInfinity μ) (f : Lp ℂ 2 μ) :
    scalarL2MulL b f = scalarL2Mul b f := rfl

variable [IsProbabilityMeasure μ]

theorem scalarInfinityToL2_mul (b f : ScalarLInfinity μ) :
    scalarInfinityToL2 (scalarInfinityMul b f) = scalarL2MulL b (scalarInfinityToL2 f) := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (scalarInfinityMul b f), scalarInfinityMul_ae b f,
    scalarL2Mul_ae b (scalarInfinityToL2 f), scalarInfinityToL2_ae f] with x ha hb hc hd
  exact ha.trans (hb.trans (by rw [scalarL2MulL_apply, hc, hd]))

theorem scalarInfinityMul_of_weak_limits
    {ι : Type*} {l : Filter ι} [l.NeBot] (b : ScalarLInfinity μ)
    (f g : ι → ScalarLInfinity μ) (a c : ScalarLInfinity μ)
    (hfg : ∀ i, scalarInfinityMul b (f i) = g i)
    (hf : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 a))))
    (hg : ∀ y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (g i))) l
      (𝓝 (inner ℂ y (scalarInfinityToL2 c)))) : scalarInfinityMul b a = c := by
  apply scalarInfinityToL2_injective
  apply ext_inner_left ℂ
  intro y
  apply (tendsto_nhds_unique (hg y) ?_).symm
  let F : Lp ℂ 2 μ →L[ℂ] ℂ := (innerSL ℂ y).comp (scalarL2MulL b)
  have h := dual_tendsto_of_inner_tendsto (fun i => scalarInfinityToL2 (f i))
    (scalarInfinityToL2 a) hf F
  change Tendsto (fun i => inner ℂ y (scalarL2MulL b (scalarInfinityToL2 (f i)))) l
    (𝓝 (inner ℂ y (scalarL2MulL b (scalarInfinityToL2 a)))) at h
  simpa only [← scalarInfinityToL2_mul, hfg] using h

end

end KadisonKastler

end OAI
