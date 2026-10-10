import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

namespace OAI

/-!
# Analytic jet composition, normal scaling, and normal velocity limits; Preservation of local order by variable analytic units
-/

section

/-!
# Analytic Taylor order and local coordinate changes

`HasAnalyticOrderAtLeast` refers to an actual convergent local multilinear
power-series expansion, with every coefficient of degree below m zero.
The expansion is existential: multilinear expansions need not be
symmetric or unique, unlike their diagonal homogeneous polynomials.
-/

noncomputable section
namespace Nagata.Workers.W28

open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Low Taylor coefficients of the outer series remain zero after substitution. -/
theorem comp_coeff_eq_zero_below
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (m : ℕ) (hq : ∀ n < m, q n = 0) :
    ∀ n < m, (q.comp p) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply,
    zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [hq c.length (lt_of_le_of_lt c.length_le hn)]
  rfl

/-- Genuine convergent analytic Taylor vanishing of order at least m. -/
def HasAnalyticOrderAtLeast (f : E → F) (x : E) (m : ℕ) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F,
    HasFPowerSeriesAt f p x ∧ ∀ n < m, p n = 0

/-- Analytic substitution preserves the lower bound on Taylor order. -/
theorem HasAnalyticOrderAtLeast.comp {g : F → G} {f : E → F} {x : E} {m : ℕ}
    (hg : HasAnalyticOrderAtLeast (𝕜 := 𝕜) g (f x) m)
    (hf : AnalyticAt 𝕜 f x) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (g ∘ f) x m := by
  obtain ⟨q, hq, hzero⟩ := hg
  obtain ⟨p, hp⟩ := hf
  exact ⟨q.comp p, hq.comp hp, comp_coeff_eq_zero_below q p m hzero⟩

/-- Taylor vanishing depends only on the actual local function germ. -/
theorem HasAnalyticOrderAtLeast.congr {f g : E → F} {x : E} {m : ℕ}
    (hf : HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m)
    (hfg : f =ᶠ[𝓝 x] g) : HasAnalyticOrderAtLeast (𝕜 := 𝕜) g x m := by
  obtain ⟨p, hp, hzero⟩ := hf
  exact ⟨p, hp.congr hfg, hzero⟩

/-- A genuine local analytic coordinate change preserves and reflects Taylor
order, provided its actual inverse is analytic at the marked image. -/
theorem analytic_order_comp_local_chart_iff
    (e : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ e.source)
    (he : AnalyticAt 𝕜 e x) (hei : AnalyticAt 𝕜 e.symm (e x))
    (f : F → G) (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (f ∘ e) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := 𝕜) f (e x) m := by
  constructor
  · intro h
    have hcenter : HasAnalyticOrderAtLeast (𝕜 := 𝕜) (f ∘ e) (e.symm (e x)) m := by
      simpa only [e.left_inv hx] using h
    have hc := hcenter.comp hei
    apply hc.congr
    exact (e.eventually_right_inverse' hx).mono fun y hy => by
      change f (e (e.symm y)) = f y
      rw [hy]
  · intro h
    exact h.comp he

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology

/-- The actual nonlinear defining equation has divided normal displacement
converging to its actual derivative applied to the chosen affine velocity. -/
theorem normal_equation_affine_velocity_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : E → ℂ) (L : E →L[ℂ] ℂ) (p V : E)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    Filter.Tendsto (fun s : ℂ => s⁻¹ * G (p + s • V)) (𝓝[≠] 0) (𝓝 (L V)) := by
  have hm : HasDerivAt (fun s : ℂ => p + s • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const V).const_add p
  have hd : HasDerivAt (fun s : ℂ => G (p + s • V)) (L V) 0 := by
    have hh : HasFDerivAt G L (p + (0 : ℂ) • V) := by simpa using hG
    exact hh.comp_hasDerivAt 0 hm
  simpa only [zero_add, zero_smul, add_zero, hp, sub_zero, smul_eq_mul] using
    hd.tendsto_slope_zero

end Nagata.Workers.W28

end
end

section

namespace Nagata.VariableUnitOrder
open scoped Topology
open Nagata.Workers.W28

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every coefficient of a bilinear expansion at (a,0) vanishes on vectors
whose second component is zero. -/
theorem bilinear_series_zero_second (b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a : ℂ)
    (n : ℕ) (v : Fin n → ℂ × ℂ) (hv : ∀ i, (v i).2 = 0) :
    b.fpowerSeriesBilinear (a, 0) n v = 0 := by
  rcases n with _ | _ | _ | n
  · simp [ContinuousLinearMap.fpowerSeriesBilinear]
  · simp [ContinuousLinearMap.fpowerSeriesBilinear, ContinuousLinearMap.coe_deriv₂, hv]
  · simp [ContinuousLinearMap.fpowerSeriesBilinear, hv]
  · rfl

/-- Product composition coefficients below m vanish when the second series
has no coefficients below m; this is a formal multilinear-series calculation. -/
theorem product_series_coeff_zero (b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a : ℂ)
    (p q : FormalMultilinearSeries ℂ E ℂ) (m : ℕ)
    (hq : ∀ n < m, q n = 0) :
    ∀ n < m, ((b.fpowerSeriesBilinear (a, 0)).comp (p.prod q)) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply, zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  apply bilinear_series_zero_second
  intro i
  change q (c.blocksFun i) (v ∘ c.embedding i) = 0
  rw [hq _ (lt_of_le_of_lt (c.blocksFun_le i) hn)]
  rfl

/-- Multiplying by any actual analytic function preserves the lower Taylor-order bound. -/
theorem analytic_order_mul_left {u f : E → ℂ} {x : E} {m : ℕ}
    (hu : AnalyticAt ℂ u x)
    (hf : HasAnalyticOrderAtLeast (𝕜 := ℂ) f x m) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun y => u y * f y) x m := by
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq, hqzero⟩ := hf
  by_cases hm : m = 0
  · subst m
    obtain ⟨r, hr⟩ := hp.analyticAt.mul hq.analyticAt
    exact ⟨r, hr, by intro n hn; omega⟩
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hfx : f x = 0 := by
      rw [← hq.coeff_zero (fun i => Fin.elim0 i), hqzero 0 hmpos]
      rfl
    let b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
    have hb := b.hasFPowerSeriesAt_bilinear (u x, f x)
    have hc := hb.comp (f := fun y : E => (u y, f y)) (hp.prod hq)
    rw [hfx] at hc
    exact ⟨(b.fpowerSeriesBilinear (u x, 0)).comp (p.prod q), hc,
      product_series_coeff_zero b (u x) p q m hqzero⟩

/-- The source's variable holomorphic-unit multiplication preserves and reflects
ordinary analytic Taylor order. This includes the factor Pi(z)^(-m). -/
theorem analytic_order_unit_mul_iff {u f : E → ℂ} {x : E} (m : ℕ)
    (hu : AnalyticAt ℂ u x) (hu0 : u x ≠ 0) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (fun y => u y * f y) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := ℂ) f x m := by
  constructor
  · intro h
    have hi := analytic_order_mul_left (hu.inv hu0) h
    apply hi.congr
    filter_upwards [hu.continuousAt.eventually_ne hu0] with y hy
    simp [hy]
  · exact analytic_order_mul_left hu

end Nagata.VariableUnitOrder

end

section

noncomputable section
namespace Nagata.Workers.W28

/-- The actual rescaling of the normal coordinate. -/
def analyticNormalScale (s : ℂ) (x : ℂ × ℂ) : ℂ × ℂ := (x.1, s * x.2)

theorem analyticNormalScale_analyticAt (s : ℂ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (analyticNormalScale s) x := by
  have hh := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x).const_smul (c := s)
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x).prod (by
    simpa only [Pi.smul_def, smul_eq_mul, ContinuousLinearMap.coe_snd'] using hh)

theorem analyticNormalScale_inv (s : ℂ) (hs : s ≠ 0) (x : ℂ × ℂ) :
    analyticNormalScale s⁻¹ (analyticNormalScale s x) = x := by
  ext <;> simp [analyticNormalScale, hs]

/-- For a nonzero specialization parameter, normal rescaling preserves and
reflects the actual local convergent Taylor order. -/
theorem analytic_order_normal_scale_iff
    (f : ℂ × ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) (x : ℂ × ℂ) (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (f ∘ analyticNormalScale s) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := ℂ) f (analyticNormalScale s x) m := by
  constructor
  · intro h
    have hc : HasAnalyticOrderAtLeast (𝕜 := ℂ) (f ∘ analyticNormalScale s)
        (analyticNormalScale s⁻¹ (analyticNormalScale s x)) m := by
      rwa [analyticNormalScale_inv s hs]
    have hh := hc.comp (analyticNormalScale_analyticAt s⁻¹ (analyticNormalScale s x))
    apply hh.congr
    exact Filter.Eventually.of_forall fun y => by
      change f (analyticNormalScale s (analyticNormalScale s⁻¹ y)) = f y
      have hi := analyticNormalScale_inv s⁻¹ (inv_ne_zero hs) y
      simpa only [inv_inv] using congrArg f hi
  · intro h
    exact h.comp (analyticNormalScale_analyticAt s x)

end Nagata.Workers.W28

end
end

end OAI
