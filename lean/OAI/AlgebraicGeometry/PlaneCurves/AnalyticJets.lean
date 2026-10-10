import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Topology.Separation.Hausdorff
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticScaling

namespace OAI

/-!
# Analytic scalar families, moving jets, and cofinite jet limits
-/

section

/-!
# Cofinite parameter specialization of actual derivative jets
-/

namespace Nagata.Workers.W17

open Filter
open scoped Topology

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace V] [T2Space V] [Zero V]

/-- A continuous quantity vanishing outside a finite parameter set vanishes
at the limiting parameter, including when the parameter lies in that set. -/
theorem continuous_value_zero_of_cofinite
    (f : 𝕜 → V) (x : 𝕜) (exceptional : Finset 𝕜)
    (hf : ContinuousAt f x) (hzero : ∀ s, s ∉ exceptional → f s = 0) :
    f x = 0 := by
  have he : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional :=
    exceptional.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite x)
  have hz : f =ᶠ[𝓝[≠] x] fun _ => 0 := he.mono fun s hs => hzero s hs
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hz

/-- Local version: only a neighborhood of the limiting parameter is needed. -/
theorem continuous_value_zero_of_eventually_cofinite
    (f : 𝕜 → V) (x : 𝕜) (exceptional : Finset 𝕜)
    (hf : ContinuousAt f x)
    (hzero : ∀ᶠ s in 𝓝 x, s ∉ exceptional → f s = 0) : f x = 0 := by
  have he : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional :=
    exceptional.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite x)
  have hlocal : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional → f s = 0 :=
    hzero.filter_mono nhdsWithin_le_nhds
  have hz : f =ᶠ[𝓝[≠] x] fun _ => 0 :=
    (he.and hlocal).mono fun s hs => hs.2 hs.1
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hz

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Genuine low-order derivative jets survive a cofinite parameter limit.
Continuity is explicitly required and is not hidden in a substitute object. -/
theorem cofinite_moving_derivative_jets
    (family : 𝕜 → E → F) (center : 𝕜 → E) (x : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hcontinuous : ∀ n < m,
      ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x)
    (hjets : ∀ s, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family x) (center x) = 0 := by
  intro n hn
  exact continuous_value_zero_of_cofinite
    (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x exceptional
    (hcontinuous n hn) (fun s hs => hjets s hs n hn)

/-- The source application: the holomorphic family and its jet identities
need only hold near the limiting parameter outside finitely many values. -/
theorem local_cofinite_moving_derivative_jets
    (family : 𝕜 → E → F) (center : 𝕜 → E) (x : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hcontinuous : ∀ n < m,
      ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x)
    (hjets : ∀ᶠ s in 𝓝 x, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family x) (center x) = 0 := by
  intro n hn
  exact continuous_value_zero_of_eventually_cofinite
    (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x exceptional
    (hcontinuous n hn) (hjets.mono fun s hs hE => hs hE n hn)

end Nagata.Workers.W17

end

section

/-! Vanishing derivatives imply genuine Taylor order in characteristic zero.
Multilinear expansions need not be symmetric; only their diagonals are forced
zero. Erasing those low diagonal-zero maps produces the required expansion. -/

noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The diagonal of a Taylor coefficient vanishes when its derivative does. -/
theorem powerSeries_diagonal_zero_of_iteratedFDeriv_zero
    {f : E → F} {x : E} {p : FormalMultilinearSeries 𝕜 E F} {n : ℕ}
    (hp : HasFPowerSeriesAt f p x) (hn : iteratedFDeriv 𝕜 n f x = 0) (v : E) :
    p n (fun _ => v) = 0 := by
  obtain ⟨r, hr⟩ := hp
  have he := hr.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => v)
  have hz : n.factorial • p n (fun _ => v) = 0 := by
    simpa only [hn, zero_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using he.symm
  have hz' : (n.factorial : 𝕜) • p n (fun _ => v) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hz
  exact (smul_eq_zero.mp hz').resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- Actual analytic derivatives detect the existential convergent Taylor order. -/
theorem analytic_order_of_iteratedFDeriv_zero
    {f : E → F} {x : E} (hf : AnalyticAt 𝕜 f x) (m : ℕ)
    (hz : ∀ n < m, iteratedFDeriv 𝕜 n f x = 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m := by
  obtain ⟨p, r, hp⟩ := hf
  let q : FormalMultilinearSeries 𝕜 E F := fun n => if n < m then 0 else p n
  have hnorm : ∀ n, ‖q n‖ ≤ ‖p n‖ := by
    intro n
    by_cases hn : n < m
    · simp [q, hn]
    · simp [q, hn]
  have hdiag : ∀ n v, q n (fun _ => v) = p n (fun _ => v) := by
    intro n v
    by_cases hn : n < m
    · simp [q, hn, powerSeries_diagonal_zero_of_iteratedFDeriv_zero
        hp.hasFPowerSeriesAt (hz n hn) v]
    · simp [q, hn]
  refine ⟨q, ⟨r, ?_⟩, ?_⟩
  · refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le hnorm), hp.r_pos, ?_⟩
    intro y hy
    simpa only [hdiag] using hp.hasSum hy
  · intro n hn
    simp [q, hn]

end Nagata.Workers.W17

end
end

section

/-!
# Removing a nonzero scalar from analytic order conditions

This is the analytic order step used after dividing the substituted family
by s^u for a fixed nonzero parameter s. It uses actual convergent multilinear
power-series expansions and does not assume a multiplicity invariance field.
-/

namespace Nagata.Workers.W17

open Nagata.Workers.W28

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Multiplication by a constant preserves lower Taylor order. -/
theorem analytic_order_const_smul {f : E → F} {x : E} {m : Nat}
    (hf : HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m) (c : 𝕜) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (c • f) x m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]

/-- A nonzero scalar preserves and reflects analytic Taylor order. -/
theorem analytic_order_const_smul_iff (f : E → F) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (c • f) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m := by
  constructor
  · intro h
    have hi := analytic_order_const_smul h c⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  · intro h
    exact analytic_order_const_smul h c

/-- Scalar multiplication of a scalar-valued section in a local frame. -/
theorem analytic_order_const_mul_iff (f : E → 𝕜) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HasAnalyticOrderAtLeast (𝕜 := 𝕜) (fun y => c * f y) x m ↔
      HasAnalyticOrderAtLeast (𝕜 := 𝕜) f x m :=
  analytic_order_const_smul_iff f x m c hc

end Nagata.Workers.W17

end

section

/-!
# Continuity of derivative jets in a joint analytic family

The derivatives here are taken in the fiber variable only. Parameterized
Fréchet differentiation proves that they depend smoothly on both variables,
so a continuous moving center gives precisely the continuity needed for the
cofinite central-limit theorem. No derivative-continuity field is assumed.
-/

namespace Nagata.Workers.W17

open scoped ContDiff

variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Fiber-variable iterated derivatives of a jointly smooth family are
jointly smooth, proved by parameterized differentiation. -/
theorem contDiffAt_parameter_iteratedFDeriv
    (family : P → E → F) (p : P × E)
    (hf : ContDiffAt 𝕜 ∞ (Function.uncurry family) p) (n : Nat) :
    ContDiffAt 𝕜 ∞ (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) p := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.coe_coe'', Function.uncurry_def] using
      hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 𝕜 E F).symm :
          F →L[𝕜] E [×0]→L[𝕜] F)
  | succ n ih =>
    have hprojection : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => (q.1.1, q.2)) (p, p.2) :=
      contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hjoint : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => iteratedFDeriv 𝕜 n (family q.1.1) q.2) (p, p.2) :=
      by
        have ih' : ContDiffAt 𝕜 ∞
            (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (p.1, p.2) := by
          simpa only [Prod.eta] using ih
        simpa only [Function.comp_def] using ih'.comp (p, p.2) hprojection
    have hd : ContDiffAt 𝕜 ∞
        (fun q : P × E => fderiv 𝕜 (iteratedFDeriv 𝕜 n (family q.1)) q.2) p :=
      hjoint.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm.contDiff.contDiffAt.comp
        p hd

/-- Joint analyticity supplies continuity of all ordinary fiber jets along
any continuous moving center. -/
theorem analytic_moving_derivative_continuousAt [CompleteSpace F]
    (family : P → E → F) (center : P → E) (s₀ : P)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀) (n : Nat) :
    ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) s₀ := by
  have hpartial : ContinuousAt
      (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (s₀, center s₀) :=
    (contDiffAt_parameter_iteratedFDeriv family (s₀, center s₀) hf.contDiffAt n).continuousAt
  have hcurve : ContinuousAt (fun s : P => (s, center s)) s₀ :=
    continuousAt_id.prodMk hc
  simpa only [Function.comp_def] using hpartial.comp (f := fun s : P => (s, center s)) hcurve

/-- Thus actual cofinite jet vanishing specializes in a jointly analytic
family without any separately assumed derivative-continuity hypothesis. -/
theorem analytic_local_cofinite_moving_derivative_jets [CompleteSpace F]
    (family : 𝕜 → E → F) (center : 𝕜 → E) (s₀ : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀)
    (hjets : ∀ᶠ s in nhds s₀, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family s₀) (center s₀) = 0 := by
  exact local_cofinite_moving_derivative_jets family center s₀ exceptional m
    (fun n _ => analytic_moving_derivative_continuousAt family center s₀ hf hc n) hjets

end Nagata.Workers.W17

end

end OAI
