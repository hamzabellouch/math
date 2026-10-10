import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import OAI.NumberTheory.Ostmann.Dirichlet.Zeros
import PrimeNumberTheoremAnd.Erdos970.Auxiliary
import PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Dirichlet
open Complex Filter Set
open scoped Topology

theorem tendsto_mul_logDeriv_order {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hfinite : analyticOrderAt f p ≠ ⊤) :
    Tendsto (fun z => (z-p)*logDeriv f z) (𝓝[≠] p)
      (𝓝 ((analyticOrderAt f p).toNat : ℂ)) := by
  obtain ⟨g, hg, hg0, he⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hlog := logDeriv_congr_nhds he
  have hreg : ContinuousAt (logDeriv g) p :=
    (hg.deriv.div hg hg0).continuousAt
  have hlim : Tendsto (fun z : ℂ => ((analyticOrderAt f p).toNat : ℂ) +
      (z-p)*logDeriv g z) (𝓝[≠] p) (𝓝 ((analyticOrderAt f p).toNat : ℂ)) := by
    have hsub : Tendsto (fun z : ℂ => z-p) (𝓝[≠] p) (𝓝 (0 : ℂ)) := by
      simpa only [Pi.sub_apply, id_eq, sub_self] using! ((continuousAt_id.sub (continuousAt_const (y := p))).tendsto.mono_left
        (show 𝓝[≠] p ≤ 𝓝 p from nhdsWithin_le_nhds))
    simpa using (tendsto_const_nhds (x := ((analyticOrderAt f p).toNat : ℂ))).add
      (hsub.mul (hreg.tendsto.mono_left nhdsWithin_le_nhds))
  apply hlim.congr'
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hgz hgnz hzp
  have hzp' : z-p ≠ 0 := sub_ne_zero.mpr hzp
  rw [hz]
  change _ = (z-p)*logDeriv (fun z => (z-p)^((analyticOrderAt f p).toNat)*g z) z
  rw [logDeriv_fun_mul (f := fun w : ℂ => (w-p)^((analyticOrderAt f p).toNat))
    (g := g) z (pow_ne_zero _ hzp') hgnz (by fun_prop) hgz.differentiableAt,
    logDeriv_fun_pow (by fun_prop)]
  have hlin : logDeriv (fun z : ℂ => z-p) z = 1/(z-p) := by simp [logDeriv_apply]
  rw [hlin]
  field_simp

theorem residue_neg_logDeriv_mul {f K : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hfinite : analyticOrderAt f p ≠ ⊤)
    (hK : ContinuousAt K p) :
    Erdos970.residue (fun z => -logDeriv f z * K z) p =
      -((analyticOrderAt f p).toNat : ℂ)*K p := by
  apply residue_eq_of_tendsto
  have h := (tendsto_mul_logDeriv_order hf hfinite).neg.mul
    (hK.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  funext point
  ring

theorem residue_neg_LFunction_logDeriv_mul {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {K : ℂ → ℂ} {p : ℂ}
    (hK : ContinuousAt K p) :
    Erdos970.residue (fun z => -(deriv χ.LFunction z / χ.LFunction z)*K z) p =
      -(zeroMultiplicity χ p : ℂ)*K p :=
  residue_neg_logDeriv_mul (analyticAt_LFunction χ hχ p)
    (analyticOrderAt_LFunction_ne_top χ hχ p) hK

theorem logDeriv_has_at_most_simple_pole {f : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hfinite : analyticOrderAt f p ≠ ⊤) :
    (-1 : ℤ) ≤ meromorphicOrderAt (logDeriv f) p := by
  by_cases hzero : meromorphicOrderAt f p = 0
  · exact le_trans (by exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega))
      (meromorphicOrderAt_logDeriv_nonneg hf.meromorphicAt hzero)
  · have htop : meromorphicOrderAt f p ≠ ⊤ := by
      rw [hf.meromorphicOrderAt_eq]
      simpa using hfinite
    rw [meromorphicOrderAt_logDeriv_eq_neg_one hf.meromorphicAt hzero htop]
    rfl

theorem weighted_logDeriv_has_at_most_simple_pole {f K : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hfinite : analyticOrderAt f p ≠ ⊤)
    (hK : AnalyticAt ℂ K p) :
    (-1 : ℤ) ≤ meromorphicOrderAt (fun z => -logDeriv f z*K z) p := by
  change (-1 : ℤ) ≤ meromorphicOrderAt ((-logDeriv f)*K) p
  rw [meromorphicOrderAt_mul hf.meromorphicAt.logDeriv.neg hK.meromorphicAt,
    ← meromorphicOrderAt_neg]
  have hlog := logDeriv_has_at_most_simple_pole hf hfinite
  have hker := hK.meromorphicOrderAt_nonneg
  simpa using add_le_add hlog hker

end Ostmann.Dirichlet

end

end OAI
