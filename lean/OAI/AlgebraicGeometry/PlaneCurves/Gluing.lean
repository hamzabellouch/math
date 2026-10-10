import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticScaling
import OAI.AlgebraicGeometry.PlaneCurves.CoefficientSpaces
import OAI.AlgebraicGeometry.PlaneCurves.MultiplierBundles

namespace OAI

/-!
# Holomorphic local division and gluing on multiplier quotient bundles
-/

section

/-!
Local analytic division used in §02, Proposition `necessary-W`. This concerns
actual complex analytic functions and their ordinary analytic vanishing order.
It does not assume existence of a global quotient section.
-/
namespace Nagata.LocalDivision
open Filter Topology

/-- Dividing by a power of a function with a simple zero produces an analytic
germ precisely when the numerator has sufficient vanishing. This constructs
the germ, rather than assuming a global quotient exists. -/
theorem exists_analytic_quotient_at_simple_zero {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ = 0) (hP' : deriv P z₀ ≠ 0) (k : ℕ)
    (horder : (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  have hPo : analyticOrderAt P z₀ = (1 : ℕ) :=
    hP.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hP0 hP'
  obtain ⟨u, hu, hu0, hPu⟩ := hP.analyticOrderAt_eq_natCast.mp hPo
  obtain ⟨v, hv, hfv⟩ := (natCast_le_analyticOrderAt hf).mp horder
  refine ⟨fun z => v z / u z ^ k, hv.div (hu.pow k) (pow_ne_zero k hu0), ?_⟩
  have hune : ∀ᶠ z in 𝓝 z₀, u z ≠ 0 := hu.continuousAt.eventually_ne hu0
  filter_upwards [hPu, hfv, hune] with z hPu hfv hu
  simp only [pow_one, smul_eq_mul] at hPu hfv
  rw [hPu, hfv, mul_pow]
  field_simp

/-- Away from the zero divisor, the usual pointwise quotient is analytic. -/
theorem analytic_quotient_at_nonzero {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun z => f z / P z ^ k) z₀ :=
  hf.div (hP.pow k) (pow_ne_zero k hP0)

/-- One uniform local-division statement handles both marked points and their
complement. The derivative condition is needed only at a zero of P. -/
theorem exists_analytic_quotient {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀) (k : ℕ)
    (hzero : P z₀ = 0 → deriv P z₀ ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  by_cases hP0 : P z₀ = 0
  · exact exists_analytic_quotient_at_simple_zero hf hP hP0 (hzero hP0).1 k
      (hzero hP0).2
  · refine ⟨fun z => f z / P z ^ k, analytic_quotient_at_nonzero hf hP hP0 k, ?_⟩
    have hPne : ∀ᶠ z in 𝓝 z₀, P z ≠ 0 := hP.continuousAt.eventually_ne hP0
    filter_upwards [hPne] with z hz
    field_simp

end Nagata.LocalDivision

end

section

/-! Global gluing of actual analytic quotient germs, used for the low-index
coefficient blocks of `necessary-W`. No global quotient is assumed. -/
namespace Nagata.LocalDivision
open Filter Topology

/-- Local quotient germs are unique wherever the denominator is not the zero germ. -/
theorem analytic_quotient_germ_unique {f P g h : ℂ → ℂ} {z₀ : ℂ} (k : ℕ)
    (hP : AnalyticAt ℂ P z₀) (hPfin : analyticOrderAt P z₀ ≠ ⊤)
    (hg : AnalyticAt ℂ g z₀) (hh : AnalyticAt ℂ h z₀)
    (hfg : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z)
    (hfh : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * h z) :
    g =ᶠ[𝓝 z₀] h := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have heq : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, hfg.filter_mono nhdsWithin_le_nhds,
      hfh.filter_mono nhdsWithin_le_nhds] with z hz hfg hfh
    exact mul_left_cancel₀ (pow_ne_zero k hz) (hfg.symm.trans hfh)
  exact (hg.frequently_eq_iff_eventually_eq hh).mp heq.frequently

/-- A continuous identity known off a nonzero analytic divisor extends across
its zero set. This is used to recover multiplier transition identities after gluing. -/
theorem continuous_eq_at_of_eq_off_divisor {P g h : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hP : AnalyticAt ℂ P z₀)
    (hPfin : analyticOrderAt P z₀ ≠ ⊤) (hg : ContinuousAt g z₀)
    (hh : ContinuousAt h z₀)
    (heq : ∀ z ∈ U, P z ≠ 0 → g z = h z) : g z₀ = h z₀ := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have hlocal : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).filter_mono nhdsWithin_le_nhds]
      with z hz hzu
    exact heq z hzu hz
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (hh.tendsto.mono_left nhdsWithin_le_nhds) hlocal

/-- Multiplication by P^k is injective on continuous functions on U when P
has no zero germ. This is the noncancellation needed for the positive-index blocks. -/
theorem multiply_power_injective_on {P f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hf : ∀ z ∈ U, ContinuousAt f z) (hg : ∀ z ∈ U, ContinuousAt g z)
    (hmul : ∀ z ∈ U, P z ^ k * f z = P z ^ k * g z) :
    Set.EqOn f g U := by
  intro z hz
  apply continuous_eq_at_of_eq_off_divisor hU hz (hP z hz) (hPfin z hz)
    (hf z hz) (hg z hz)
  intro w hw hPw
  exact mul_left_cancel₀ (pow_ne_zero k hPw) (hmul w hw)

/-- Consequently an actual nonzero coefficient does not vanish identically when
multiplied by a marked-product power. -/
theorem multiply_power_nonzero {P f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hf : ∀ z ∈ U, ContinuousAt f z) (hne : ∃ z ∈ U, f z ≠ 0) :
    ∃ z ∈ U, P z ^ k * f z ≠ 0 := by
  classical
  by_contra h
  have hmul : ∀ z ∈ U, P z ^ k * f z = P z ^ k * (0 : ℂ) := by
    intro z hz
    rw [mul_zero]
    by_contra hn
    exact h ⟨z, hz, hn⟩
  have heq := multiply_power_injective_on hU k hP hPfin hf
    (fun z hz => continuousAt_const) hmul
  obtain ⟨z, hz, hn⟩ := hne
  exact hn (heq hz)

/-- Compatible local quotient germs glue to a genuine global analytic function
on any open domain. Uniqueness was proved above by ordinary analytic cancellation. -/
theorem glue_analytic_quotients {f P : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hlocal : ∀ z ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, f w = P w ^ k * g w) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  classical
  choose g hg hfg using hlocal
  let G : ℂ → ℂ := fun z => if hz : z ∈ U then g z hz z else 0
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz
    have heq : G =ᶠ[𝓝 z] g z hz := by
      filter_upwards [hU.mem_nhds hz, (hg z hz).eventually_analyticAt,
        (hfg z hz).eventually_nhds] with w hw hgw hfw
      have huniq := analytic_quotient_germ_unique k (hP w hw) (hPfin w hw)
        hgw (hg w hw) hfw (hfg w hw)
      simp only [G, dite_eq_left hw]
      exact huniq.self_of_nhds.symm
    exact (hg z hz).congr heq.symm
  · intro z hz
    simpa only [G, dite_eq_left hz] using (hfg z hz).self_of_nhds
  · intro z hz
    simp only [G, dite_eq_right hz]

/-- Global extension across the simple-zero divisor of P. The only vanishing
hypothesis is the actual numerator order at the zeros, not a pre-existing quotient. -/
theorem exists_global_analytic_quotient {f P : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hP : AnalyticOnNhd ℂ P U)
    (k : ℕ) (hzero : ∀ z ∈ U, P z = 0 → deriv P z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  apply glue_analytic_quotients hU k hP
  · intro z hz
    by_cases hPz : P z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  · intro z hz
    exact exists_analytic_quotient (hf z hz) (hP z hz) k (hzero z hz)

/-- A nonzero original coefficient stays nonzero after the constructed division. -/
theorem quotient_nonzero_of_nonzero {f P G : ℂ → ℂ} {U : Set ℂ} (k : ℕ)
    (hfactor : ∀ z ∈ U, f z = P z ^ k * G z)
    (hf : ∃ z ∈ U, f z ≠ 0) : ∃ z ∈ U, G z ≠ 0 := by
  obtain ⟨z, hz, hfz⟩ := hf
  refine ⟨z, hz, ?_⟩
  intro hG
  apply hfz
  rw [hfactor z hz, hG, mul_zero]

end Nagata.LocalDivision

end

section

namespace Nagata.CoefficientSpaces
open Nagata.W21

/-- Literal multiplication by a section on the genuine line-bundle cover. -/
def sectionCoverMap {τ δ : ℂˣ} {s : ℤ}
    (P : Nagata.W08.automorphicSections (τ : ℂ) s (δ : ℂ))
    (p : MultiplicativeLineCover ℂ) : MultiplicativeLineCover ℂ :=
  (p.1, P.val p.1 * p.2)

/-- Tensor multiplication commutes with the actual period generator. -/
theorem sectionCoverMap_step (τ γ δ : ℂˣ) (n s : ℤ)
    (P : Nagata.W08.automorphicSections (τ : ℂ) s (δ : ℂ))
    (p : MultiplicativeLineCover ℂ) :
    sectionCoverMap P (multiplierStep τ γ n p) =
      multiplierStep τ (γ * δ) (n + s) (sectionCoverMap P p) := by
  rcases p with ⟨z, t⟩
  apply Prod.ext
  · rfl
  · change P.val (↑(τ * z)) * ((↑(γ * z ^ (-n)) : ℂ) * t) =
      (↑((γ * δ) * z ^ (-(n + s))) : ℂ) * (P.val z * t)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [P.property.2.2 _ z.ne_zero, neg_add, zpow_add₀ z.ne_zero]
    ring

/-- Equivariance holds for every integer period, including inverse transitions. -/
theorem sectionCoverMap_iterate (τ γ δ : ℂˣ) (n s k : ℤ)
    (P : Nagata.W08.automorphicSections (τ : ℂ) s (δ : ℂ))
    (p : MultiplicativeLineCover ℂ) :
    sectionCoverMap P (multiplierIterate τ γ n k p) =
      multiplierIterate τ (γ * δ) (n + s) k (sectionCoverMap P p) := by
  have hs := sectionCoverMap_step τ γ δ n s P
  have hi (q : MultiplicativeLineCover ℂ) :
      sectionCoverMap P ((multiplierStep τ γ n).symm q) =
        (multiplierStep τ (γ * δ) (n + s)).symm (sectionCoverMap P q) := by
    apply (multiplierStep τ (γ * δ) (n + s)).injective
    rw [Equiv.apply_symm_apply, ← hs, Equiv.apply_symm_apply]
  induction k using Int.induction_on generalizing p with
  | zero => simp
  | succ k ih =>
      rw [show (k : ℤ) + 1 = 1 + k by omega, multiplierIterate_add,
        multiplierIterate_add]
      simpa only [multiplierIterate, zpow_one] using
        (hs (multiplierIterate τ γ n k p)).trans (congrArg (multiplierStep τ (γ * δ) (n + s)) (ih p))
  | pred k ih =>
      rw [show -(k : ℤ) - 1 = -1 + -k by omega, multiplierIterate_add,
        multiplierIterate_add]
      simpa only [multiplierIterate, zpow_neg_one, Equiv.Perm.inv_def] using
        (hi (multiplierIterate τ γ n (-k) p)).trans
          (congrArg (multiplierStep τ (γ * δ) (n + s)).symm (ih p))

/-- The actual globally defined map between the two multiplier quotients. -/
def sectionQuotientMap (τ γ δ : ℂˣ) (n s : ℤ)
    (P : Nagata.W08.automorphicSections (τ : ℂ) s (δ : ℂ)) :
    MultiplierQuotient τ γ n → MultiplierQuotient τ (γ * δ) (n + s) :=
  Quotient.map (sectionCoverMap P) (by
    intro p q hpq
    obtain ⟨k, hk⟩ := hpq
    refine ⟨k, ?_⟩
    rw [← sectionCoverMap_iterate, hk])

/-- Evaluation on any genuine lifted fibre is multiplication by the section value. -/
theorem sectionQuotientMap_mk (τ γ δ : ℂˣ) (n s : ℤ)
    (P : Nagata.W08.automorphicSections (τ : ℂ) s (δ : ℂ))
    (z : ℂˣ) (t : ℂ) :
    sectionQuotientMap τ γ δ n s P (Quotient.mk _ (z, t)) =
      Quotient.mk _ (z, P.val z * t) := rfl

end Nagata.CoefficientSpaces

end

section

namespace Nagata.FiberCoordinateChange
open Nagata.Workers.W28

/-- Actual fibre substitution w=P(z)*v over an open base where P is nonzero. -/
noncomputable def fibreChart (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) where
  toFun x := (x.1, P x.1 * x.2)
  invFun x := (x.1, x.2 / P x.1)
  source := {x | x.1 ∈ U}
  target := {x | x.1 ∈ U}
  map_source' := by intro x hx; exact hx
  map_target' := by intro x hx; exact hx
  left_inv' := by
    intro x hx
    ext
    · rfl
    · field_simp [hne x.1 hx]
  right_inv' := by
    intro x hx
    ext
    · rfl
    · field_simp [hne x.1 hx]
  open_source := hU.preimage continuous_fst
  open_target := hU.preimage continuous_fst
  continuousOn_toFun := by
    intro x hx
    exact (continuousAt_fst.prodMk
      (((hP x.1 hx).continuousAt.comp continuousAt_fst).mul continuousAt_snd)).continuousWithinAt
  continuousOn_invFun := by
    intro x hx
    exact (continuousAt_fst.prodMk
      (continuousAt_snd.div ((hP x.1 hx).continuousAt.comp continuousAt_fst)
        (hne x.1 hx))).continuousWithinAt

/-- Analyticity of the actual forward fibre coordinate map. -/
theorem fibreChart_analyticAt (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    AnalyticAt ℂ (fibreChart P U hU hP hne) x := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x
  have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x
  exact hf.prod (((hP x.1 hx).comp hf).mul hs)

/-- Analyticity of the actual inverse fibre coordinate map. -/
theorem fibreChart_symm_analyticAt (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    AnalyticAt ℂ (fibreChart P U hU hP hne).symm x := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x
  have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x
  exact hf.prod (hs.div ((hP x.1 hx).comp hf) (hne x.1 hx))

/-- Exactly the multiplicity-preserving transformation in `necessary-W`:
substitute w=P*v and divide the value frame by P^m. -/
theorem order_preserved_by_fibre_substitution
    (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (F : (ℂ × ℂ) → ℂ) (x : ℂ × ℂ) (hx : x.1 ∈ U) (m : ℕ) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹ * F (y.1, P y.1 * y.2)) x m ↔
    HasAnalyticOrderAtLeast (𝕜 := ℂ) F (x.1, P x.1 * x.2) m := by
  have hbase := (hP x.1 hx).comp ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x)
  have hunit := (hbase.pow m).inv (pow_ne_zero m (hne x.1 hx))
  have hunitne : (P x.1 ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero m (hne x.1 hx))
  have hunit' : AnalyticAt ℂ (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹) x := hunit
  apply (Nagata.VariableUnitOrder.analytic_order_unit_mul_iff
    (f := fun y : ℂ × ℂ => F (y.1, P y.1 * y.2)) m hunit' hunitne).trans
  exact analytic_order_comp_local_chart_iff (fibreChart P U hU hP hne) x hx
    (fibreChart_analyticAt P U hU hP hne x hx)
    (fibreChart_symm_analyticAt P U hU hP hne (x.1, P x.1 * x.2) hx) F m

end Nagata.FiberCoordinateChange

end

section

/-! Transition identities for the analytically glued coefficient quotient.
The maps are actual functions; the hypotheses are the original numerator and
denominator transitions, not the desired quotient transition. -/
namespace Nagata.LocalDivision

/-- Cancellation derives the quotient transition wherever the denominator is nonzero. -/
theorem quotient_transition_off_zero {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    (k : ℕ) (z : ℂ) (hP : P z ≠ 0) (hB : B z ≠ 0)
    (hfz : f z = P z ^ k * G z) (hfT : f (T z) = P (T z) ^ k * G (T z))
    (htf : f (T z) = A z * f z) (htP : P (T z) = B z * P z) :
    G (T z) = (A z / B z ^ k) * G z := by
  have heq : P (T z) ^ k * G (T z) = A z * (P z ^ k * G z) := by
    rw [← hfT, htf, hfz]
  rw [htP, mul_pow] at heq
  have hcancel : B z ^ k * G (T z) = A z * G z := by
    apply mul_left_cancel₀ (pow_ne_zero k hP)
    calc
      P z ^ k * (B z ^ k * G (T z)) = (B z ^ k * P z ^ k) * G (T z) := by ring
      _ = A z * (P z ^ k * G z) := heq
      _ = P z ^ k * (A z * G z) := by ring
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero k hB)).mpr
  rw [mul_comm]
  exact hcancel

/-- The actual quotient transition extends over all zeros by continuity and
isolated zeros. This closes the local-to-global transition step. -/
theorem quotient_transition_global {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P U) (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hTU : Set.MapsTo T U U) (hB : ∀ z ∈ U, B z ≠ 0)
    (hfactor : ∀ z ∈ U, f z = P z ^ k * G z)
    (htf : ∀ z ∈ U, f (T z) = A z * f z)
    (htP : ∀ z ∈ U, P (T z) = B z * P z)
    (hleft : ∀ z ∈ U, ContinuousAt (fun w => G (T w)) z)
    (hright : ∀ z ∈ U, ContinuousAt (fun w => (A w / B w ^ k) * G w) z) :
    ∀ z ∈ U, G (T z) = (A z / B z ^ k) * G z := by
  intro z hz
  apply continuous_eq_at_of_eq_off_divisor hU hz (hP z hz) (hPfin z hz)
    (hleft z hz) (hright z hz)
  intro w hw hPw
  exact quotient_transition_off_zero k w hPw (hB w hw) (hfactor w hw)
    (hfactor (T w) (hTU hw)) (htf w hw) (htP w hw)

end Nagata.LocalDivision

end

section

namespace Nagata.CoefficientSpaces

/-- The literal multiplication map restricted to actual automorphic sections. -/
noncomputable def multiplySection (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ) :
    Nagata.W08.automorphicSections τ n γ →ₗ[ℂ] (ℂ → ℂ) :=
  (multiplyPower P k).comp (Nagata.W08.automorphicSections τ n γ).subtype

/-- No nonzero source section is lost in the positive-index coefficient image.
The omitted point contributes no fake section because both representatives are
normalized to zero there. -/
theorem multiplySection_injective (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    Function.Injective (multiplySection τ γ n P k) := by
  intro f g heq
  have hoff : Set.EqOn f.val g.val {z | z ≠ 0} := by
    apply Nagata.LocalDivision.multiply_power_injective_on
      isOpen_ne k hP hPfin
      (fun z hz => (f.property.2.1 z hz).continuousAt)
      (fun z hz => (g.property.2.1 z hz).continuousAt)
    intro z hz
    exact congrFun heq z
  apply Nagata.W08.automorphicSections_ext
  exact hoff

end Nagata.CoefficientSpaces

end

section

namespace Nagata.CoefficientSpaces

/-- The exact degree and multiplier of a quotient coefficient. -/
theorem quotient_multiplier_identity {γ δ z : ℂ} (hδ : δ ≠ 0) (hz : z ≠ 0)
    (n s : ℤ) (k : ℕ) :
    (γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k =
      (γ / δ ^ k) * z ^ (-(n - (k : ℤ) * s)) := by
  have he : -(n - (k : ℤ) * s) = -n - (-s) * (k : ℤ) := by ring
  rw [he, zpow_sub₀ hz, zpow_mul, zpow_natCast, mul_pow]
  field_simp

theorem exists_automorphic_quotient {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.automorphicSections τ n γ)
    (P : Nagata.W08.automorphicSections τ s δ)
    (hf : AnalyticOnNhd ℂ f.val {z | z ≠ 0})
    (hP : AnalyticOnNhd ℂ P.val {z | z ≠ 0}) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.automorphicSections τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z := by
  obtain ⟨G, hG, hfactor, hGoutside⟩ :=
    Nagata.LocalDivision.exists_global_analytic_quotient isOpen_ne hf hP k hzero
  have hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤ := by
    intro z hz
    by_cases hPz : P.val z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  have heq : ∀ z ≠ 0, G (τ * z) =
      ((γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k) * G z := by
    apply Nagata.LocalDivision.quotient_transition_global isOpen_ne k hP hPfin
      (fun z hz => mul_ne_zero hτ hz)
      (fun z hz => mul_ne_zero hδ (zpow_ne_zero _ hz)) hfactor
      (fun z hz => f.property.2.2 z hz) (fun z hz => P.property.2.2 z hz)
    · intro z hz
      exact (hG (τ * z) (mul_ne_zero hτ hz)).continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    · intro z hz
      have hA : ContinuousAt (fun w : ℂ => γ * w ^ (-n)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-n) (Or.inl hz))
      have hB : ContinuousAt (fun w : ℂ => δ * w ^ (-s)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-s) (Or.inl hz))
      exact (hA.div (hB.pow k) (pow_ne_zero k
        (mul_ne_zero hδ (zpow_ne_zero _ hz)))).mul (hG z hz).continuousAt

  refine ⟨⟨G, ?_⟩, hfactor⟩
  refine ⟨hGoutside 0 (by simp), ?_, ?_⟩
  · intro z hz
    exact (hG z hz).differentiableAt
  · intro z hz
    rw [heq z hz, quotient_multiplier_identity hδ hz]

end Nagata.CoefficientSpaces

end

end OAI
