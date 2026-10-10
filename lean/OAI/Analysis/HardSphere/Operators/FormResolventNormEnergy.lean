import Mathlib
import OAI.Analysis.HardSphere.Operators.KilledTransitionFormHeat
import OAI.Analysis.HardSphere.Collisions.IteratedInsertion

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open ContinuousLinearMap

lemma formResolvent_norm_le_of_energy {N : ℕ} {L : Length} {a b : ℝ}
    (hb : 0≤b) (henergy : ∀ u : Jet N L, u∈dirichletDomain N L a → b*‖u.1‖^2≤energy u) :
    ‖formResolvent N L a‖≤(1+b)⁻¹ := by
  have hp : 0<1+b := by linarith
  apply opNorm_le_bound _ (inv_nonneg.mpr hp.le)
  intro f
  let g := (scalarEmbedding N L a).adjoint f
  let u := hilbertJetEquiv N L (g : HilbertJet N L)
  have hu : u∈dirichletDomain N L a := g.property
  have he := henergy u hu
  have hn : ‖g‖^2=‖u.1‖^2+energy u := hilbertJet_norm_sq (g : HilbertJet N L)
  have hinner : ‖g‖^2=(inner ℂ f u.1).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (adjoint_inner_left (scalarEmbedding N L a) g f)
  have hbound : (1+b)*‖u.1‖^2≤‖f‖*‖u.1‖ := by
    have hi := re_inner_le_norm (𝕜 := ℂ) f u.1
    change (inner ℂ f u.1).re≤‖f‖*‖u.1‖ at hi
    nlinarith
  change ‖u.1‖≤(1+b)⁻¹*‖f‖
  by_cases hz : ‖u.1‖=0
  · rw [hz]; positivity
  · have hupos : 0<‖u.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [← div_eq_inv_mul,le_div_iff₀ hp]
    nlinarith

local instance scalarOperatorRealAlgebraCoercive (N : ℕ) (L : Length) :
    Algebra ℝ (ScalarL2 N L →L[ℂ] ScalarL2 N L) := Algebra.restrictScalars ℝ ℂ _

lemma formHeat_norm_le_of_energy {N : ℕ} {L : Length} {a b t : ℝ} (ht : 0<t)
    (henergy : ∀ u : Jet N L, u∈dirichletDomain N L a → b*‖u.1‖^2≤energy u) :
    ‖formHeat N L a t‖≤Real.exp (-t*b) := by
  cases subsingleton_or_nontrivial (ScalarL2 N L) with
  | inl h =>
    let := h
    rw [show formHeat N L a t=0 from Subsingleton.elim _ _,norm_zero]
    exact (Real.exp_pos _).le
  | inr h =>
   let := h
   by_cases hb : 0≤b
   · have hp : 0<1+b := by linarith
     have hR := formResolvent_norm_le_of_energy hb henergy
     unfold formHeat
     apply norm_cfc_le (Real.exp_pos _).le
     intro x hx
     have hx0 : 0≤x := spectrum_nonneg_of_nonneg
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr (formResolvent_isPositive N L a)) hx
     have hxb : x≤(1+b)⁻¹ := (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hR)
     rw [Real.norm_eq_abs,abs_of_nonneg (heatScalar_nonneg t x)]
     rcases eq_or_lt_of_le hx0 with rfl | hx0
     · rw [heatScalar_zero]; exact (Real.exp_pos _).le
     · rw [heatScalar_of_pos ht hx0]
       apply Real.exp_le_exp.mpr
       have hxinv : 1+b≤x⁻¹ := by
        simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hp) hx0).mpr hxb
       have hg := mul_le_mul_of_nonneg_left hxinv ht.le
       rw [div_eq_mul_inv]
       linarith
   · have hnorm : ‖formHeat N L a t‖≤1 := by
       rw [formHeat,← regularHeat_pos (formResolvent N L a) ht]
       exact regularHeat_contract (formResolvent_isPositive N L a) (formResolvent_norm_le_one N L a) t
     exact hnorm.trans (Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_not_ge hb)))
lemma killedTransition_norm_le_of_energy {N : ℕ} {L : Length} {a b t : ℝ} (ht : 0<t)
    (henergy : ∀ u : Jet N L, u∈dirichletDomain N L a → b*‖u.1‖^2≤energy u) :
    ‖killedTransition N L a t‖≤Real.exp (-t*b) := by
  rw [killedTransition_eq_formHeat N L a ht]
  exact formHeat_norm_le_of_energy ht henergy

lemma bath_heat_bound : ∃ C : ℝ, 0<C ∧
    ∀ (n m : ℕ) (L : Length) (r t : ℝ), 0<r → 0<t →
    ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (n+m) L, IsGroundVector (n+m) L r u →
      ‖killedTransition n L r t‖≤
        Real.exp (-t*(energy u-C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3)) := by
  obtain ⟨C,hC,hrem⟩ := ground_energy_removal
  exact ⟨C,hC,fun n m L r t hr ht hs u hu ↦
    killedTransition_norm_le_of_energy ht (hrem n m L r hr hs u hu)⟩
end HardSphere

end

end OAI
