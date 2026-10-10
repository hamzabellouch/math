import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.ScaledJointLowCounts

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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter

def groundPositionLaw (N : ℕ) (L : Length) (u : Jet N L) : Measure (Configuration N L) :=
  volume.withDensity (fun X ↦ ENNReal.ofReal (‖u.1 X‖^2))

namespace CellOrbital

lemma count_continuous {n : ℕ} (L : Length) (δ : ℝ) (c : Torus L) :
    Continuous (count (n:=n) L δ c) := by
  apply continuous_finsetSum
  intro i _
  exact ((bump_continuous L (8*δ) c).comp (continuous_apply i)).pow 2

lemma joint_one {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ} (hh : 0<h)
    (c : S → Torus L) (A : Finset S) (X : Configuration n L)
    (hX : ∀ s∈A, count L (1/100) (c s) X ≤ h) : (joint n L c h A).toFun X=1 := by
  rw [joint_apply]
  apply Finset.prod_eq_one
  intro s hs
  rw [profile_one hh (hX s hs),Complex.ofReal_one]

lemma groundPositionLaw_le_joint {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} {h : ℝ}
    (hh : 0<h) (c : S → Torus L) (A : Finset S) (u : Jet n L)
    (T : Set (Configuration n L)) (hT : MeasurableSet T)
    (hcount : ∀ X∈T, ∀ s∈A, count L (1/100) (c s) X ≤ h) :
    groundPositionLaw n L u T ≤ ENNReal.ofReal (‖(joint n L c h A).onScalar u.1‖^2) := by
  rw [groundPositionLaw,withDensity_apply _ hT,
    ← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integrableOn
      (Eventually.of_forall fun X ↦ sq_nonneg ‖u.1 X‖),IndicatorStrong.norm_sq_integral]
  apply ENNReal.ofReal_le_ofReal
  have hi : Integrable (fun X ↦ ‖((joint n L c h A).onScalar u.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  calc
    _ = ∫ X in T, ‖((joint n L c h A).onScalar u.1) X‖^2 ∂volume := by
      apply setIntegral_congr_ae hT
      filter_upwards [(joint n L c h A).coe_onScalar u.1] with X hX hXT
      rw [hX,joint_one hh c A X (hcount X hXT),one_mul]
    _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun X ↦ sq_nonneg _)

theorem scaled_low_count_probability : ∃ α₀ ell D₀ Q : ℝ,
    0<α₀ ∧ 0<ell ∧ 0<D₀ ∧ 0<Q ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (D α : ℝ),
      2≤n → 1 ≤ L.val → D=(n:ℝ)/L.val^3 → D₀ ≤ D →
      α₀/2 ≤ α → α ≤ 2*α₀ →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (c : S → Torus L), (∀ z v, z≠v → 1 ≤ dist (c z) (c v)) →
    ∀ A : Finset S,
      groundPositionLaw n L g {X | ∀ s∈A, count L (1/100) (c s) X < ell*D} ≤
        ENNReal.ofReal ((Q/D^2)^A.card) := by
  obtain ⟨α₀,ell,D₀,Q,hα,hell,hD₀,hQ,hs⟩ := scaled_joint_low_counts
  refine ⟨α₀,ell,D₀,Q,hα,hell,hD₀,hQ,?_⟩
  intro S _ n L D α hn hL hDN hDD hαl hαu g hg c hc A
  have hh : 0<ell*D := mul_pos hell (hD₀.trans_le hDD)
  apply (groundPositionLaw_le_joint hh c A g _ ?_ (fun X hX s hs ↦ (hX s hs).le)).trans
  · exact ENNReal.ofReal_le_ofReal (hs S n L D α hn hL hDN hDD hαl hαu g hg c hc A)
  · simpa only [Set.ofPred_forall] using Finset.measurableSet_biInter A (fun s _ ↦ measurableSet_lt
      (count_continuous (n:=n) L (1/100) (c s)).measurable
      (show Measurable (fun _ : Configuration n L ↦ ell*D) from measurable_const))

end CellOrbital
end HardSphere

end

end OAI
