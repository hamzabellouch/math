import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPositionLaw
import OAI.Analysis.HardSphere.Geometry.SpatialScalarSquare
import OAI.Analysis.HardSphere.Geometry.MollifiedCloseJoint

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
open scoped ComplexConjugate

lemma finset_erase_recursion_on {S : Type*} [DecidableEq S] (a : Finset S → ℝ)
    (P : Finset S → Prop) (hP : ∀ A s, P A → P (A.erase s)) (q : ℝ)
    (hq : 0≤q) (h0 : a ∅≤1)
    (hr : ∀ A : Finset S, P A → A.Nonempty → (A.card:ℝ)*a A≤q*∑ s∈A, a (A.erase s)) :
    ∀ A : Finset S, P A → a A≤q^A.card := by
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro hPA
    by_cases hA : A.Nonempty
    · have hc : 0<(A.card:ℝ) := by exact_mod_cast hA.card_pos
      have hs : (∑ s∈A, a (A.erase s))≤(A.card:ℝ)*q^(A.card-1) := by
        calc
          _ ≤ ∑ _s∈A, q^(A.card-1) := Finset.sum_le_sum fun s hs ↦ by
            have hh := ih (A.erase s) (Finset.erase_ssubset hs) (hP A s hPA)
            rwa [Finset.card_erase_of_mem hs] at hh
          _ = _ := by simp
      have he : q*((A.card:ℝ)*q^(A.card-1))=(A.card:ℝ)*q^A.card := by
        rw [show q^A.card=q^(A.card-1)*q by
          conv_lhs => rw [←Nat.sub_add_cancel hA.card_pos]
          rw [pow_succ]]
        ring
      have ht := (hr A hPA hA).trans ((mul_le_mul_of_nonneg_left hs hq).trans_eq he)
      exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm (A.card:ℝ)] using ht)
    · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simpa [he] using h0

variable {n : ℕ} [Nontrivial (Fin n)]

lemma mollifiedCloseJoint_empty_onScalar (L : Length) (s h : ℝ)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (u : ScalarL2 n L) :
    (mollifiedCloseJoint L s φ h ∅).onScalar u=u := by
  apply Lp.ext
  filter_upwards [(mollifiedCloseJoint L s φ h ∅).coe_onScalar u] with X hX
  simpa only [mollifiedCloseJoint_apply,Finset.prod_empty,one_mul] using hX

lemma groundPositionLaw_le_closeJoint (L : Length) {s h : ℝ} (hs : 0<s) (hs1 : s≤1) (hh : 0<h)
    (φ : ContDiffBump (0 : EuclideanConfiguration (Fin n))) (hφ : ((32/s)*φ.rOut)^2≤h/4)
    (A : Finset (Torus L)) (g : Jet n L) (T : Set (Configuration n L)) (hT : MeasurableSet T)
    (hcount : ∀ X∈T, ∀ v∈A, 8*h≤((localCloseLabels L s v X).card:ℝ)) :
    groundPositionLaw n L g T≤ENNReal.ofReal (‖(mollifiedCloseJoint L s φ h A).onScalar g.1‖^2) := by
  rw [groundPositionLaw,withDensity_apply _ hT,
    ←ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp g.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).integrableOn
      (Eventually.of_forall fun X ↦ sq_nonneg ‖g.1 X‖),IndicatorStrong.norm_sq_integral]
  apply ENNReal.ofReal_le_ofReal
  have hi : Integrable (fun X ↦ ‖((mollifiedCloseJoint L s φ h A).onScalar g.1) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  calc
    _ = ∫ X in T, ‖((mollifiedCloseJoint L s φ h A).onScalar g.1) X‖^2 ∂volume := by
      apply setIntegral_congr_ae hT
      filter_upwards [(mollifiedCloseJoint L s φ h A).coe_onScalar g.1] with X hX hXT
      rw [hX,mollifiedCloseJoint_covers L hs hs1 hh φ hφ A X (hcount X hXT),one_mul]
    _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun X ↦ sq_nonneg _)

end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma close_support_integral {n : ℕ} {L : Length} (A : Finset (Torus L))
    {s C c b D h : ℝ} (hc : 0<c) (hb : 0<b)
    (hcoef : (C+1)*D≤c/b^3*(h/4))
    (f : SmoothMultiplier n L) (g : ScalarL2 n L)
    (hsupport : ∀ X, f.toFun X≠0 → (h/4)*(A.card:ℝ)≤((localizedNearLabels L A s X).card:ℝ)) :
    D*(A.card:ℝ)*‖f.onScalar g‖^2≤
      ∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2 := by
  have hn : Integrable (fun X ↦ ‖(f.onScalar g) X‖^2) volume :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hf := weightedSiteCount_integrable L A (f.onScalar g)
  have hk := localizedNearLabels_integrable L A s (f.onScalar g)
  have hi : Integrable (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+
      c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2) volume := by
    have he : (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A s X).card:ℝ))*‖(f.onScalar g) X‖^2) =
        fun X ↦ (weightedSiteCount L A X*‖(f.onScalar g) X‖^2-
          (C*D*(A.card:ℝ))*‖(f.onScalar g) X‖^2)+
          (c/b^3)*(((localizedNearLabels L A s X).card:ℝ)*‖(f.onScalar g) X‖^2) := by
      funext X
      ring
    rw [he]
    exact (hf.sub (hn.const_mul (C*D*(A.card:ℝ)))).add (hk.const_mul (c/b^3))
  rw [IndicatorStrong.norm_sq_integral,←integral_const_mul]
  apply integral_mono_ae (hn.const_mul _) hi
  filter_upwards [f.coe_onScalar g] with X hX
  by_cases hz : f.toFun X=0
  · simp only [hX,hz,zero_mul,norm_zero,zero_pow (by omega : (2:ℕ)≠0),mul_zero,le_rfl]
  · have hkX := mul_le_mul_of_nonneg_left (hsupport X hz) (by positivity : 0≤c/b^3)
    have hcX := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
    have hw := weightedSiteCount_nonneg L A X
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [hkX,hcX,hw]

end HardSphere

end

end OAI
