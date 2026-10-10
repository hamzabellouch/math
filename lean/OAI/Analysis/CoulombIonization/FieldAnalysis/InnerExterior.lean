import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier
import OAI.Analysis.CoulombIonization.Variational.InnerPotential

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def sourceField (Z : ℝ) (mu : Measure Space) (y : Space) : ℝ :=
   Z/‖y‖-sourcePotential mu y

 lemma sourceField_le_nuclear (Z : ℝ) (mu : Measure Space) (y : Space) :
     sourceField Z mu y ≤ Z/‖y‖ := sub_le_self _ (sourcePotential_nonneg mu y)

 lemma sourceField_continuousOn (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) :
     ContinuousOn (sourceField Z mu) {y | h < ‖y‖} := by
   exact (continuousOn_const.div continuous_norm.continuousOn
     (fun y hy => ne_of_gt (hh.trans_lt hy))).sub
       (sourcePotential_continuousOn_exterior mu hs)

 lemma sourceField_weak_harmonic (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
     (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
     (∫ y, sourceField Z mu y*Δ g y) = 0 := by
   have hg0 : g 0 = 0 := by
     apply image_eq_zero_of_notMem_tsupport
     intro ht
     have hf : h < ‖(0 : Space)‖ := hsg ht
     simp only [norm_zero,not_lt_of_ge hh] at hf
   have hi : Integrable (fun y : Space => (Z/‖y‖)*Δ g y) :=
     continuousOn_mul_integrable_support hcg
       ((continuousOn_const.div continuous_norm.continuousOn
         (fun y hy => ne_of_gt (hh.trans_lt (hsg hy)))))
       (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hj : Integrable (fun y : Space => sourcePotential mu y*Δ g y) :=
     continuousOn_mul_integrable_support hcg
       ((sourcePotential_continuousOn_exterior mu hs).mono hsg)
       (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hn : (∫ y : Space, (Z/‖y‖)*Δ g y) = 0 := by
     have he : (fun y : Space => (Z/‖y‖)*Δ g y) =
         fun y => Z*(Δ g y/‖(0 : Space)-y‖) := by
       funext y
       simp only [zero_sub,norm_neg]
       ring
     rw [he,integral_const_mul]
     have ht := tfPotential_laplacian hg hcg (0 : Space)
     change (∫ y, Δ g y/‖(0 : Space)-y‖) = _ at ht
     rw [ht,hg0,mul_zero,neg_zero,mul_zero]
   simp only [sourceField,sub_mul]
   rw [integral_sub hi hj,hn,sourcePotential_weak_harmonic_exterior mu hs hg hcg hsg,sub_self]

 lemma sourceField_sub_const_weak (Z e : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
     (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
     (∫ y, (sourceField Z mu y-e)*Δ g y) = 0 := by
   have hi := continuousOn_mul_integrable_support hcg
     ((sourceField_continuousOn Z mu hh hs).mono hsg)
     (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hj : Integrable (fun x => e*Δ g x) := ((tfLaplacian_continuous hg).integrable_of_hasCompactSupport
     (tfLaplacian_compact hg hcg)).const_mul e
   simp_rw [sub_mul]
   rw [integral_sub hi hj,sourceField_weak_harmonic Z mu hh hs hg hcg hsg,
     integral_const_mul,compact_laplacian_mass hg hcg,mul_zero,sub_self]

 theorem sourceField_exterior_comparison (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h R C : ℝ} (hh : 0 ≤ h) (hR : h < R) (hC : 0 ≤ C)
     (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     (hb : ∀ y : Space, ‖y‖ = R → sourceField Z mu y ≤ C)
     {y : Space} (hy : R ≤ ‖y‖) : sourceField Z mu y ≤ C*R/‖y‖ := by
   have hRp : 0 < R := hh.trans_lt hR
   by_cases hfield : sourceField Z mu y ≤ 0
   · exact hfield.trans (div_nonneg (mul_nonneg hC hRp.le) (norm_nonneg y))
   apply le_of_forall_pos_le_add
   intro e he
   let T := max (‖y‖+1) ((|Z-C*R|+1)/e)
   have hyT : ‖y‖ < T := lt_of_lt_of_le (by linarith) (le_max_left _ _)
   have hRT : R < T := hy.trans_lt hyT
   have hT : 0 < T := hRp.trans hRT
   have hTe : |Z-C*R|+1 ≤ e*T := by
     have hv := (div_le_iff₀ he).mp (le_max_right (‖y‖+1) ((|Z-C*R|+1)/e))
     simpa only [T,mul_comm] using hv
   let K : Set Space := closedBall 0 T \ ball 0 R
   let v : Space → ℝ := fun x => sourceField (Z-C*R) mu x-e
   have hK : IsCompact K := (isCompact_closedBall (0 : Space) T).diff isOpen_ball
   have hKr : ∀ x ∈ K, R ≤ ‖x‖ := by
     intro x hx
     exact le_of_not_gt (fun ht => hx.2 (mem_ball_zero_iff.mpr ht))
   have hKT : ∀ x ∈ K, ‖x‖ ≤ T := fun _ hx => mem_closedBall_zero_iff.mp hx.1
   have hsub : K ⊆ {x | h < ‖x‖} := fun x hx => hR.trans_le (hKr x hx)
   have hiv : ContinuousOn v K := ((sourceField_continuousOn (Z-C*R) mu hh hs).mono hsub).sub continuousOn_const
   have hvi : ∀ x ∈ K, x ∉ interior K → v x ≤ 0 := by
     intro x hx hxi
     have hnorm : ‖x‖ = R ∨ ‖x‖ = T := by
       by_contra hne
       push Not at hne
       have hrx : R < ‖x‖ := lt_of_le_of_ne (hKr x hx) hne.1.symm
       have hxt : ‖x‖ < T := lt_of_le_of_ne (hKT x hx) hne.2
       have ho : IsOpen {z : Space | R < ‖z‖ ∧ ‖z‖ < T} :=
         (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
       apply hxi
       exact mem_interior.mpr ⟨{z : Space | R < ‖z‖ ∧ ‖z‖ < T},
         (fun z hz => ⟨mem_closedBall_zero_iff.mpr hz.2.le,
           fun hg => not_lt_of_ge hz.1.le (mem_ball_zero_iff.mp hg)⟩),ho,⟨hrx,hxt⟩⟩
     rcases hnorm with hrx | hxt
     · have hhx := hb x hrx
       have hex : v x = sourceField Z mu x-C-e := by
         dsimp [v,sourceField]
         rw [hrx]
         field_simp
         ring
       rw [hex]
       linarith
     · have hv := sourceField_le_nuclear (Z-C*R) mu x
       have hbound : (Z-C*R)/‖x‖ ≤ e := by
         rw [hxt]
         exact (div_le_iff₀ hT).mpr ((le_abs_self _).trans (by linarith [hTe]))
       dsimp [v]
       linarith
   have hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
       tsupport g ⊆ interior K ∩ {x | 0 < v x} → (∀ x, 0 ≤ g x) →
       0 ≤ ∫ x, v x*Δ g x := by
     intro g hg hcg hsg _
     exact (sourceField_sub_const_weak (Z-C*R) e mu hh hs hg hcg
       (hsg.trans (inter_subset_left.trans (interior_subset.trans hsub)))).ge
   have hvy := weak_subharmonic_positive_compact hK hiv hvi hw y
     (show y ∈ K from ⟨mem_closedBall_zero_iff.mpr hyT.le,
       fun ht => not_lt_of_ge hy (mem_ball_zero_iff.mp ht)⟩)
   have heq : v y = sourceField Z mu y-C*R/‖y‖-e := by
     dsimp [v,sourceField]
     ring
   rw [heq] at hvy
   linarith

end CoulombAtom

end

end OAI
