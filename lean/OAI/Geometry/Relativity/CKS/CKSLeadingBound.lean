import OAI.Geometry.Relativity.CKS.MixedMassCompact
import OAI.Geometry.Relativity.CKS.CKSCoefficientRealization
import OAI.Geometry.Relativity.CKS.LogPhysicalTensor

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

attribute [local irreducible] cksMassJet leadingMassJet

lemma leadingMassJet_continuousAt {j : MassInput}
    (h : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ContinuousAt leadingMassJet j := by
  have hr := massRegion_zero h
  have hm := (cksMassJet_smooth hr.1 hr.2).continuousAt.comp
    (show ContinuousAt (fun i : MassInput => ((0:ScalarThreeJet),i)) j from by fun_prop)
  change ContinuousAt (fun i : MassInput => cksMassJet 0 i) j at hm
  have he : (fun i : MassInput => cksMassJet 0 i) = (fun i => leadingMassJet i) := funext (fun i => cksMassJet_zero i)
  rw [he] at hm
  exact hm

lemma leading_mass_uniform_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : MassInput, j.1 0 ∈ K → ‖j‖ ≤ B → ‖leadingMassJet j‖ ≤ C := by
  obtain ⟨C,hC⟩ := (boundedMassFamily_compact hK B).exists_bound_of_continuousOn
    (fun j hj => (leadingMassJet_continuousAt (hreg _ hj.1)).continuousWithinAt)
  exact ⟨max C 0,le_max_right _ _,fun j hj hb => (hC j (boundedMassFamily_mem hj hb)).trans (le_max_left _ _)⟩

lemma cks_leading_mixed_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      f.RegularAt x → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (cksLeadingField f) x‖ ≤ C := by
  obtain ⟨C,hC,hh⟩ := leading_mass_uniform_bounded hK hreg (216*B)
  refine ⟨C,hC,?_⟩
  intro f x hf hσ hs hmg heg hmk hek hb hmr herr
  have hd : determinant (f.sigma x) ≠ 0 := hreg _ hσ
  have hn := normalizeMassLogFields_regular hf
  have hbound := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  have hreal := cksLeadingField_realized hn hd
  change actualScalarJet (cksLeadingField f) x=leadingMassJet (massInputOf (normalizeMassLogFields f) x) at hreal
  rw [hreal]
  exact hh _ hσ hbound

def logQError (f : MassFields) : Point → Mat := fun y =>
  radiusPower (-3) y • f.mg y+radiusPower (-2) y • f.eg y

lemma logQError_diff {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 3 (logQError f) x :=
  ((radiusPower_diff (-3) 3 x).smul hf.mg).add ((radiusPower_diff (-2) 3 x).smul hf.eg)

lemma logQError_three_bound {f : MassFields} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hr : 1 ≤ Real.exp (x 0)) (hf : f.RegularAt x)
    (hm : ‖matrixThreeJets f.mg x‖ ≤ B)
    (he : ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2) (a b : A) :
    ‖actualThreeJet (fun y => logQError f y a b) x‖ ≤ 280*B/Real.exp (x 0)^3 := by
  have hmab := (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hm)
  have heab := (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans he)
  have h3 : ‖actualThreeJet (radiusPower (-3)) x‖ ≤ 27/Real.exp (x 0)^3 := by
    have hh := radiusPower_three_norm (-3) x
    norm_num only [abs_neg,abs_of_pos (show (0:ℝ)<3 by norm_num),max_eq_right (show (1:ℝ)≤3 by norm_num),radiusPower_minus_three] at hh
    norm_num at hh
    exact hh
  have h2 : ‖actualThreeJet (radiusPower (-2)) x‖ ≤ 8/Real.exp (x 0)^2 := by
    have hh := radiusPower_three_norm (-2) x
    norm_num only [abs_neg,abs_of_pos (show (0:ℝ)<2 by norm_num),max_eq_right (show (1:ℝ)≤2 by norm_num)] at hh
    rw [show (-2:ℝ)=-(2:ℕ) by norm_num,radiusPower_neg_nat] at hh
    norm_num at hh
    exact hh
  change ‖actualThreeJet (fun y => radiusPower (-3) y*f.mg y a b+radiusPower (-2) y*f.eg y a b) x‖ ≤ _
  rw [actualThreeJet_add ((radiusPower_diff (-3) 3 x).mul (component_diff hf.mg a b))
    ((radiusPower_diff (-2) 3 x).mul (component_diff hf.eg a b)),
    actualThreeJet_mul (radiusPower_diff (-3) 3 x) (component_diff hf.mg a b),
    actualThreeJet_mul (radiusPower_diff (-2) 3 x) (component_diff hf.eg a b)]
  have hraw := (norm_add_le _ _).trans (add_le_add (productThreeJet_norm h3 hmab) (productThreeJet_norm h2 heab))
  apply hraw.trans
  have hp : Real.exp (x 0)^3 ≤ Real.exp (x 0)^4 := by
    simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hr (show 0≤Real.exp (x 0)^3 by positivity)
  have hdec : B/Real.exp (x 0)^4 ≤ B/Real.exp (x 0)^3 :=
    div_le_div_of_nonneg_left hB (by positivity) hp
  have hid : 8*(27/Real.exp (x 0)^3)*B+8*(8/Real.exp (x 0)^2)*(B/Real.exp (x 0)^2) =
      216*B/Real.exp (x 0)^3+64*(B/Real.exp (x 0)^4) := by ring
  rw [hid]
  calc
    _ ≤ 216*B/Real.exp (x 0)^3+64*(B/Real.exp (x 0)^3) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdec (show (0:ℝ) ≤ 64 by norm_num))
    _ = _ := by ring

end
end CKSMixedGeometry

end

end OAI
