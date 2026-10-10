import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledObservable
import OAI.Analysis.HardSphere.Cutoffs.PathDiameter

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshProduct {L : Length} (m : ℕ) (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :=
  ∏ j : Fin m, F (meshSegment j ω)

lemma meshProduct_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshProduct m F) := by
  unfold meshProduct
  exact Finset.measurable_prod _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

@[simp] lemma meshProduct_one {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :
    meshProduct 1 F ω=F ω := by simp [meshProduct]

lemma splitTime_mul {τ : ℝ} (hτ : 0<τ) {m : ℕ} (hm : 0 < m) :
    splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)=
      splitTime 1 (m:ℝ) (by norm_num) (by exact_mod_cast hm) := by
  apply Subtype.ext
  change τ/(τ+(m:ℝ)*τ)=1/(1+(m:ℝ))
  have hτ' := ne_of_gt hτ
  have hm' : (1:ℝ)+(m:ℝ)≠0 := by positivity
  field_simp

lemma meshProduct_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshProduct (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)*
      meshProduct m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshProduct,Fin.prod_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshProduct_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ B^m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) *
      meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshProduct_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.mul hsecond
    have he (w : CoordinatePaths 1) :
        meshProduct (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshProduct_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)*B^m ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshProduct m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshProduct_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_const_mul _ hmeas]
        exact mul_le_mul_right (ih _) _
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)*B^m :=
        lintegral_mul_const _ (hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable)
      _ ≤ B*B^m := mul_le_mul_left (hB X) _
      _ = B^(m+1) := by rw [pow_succ]; exact mul_comm _ _

end HardSphere.PathCutoff

namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

def meshSum {L : Length} (m : ℕ) (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :=
  ∑ j : Fin m, F (meshSegment j ω)

lemma meshSum_measurable {L : Length} (m : ℕ) {F : ConfigurationPath 1 L → ℝ≥0∞}
    (hF : Measurable F) : Measurable (meshSum m F) := by
  unfold meshSum
  exact Finset.measurable_sum _ (fun j _ ↦ hF.comp (meshSegment_continuous L j).measurable)

@[simp] lemma meshSum_one {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (ω : ConfigurationPath 1 L) :
    meshSum 1 F ω=F ω := by simp [meshSum]

lemma meshSum_succ {L : Length} {m : ℕ} (hm : 0 < m) (F : ConfigurationPath 1 L → ℝ≥0∞)
    {τ : ℝ} (hτ : 0<τ) (ω : ConfigurationPath 1 L) :
    meshSum (m+1) F ω =
      F (configurationPrefix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω)+
      meshSum m F (configurationSuffix 1 L (splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)) ω) := by
  rw [splitTime_mul hτ hm]
  simp only [meshSum,Fin.sum_univ_succ,meshSegment_first hm,meshSegment_next hm]

lemma meshSum_free_bound {L : Length} (F : ConfigurationPath 1 L → ℝ≥0∞) (hF : Measurable F)
    {τ : ℝ} (hτ : 0<τ) (B : ℝ≥0∞)
    (hB : ∀ X : Configuration 1 L, ∫⁻w,F (freeTrajectory 1 L τ w X) ∂coordinateWiener 1 ≤ B) :
    ∀ m : ℕ, 0 < m → ∀ X : Configuration 1 L,
      ∫⁻w, meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w X) ∂coordinateWiener 1 ≤ (m:ℝ≥0∞)*B := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hB
  | succ m hm ih =>
    intro X
    let u := splitTime τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ)
    let G : CoordinatePaths 1 × CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
      F (freeTrajectory 1 L τ w.1 X) +
      meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))
    have hfirst : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w.1 X)) :=
      hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_fst.prodMk continuous_const)).measurable
    have hsecond : Measurable (fun w : CoordinatePaths 1 × CoordinatePaths 1 ↦
        meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w.2 (freeTrajectory 1 L τ w.1 X 1))) :=
      (meshSum_measurable m hF).comp
        (measurable_snd.comp (split_fixedTrajectory_measurable 1 L τ ((m:ℝ)*τ) X))
    have hG : Measurable G := hfirst.add hsecond
    have he (w : CoordinatePaths 1) :
        meshSum (m+1) F (freeTrajectory 1 L (((m+1:ℕ):ℝ)*τ) w X)=
        G (fun p ↦ normalizedPrefix u (w p), fun p ↦ normalizedSuffix u (w p)) := by
      have hmul : (((m+1:ℕ):ℝ)*τ)=τ+(m:ℝ)*τ := by push_cast; ring
      rw [hmul,meshSum_succ hm F hτ]
      have hp := congrArg Prod.fst (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      have hq := congrArg Prod.snd (split_fixedTrajectory 1 L τ ((m:ℝ)*τ) hτ (mul_pos (by exact_mod_cast hm) hτ) w X)
      dsimp only [Prod.fst,Prod.snd] at hp hq
      rw [hp,hq]
    calc
      _ = ∫⁻w,G (fun p ↦ normalizedPrefix u (w p),fun p ↦ normalizedSuffix u (w p)) ∂coordinateWiener 1 := lintegral_congr he
      _ = ∫⁻w,G w ∂(coordinateWiener 1).prod (coordinateWiener 1) :=
        (coordinateSplit_preserving 1 u (splitTime_pos _ _ _ _) (splitTime_lt_one _ _ _ _)).lintegral_comp hG
      _ = ∫⁻w₁,∫⁻w₂,G (w₁,w₂) ∂coordinateWiener 1 ∂coordinateWiener 1 := lintegral_prod _ hG.aemeasurable
      _ ≤ ∫⁻w₁,F (freeTrajectory 1 L τ w₁ X)+(m:ℝ≥0∞)*B ∂coordinateWiener 1 := by
        apply lintegral_mono
        intro w₁
        dsimp only [G]
        have hmeas : Measurable (fun w₂ : CoordinatePaths 1 ↦
            meshSum m F (freeTrajectory 1 L ((m:ℝ)*τ) w₂ (freeTrajectory 1 L τ w₁ X 1))) :=
          (meshSum_measurable m hF).comp
            ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
        exact add_le_add le_rfl (ih _)
      _ = (∫⁻w₁,F (freeTrajectory 1 L τ w₁ X) ∂coordinateWiener 1)+(m:ℝ≥0∞)*B := by
        have hmeas : Measurable (fun w : CoordinatePaths 1 ↦ F (freeTrajectory 1 L τ w X)) := hF.comp ((freeTrajectory_continuous 1 L τ).comp (continuous_id.prodMk continuous_const)).measurable
        rw [lintegral_add_left hmeas,lintegral_const,measure_univ,mul_one]
      _ ≤ B+(m:ℝ≥0∞)*B := add_le_add (hB X) le_rfl
      _ = ((m+1:ℕ):ℝ≥0∞)*B := by push_cast; ring

end HardSphere.PathCutoff

end

end OAI
