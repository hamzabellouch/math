import OAI.Analysis.AncientFlat.Geometry.ExtensionBox
import OAI.Analysis.AncientFlat.Geometry.ExtensionCutoffMatch
import OAI.Analysis.AncientFlat.Evolution.FiniteSourceBound

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma extensionWeight_normBox {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ K : ℝ, 0<K ∧ ∀ T a : ℝ, 0<T → 0<a → a≤1/16 → ∀ p : V × ℝ,
      p.2<0 → sigma p=1 → HolderBound α (normBox a p) (extensionWeight ψ T) K := by
  obtain ⟨K,hK,hreg⟩ := regularWeight_holder (V := V) hψ α hα hα1
  refine ⟨K+1,by linarith,?_⟩
  intro T a hT ha ha1 p hp hs
  by_cases hT4 : T≤4
  · have hb := (hreg T hT hT4).restrict (fun q hq => normBox_bounds ha ha1 hp hs hq)
    have he (q : V × ℝ) (hq : q∈normBox a p) : extensionWeight ψ T q=regularWeight ψ T q :=
      extensionWeight_eq_regular hψ hT q (normBox_time hq) (by linarith [(normBox_sigma ha ha1 hp hs hq).1])
    constructor
    · intro q hq
      rw [he q hq]
      exact (hb.1 q hq).trans (by linarith)
    · intro q hq r hr
      rw [he q hq,he r hr]
      exact (hb.2 q hq r hr).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (pdist_nonneg _ _) _))
  · have he (q : V × ℝ) (hq : q∈normBox a p) : extensionWeight ψ T q=1 := by
      have hqb := normBox_bounds ha ha1 hp hs hq
      simp only [extensionWeight,ite_eq_left (show -T≤q.2 by linarith)]
    constructor
    · intro q hq
      rw [he q hq]
      simpa using (show (1:ℝ)≤K+1 by linarith)
    · intro q hq r hr
      rw [he q hq,he r hr,sub_self,norm_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (pdist_nonneg _ _) _)
lemma FiniteYBound.extension_normBox {ψ : ℝ → ℝ} (hψ : ExtensionCutoff ψ)
    {α w a T M K : ℝ} {f : V × ℝ → ℂ} (hf : FiniteYBound α w a T M f)
    (hα : 0≤α) (hw : w≤4) (hT : 0<T) (ha : 0<a) (ha1 : a≤1/16) (hM : 0≤M) (hK : 0≤K)
    (p : V × ℝ) (hp : p.2<0) (hs : sigma p=1)
    (hk : HolderBound α (normBox a p) (extensionWeight ψ T) K) :
    HolderBound α (normBox a p) (innerExtension ψ T f)
      (2*K*(((1:ℝ)/8)^(w-4)+((1:ℝ)/8)^(w-4)*((1:ℝ)/8)^(-α)+
        2*((1:ℝ)/8)^(w-4)/(a*((1:ℝ)/8))^α)*M) := by
  let C := ((1:ℝ)/8)^(w-4)+((1:ℝ)/8)^(w-4)*((1:ℝ)/8)^(-α)+2*((1:ℝ)/8)^(w-4)/(a*((1:ℝ)/8))^α
  have hC : 0≤C := by dsimp [C]; positivity
  by_cases hx : ∃ q∈normBox a p, extensionWeight ψ T q≠0
  · have hproj := normBox_project_sigma hψ hT ha ha1 hp hs hx
    have hh := hf.holder_on hα hw ha hM (by norm_num : (0:ℝ)<1/8)
      (Ω := timeProject T '' normBox a p)
      (by rintro _ ⟨q,hq,rfl⟩; exact timeProject_mem hT q (normBox_time hq))
      (by rintro _ ⟨q,hq,rfl⟩; exact hproj q hq)
    have hg : HolderBound α (normBox a p) (fun q => f (timeProject T q)) (C*M) := by
      refine ⟨fun q hq => hh.1 _ (mem_image_of_mem _ hq),?_⟩
      intro q hq r hr
      apply (hh.2 _ (mem_image_of_mem _ hq) _ (mem_image_of_mem _ hr)).trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pdist_nonneg _ _) (timeProject_pdist T q r) hα) (mul_nonneg hC hM)
    have hm := hk.smul hg hK (mul_nonneg hC hM)
    simpa only [←innerExtension_eq,mul_assoc] using hm
  · have hz (q : V × ℝ) (hq : q∈normBox a p) : innerExtension ψ T f q=0 := by
      rw [innerExtension_eq]
      have he : extensionWeight ψ T q=0 := by by_contra hn; exact hx ⟨q,hq,hn⟩
      rw [he,zero_smul]
    constructor
    · intro q hq
      rw [hz q hq,norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hC) hM
    · intro q hq r hr
      rw [hz q hq,hz r hr,sub_self,norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hC) hM) (Real.rpow_nonneg (pdist_nonneg _ _) _)
end FlatWeighted

end

end OAI
