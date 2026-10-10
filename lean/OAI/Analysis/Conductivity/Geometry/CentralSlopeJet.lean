import Mathlib
import OAI.Analysis.Conductivity.Branching.CentralJoinCover
import OAI.Analysis.Conductivity.Geometry.CutSlopeGradient
import OAI.Analysis.Conductivity.Variational.WholeBallJetFormula
import OAI.Analysis.Conductivity.Branching.ChildTransportFormula

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def collarSlopeJet (χ : (Fin 3 → ℝ) → ℝ) (a b κ : ℝ) (y : Fin 3 → ℝ) : JetFiber :=
  WithLp.toLp 2 (Fin.cases
    (κ*(χ y*max 0 (a*(sourceCollarTime y-b))))
    (fun i => κ*(fderiv ℝ χ y (Pi.single i 1)*max 0 (a*(sourceCollarTime y-b))+
      χ y*(if 0<a*(sourceCollarTime y-b) then
        fderiv ℝ (fun z => a*(sourceCollarTime z-b)) y (Pi.single i 1) else 0))))

lemma collarSlopeJet_eq_zero {χ : (Fin 3 → ℝ) → ℝ} {a b κ : ℝ} {y : Fin 3 → ℝ}
    (ht : a*(sourceCollarTime y-b)≤0) : collarSlopeJet χ a b κ y=0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [collarSlopeJet,max_eq_left ht,not_lt.mpr ht]

lemma collarSlopeJet_zero_not_tsupport {χ : (Fin 3 → ℝ) → ℝ} {a b κ : ℝ} {y : Fin 3 → ℝ}
    (hy : y∉tsupport χ) : collarSlopeJet χ a b κ y=0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [collarSlopeJet,image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy]

lemma compact_collar_slope_jet {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a : ℝ} (ha : a≠0) {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (κ l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ w.val=ᵐ[ballMeasure]
      (fun x => collarSlopeJet χ a b κ (WithLp.ofLp x)) := by
  obtain ⟨w,hw,hwe⟩ := compact_collar_slope_value_gradient hχ hc hχb ha hb κ l r hl hr hχs
  refine ⟨w,hw,?_⟩
  filter_upwards [hwe] with x hx
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx.1
  · exact hx.2 j

lemma ballWholePiJetCLM_slope_ae {z : JetSpace} {χ : (Fin 3 → ℝ) → ℝ} {a b κ : ℝ}
    (hs : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball)
    (he : z=ᵐ[ballMeasure] (fun x => collarSlopeJet χ a b κ (WithLp.ofLp x))) :
    ballWholePiJetCLM z=ᵐ[volume] collarSlopeJet χ a b κ := by
  apply (ballWholePiJetCLM_ae_of_ae z (collarSlopeJet χ a b κ) he).trans
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    split_ifs with hb
    · rfl
    · exact (collarSlopeJet_zero_not_tsupport (fun hy => hb (hs y hy))).symm)

def physicalChildSlopeJet (k : Fin 2) (a κ : ℝ) (y : Fin 3 → ℝ) : JetFiber :=
  let z := collarSlopeJet (centralJoinChildCutoff k) a (-centralThickness) κ
    ((sourceChildHomeomorph (actualChildSign k)).symm y)
  WithLp.toLp 2 (Fin.cases (z 0) (fun j => sourceScale⁻¹*z (childAxis j).succ))

lemma exists_parentSlopeExtension {a : ℝ} (ha : a<0) (κ : ℝ) :
    ∃ w : H1,w∈H10 ∧ w.val=ᵐ[ballMeasure] (fun x =>
      collarSlopeJet (centralJoinPartition 1) a centralThickness κ (WithLp.ofLp x)) :=
  compact_collar_slope_jet (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1) ha.ne
    (by norm_num [centralThickness]) κ 0 (2*centralThickness)
    (by norm_num) (by norm_num [centralThickness]) centralJoinPartition_parent_support

lemma exists_childSlopeExtension {a : ℝ} (ha : 0<a) (κ : ℝ) (k : Fin 2) :
    ∃ w : H1,w∈H10 ∧ w.val=ᵐ[ballMeasure]
      (fun x => physicalChildSlopeJet k a κ (WithLp.ofLp x)) := by
  obtain ⟨w,hw,hwe⟩ := compact_collar_slope_jet (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k) ha.ne'
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ (-2*centralThickness) 0 (by norm_num [centralThickness]) (by norm_num)
    (centralJoinChildCutoff_support k)
  refine ⟨childH10Transport k ⟨w,hw⟩,childH10Transport_mem_H10 k _,?_⟩
  have hB : ∀ y∈tsupport (centralJoinChildCutoff k),WithLp.toLp 2 y∈ball := by
    intro y hy
    have hb := centralJoinChildCutoff_support k hy
    exact sourceBand_mem_ball ⟨le_trans (by norm_num [centralThickness]) hb.1,
      le_trans hb.2 (by norm_num)⟩
  exact childTransportJetCLM_ae_of_ae k w.val _ (ballWholePiJetCLM_slope_ae hB hwe)

lemma parentSlopeJet_zero_central {a : ℝ} (ha : a<0) (κ : ℝ) {y : Fin 3 → ℝ}
    (hy : y∈centralPhysical) : collarSlopeJet (centralJoinPartition 1) a centralThickness κ y=0 :=
  collarSlopeJet_eq_zero (mul_nonpos_of_nonpos_of_nonneg ha.le
    (sub_nonneg.mpr ((centralPhysical_time_iff y).mp hy).1))

lemma physicalChildSlopeJet_zero_central {a : ℝ} (ha : 0<a) (κ : ℝ) (k : Fin 2)
    {y : Fin 3 → ℝ} (hy : y∈centralPhysical) : physicalChildSlopeJet k a κ y=0 := by
  have hz := collarSlopeJet_eq_zero (χ:=centralJoinChildCutoff k) (κ:=κ)
    (mul_nonpos_of_nonneg_of_nonpos ha.le
      (sub_nonpos.mpr (((centralPhysical_time_iff y).mp hy).2 k)))
  dsimp only [physicalChildSlopeJet]
  rw [hz]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def centralSlopeJet (a κ : Fin 3 → ℝ) (y : Fin 3 → ℝ) : JetFiber :=
  collarSlopeJet (centralJoinPartition 1) (a 0) centralThickness (κ 0) y+
    physicalChildSlopeJet 0 (a 1) (κ 1) y+physicalChildSlopeJet 1 (a 2) (κ 2) y

theorem centralSlopeExtension_exists (a κ : Fin 3 → ℝ)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) :
    ∃ w : H1,w∈H10 ∧ w.val=ᵐ[ballMeasure]
      (fun x => centralSlopeJet a κ (WithLp.ofLp x)) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical → w.val x=0) := by
  obtain ⟨wp,hp,hep⟩ := exists_parentSlopeExtension ha₀ (κ 0)
  obtain ⟨w₀,h₀,he₀⟩ := exists_childSlopeExtension (ha 0) (κ 1) 0
  obtain ⟨w₁,h₁,he₁⟩ := exists_childSlopeExtension (ha 1) (κ 2) 1
  have he : (wp+w₀+w₁).val=ᵐ[ballMeasure] (fun x => centralSlopeJet a κ (WithLp.ofLp x)) := by
    filter_upwards [Lp.coeFn_add wp.val w₀.val,Lp.coeFn_add (wp.val+w₀.val) w₁.val,hep,he₀,he₁]
      with x h₀ h₁ hp hc₀ hc₁
    change (wp.val+w₀.val+w₁.val) x=_
    simp only [Pi.add_apply] at h₀ h₁
    rw [h₁,h₀,hp,hc₀,hc₁]
    rfl
  refine ⟨wp+w₀+w₁,H10.add_mem (H10.add_mem hp h₀) h₁,he,?_⟩
  filter_upwards [he] with x hx
  intro hy
  rw [hx]
  dsimp only [centralSlopeJet]
  have hzero₀ : physicalChildSlopeJet 0 (a 1) (κ 1) (WithLp.ofLp x)=0 := by
    exact physicalChildSlopeJet_zero_central (show 0<a 1 from ha 0) _ 0 hy
  have hzero₁ : physicalChildSlopeJet 1 (a 2) (κ 2) (WithLp.ofLp x)=0 := by
    exact physicalChildSlopeJet_zero_central (show 0<a 2 from ha 1) _ 1 hy
  rw [parentSlopeJet_zero_central ha₀ _ hy,hzero₀,hzero₁,add_zero,add_zero]

end ScalarConductivity

end

end OAI
