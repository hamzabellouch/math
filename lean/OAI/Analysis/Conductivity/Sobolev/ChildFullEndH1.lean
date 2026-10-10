import Mathlib
import OAI.Analysis.Conductivity.Branching.ParentFullEndEnergy
import OAI.Analysis.Conductivity.Branching.ChildEndPartition

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem childFullEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
      weakValue w x=fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=
        fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) i) := by
  obtain ⟨χ,η,hχ,hχc,hχb,hχs,hη,hηc,hηb,hηs,hpart⟩ := child_end_partition_exists
  generalize hU : childCompletionJoin s hs ha k hχ hχc hχb hχs p = u
  have hu : u∈H10 := by
    rw [←hU]
    exact childCompletionJoin_mem_H10 s hs ha k hχ hχc hχb hχs p
  have hue := childCompletionJoin_end_ae s hs ha k hχ hχc hχb hχs p
  rw [hU] at hue
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient hχ hχc hχb ha.ne'
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ (-2*centralThickness) 0 (by norm_num [centralThickness]) (by norm_num) hχs
  have hR : 0≤a*(3*centralThickness/2) :=
    mul_nonneg ha.le (by norm_num [centralThickness])
  have hT : ∀ t∈Icc (-3*centralThickness/4) (centralThickness/2),
      affineEndTime a (-centralThickness) t∈Icc 0 (a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · apply mul_nonneg ha.le
      dsimp [centralThickness] at *
      linarith [ht.1]
    · have hm := mul_nonneg ha.le
        (sub_nonneg.mpr ht.2)
      nlinarith
  have hpos : ∀ t∈Icc (-3*centralThickness/4) (centralThickness/2),
      0<a*(t-(-centralThickness)) := by
    intro t ht
    apply mul_pos ha
    dsimp [centralThickness] at *
    linarith [ht.1]
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s k.succ p) κ ha.ne' hR
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show -3*centralThickness/4≤centralThickness/2 by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    hT hpos hη hηc hηb hηs
  refine ⟨u+v+z,H10.add_mem (H10.add_mem hu hv) hz,?_⟩
  have hne := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
        norm_num [centralThickness])))
  apply fullEnd_partition_jet s (centralT s k.succ p) a (-centralThickness) κ hχ hη hpart
      (u:=u) (v:=v) (z:=z) _ hue hve hze
  filter_upwards [hne] with x hnx hx
  exact mul_pos ha (sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hnx)))

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_local_jet (k : Fin 2) (u : H10)
    {D : Set (Fin 3 → ℝ)}
    (hD : ∀ y∈D,WithLp.toLp 2 y∈ball)
    (V : (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=V (WithLp.ofLp x) ∧
      ∀ i,weakGradient u.val x i=G (WithLp.ofLp x) i) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=
        V ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
      ∀ i,weakGradient (childH10Transport k u) x i=
        sourceScale⁻¹*G ((sourceChildHomeomorph (actualChildSign k)).symm
          (WithLp.ofLp x)) (childAxis i) := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hb := hD _ hm
  have hloc := hx hb hm
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=_
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact hloc.1
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=_
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact congrArg (fun q : ℝ => sourceScale⁻¹*q) (hloc.2 (childAxis i))

theorem physicalChildFullEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈
        sourceClosedCollarBand (-centralThickness) 0 →
      weakValue w x=fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
      ∀ i,weakGradient w x i=sourceScale⁻¹*
        fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ
          ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis i)) := by
  obtain ⟨u,hu,he⟩ := childFullEnd_H10 s hs ha k κ p
  refine ⟨childH10Transport k ⟨u,hu⟩,childH10Transport_mem_H10 k _,?_⟩
  apply childH10Transport_local_jet k ⟨u,hu⟩ _ _ _ he
  intro y hy
  apply sourceBand_mem_ball
  constructor <;> dsimp [centralThickness] at * <;> linarith [hy.1,hy.2]

end ScalarConductivity

end

end OAI
