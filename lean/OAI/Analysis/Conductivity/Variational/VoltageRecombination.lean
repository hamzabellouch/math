import Mathlib
import OAI.Analysis.Conductivity.Sobolev.VoltageH1Completion
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.Elementwise

def voltageRecombine (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (Matrix.toLin' M).toContinuousLinearMap

def fieldRecombine (M : Matrix (Fin 2) (Fin 2) ℝ) : FieldVector →L[ℝ] FieldVector :=
  ({ toFun := fun w => WithLp.toLp 2 (fun ij => ∑ k,M ij.2 k*w (ij.1,k))
     map_add' := by
       intro v w
       ext ij
       simp [mul_add,Finset.sum_add_distrib]
     map_smul' := by
       intro c v
       ext ij
       simp
       ring } : FieldVector →ₗ[ℝ] FieldVector).toContinuousLinearMap

@[simp] lemma voltageRecombine_apply (M : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → ℝ) (j : Fin 2) : voltageRecombine M v j=∑ k,M j k*v k := rfl

@[simp] lemma fieldRecombine_apply (M : Matrix (Fin 2) (Fin 2) ℝ)
    (w : FieldVector) (ij : Fin 3 × Fin 2) :
    fieldRecombine M w ij=∑ k,M ij.2 k*w (ij.1,k) := rfl

lemma voltageGradient_recombine (M : Matrix (Fin 2) (Fin 2) ℝ)
    {v : Coord3 → Fin 2 → ℝ} {x : Coord3} (hv : DifferentiableAt ℝ v x) :
    voltageGradient (fun x => voltageRecombine M (v x)) x=
      fieldRecombine M (voltageGradient v x) := by
  unfold voltageGradient
  have hd : fderiv ℝ (fun x => voltageRecombine M (v x)) x=
      (voltageRecombine M).comp (fderiv ℝ v x) := by
    simpa only [Function.comp_def] using ((voltageRecombine M).hasFDerivAt.comp x hv.hasFDerivAt).fderiv
  rw [hd]
  ext ij
  simp [gradientVectorCLM,fieldVector,gradientColumns,LinearMap.toMatrix',fieldRecombine_apply,
    voltageRecombine_apply]

def voltageJetRecombine (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) : VoltageJetSpace μ U →L[ℝ] VoltageJetSpace μ U :=
  ((voltageRecombine M).compLpL 2 (μ.restrict U)).prodMap
    ((fieldRecombine M).compLpL 2 (μ.restrict U))

lemma voltageJetRecombine_toLp (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {v : Coord3 → Fin 2 → ℝ}
    (hv : Differentiable ℝ v) (hm : MemLp v 2 (μ.restrict U))
    (hg : MemLp (voltageGradient v) 2 (μ.restrict U)) :
    ∃ (hm' : MemLp (fun x => voltageRecombine M (v x)) 2 (μ.restrict U))
      (hg' : MemLp (voltageGradient (fun x => voltageRecombine M (v x))) 2 (μ.restrict U)),
      voltageJetRecombine μ U M (hm.toLp _,hg.toLp _)=(hm'.toLp _,hg'.toLp _) := by
  have hm' : MemLp (fun x => voltageRecombine M (v x)) 2 (μ.restrict U) := by
    simpa only [Function.comp_def] using (voltageRecombine M).lipschitzWith.comp_memLp (map_zero _) hm
  have hg' : MemLp (voltageGradient (fun x => voltageRecombine M (v x))) 2 (μ.restrict U) := by
    have hh := (fieldRecombine M).lipschitzWith.comp_memLp (map_zero _) hg
    exact hh.ae_eq (Eventually.of_forall fun x => (voltageGradient_recombine M (hv x)).symm)
  refine ⟨hm',hg',?_⟩
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(voltageRecombine M).coeFn_compLpL (hm.toLp _),hm.coeFn_toLp,hm'.coeFn_toLp]
      with x h1 h2 h3
    change ((voltageRecombine M).compLpL 2 (μ.restrict U) (hm.toLp _)) x=_
    rw [h1,h2,h3]
  · apply Lp.ext
    filter_upwards [(fieldRecombine M).coeFn_compLpL (hg.toLp _),hg.coeFn_toLp,hg'.coeFn_toLp]
      with x h1 h2 h3
    change ((fieldRecombine M).compLpL 2 (μ.restrict U) (hg.toLp _)) x=_
    rw [h1,h2,h3,voltageGradient_recombine M (hv x)]

lemma voltageJetRecombine_smooth (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {z : VoltageJetSpace μ U}
    (hz : z∈smoothVoltageJets μ U) : voltageJetRecombine μ U M z∈smoothVoltageJets μ U := by
  obtain ⟨v,hv,hm,hg,rfl⟩ := hz
  obtain ⟨hm',hg',he⟩ := voltageJetRecombine_toLp μ U M (hv.differentiable (by simp)) hm hg
  exact ⟨_,(voltageRecombine M).contDiff.comp hv,hm',hg',he⟩

lemma voltageJetRecombine_compact (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {z : VoltageJetSpace μ U}
    (hz : z∈compactVoltageJets μ U) : voltageJetRecombine μ U M z∈compactVoltageJets μ U := by
  obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := hz
  obtain ⟨hm',hg',he⟩ := voltageJetRecombine_toLp μ U M (hv.differentiable (by simp)) hm hg
  refine ⟨_,(voltageRecombine M).contDiff.comp hv,hvc.comp_left (map_zero _),?_,hm',hg',he⟩
  exact (tsupport_comp_subset (map_zero (voltageRecombine M)) v).trans hvs

theorem voltageJetRecombine_H1 (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {z : VoltageJetSpace μ U}
    (hz : z∈voltageH1Jets μ U) : voltageJetRecombine μ U M z∈voltageH1Jets μ U := by
  have hs : voltageH1Jets μ U ≤ (voltageH1Jets μ U).comap (voltageJetRecombine μ U M).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro w hw
      exact (Submodule.subset_span (voltageJetRecombine_smooth μ U M hw) |>
        (Submodule.span ℝ (smoothVoltageJets μ U)).le_topologicalClosure)
    · exact (Submodule.isClosed_topologicalClosure _).preimage (voltageJetRecombine μ U M).continuous
  exact hs hz

theorem voltageJetRecombine_H10 (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {z : VoltageJetSpace μ U}
    (hz : z∈zeroVoltageJets μ U) : voltageJetRecombine μ U M z∈zeroVoltageJets μ U := by
  have hs : zeroVoltageJets μ U ≤ (zeroVoltageJets μ U).comap (voltageJetRecombine μ U M).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · intro w hw
      exact (compactVoltageJetModule μ U).le_topologicalClosure (voltageJetRecombine_compact μ U M hw)
    · exact (Submodule.isClosed_topologicalClosure _).preimage (voltageJetRecombine μ U M).continuous
  exact hs hz

lemma fieldRecombine_inner (M : Matrix (Fin 2) (Fin 2) ℝ) (v w : FieldVector) :
    inner ℝ v (fieldRecombine M w)=inner ℝ (fieldRecombine M.transpose v) w := by
  simp [PiLp.inner_apply,RCLike.inner_apply,fieldRecombine_apply,
    Fintype.sum_prod_type,Fin.sum_univ_three,Fin.sum_univ_two,Matrix.transpose_apply]
  ring

lemma fieldRecombine_innerLp (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v w : Lp FieldVector 2 (μ.restrict U)) :
    inner ℝ v ((fieldRecombine M).compLpL 2 (μ.restrict U) w)=
      inner ℝ ((fieldRecombine M.transpose).compLpL 2 (μ.restrict U) v) w := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fieldRecombine M).coeFn_compLpL w,
    (fieldRecombine M.transpose).coeFn_compLpL v] with x hx hy
  rw [hx,hy,fieldRecombine_inner]

theorem voltageJetRecombine_cauchy (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {F G : Lp FieldVector 2 (μ.restrict U)}
    (h : ∀ W : voltageH1Jets μ U,inner ℝ W.val.2 F=inner ℝ W.val.2 G) :
    ∀ W : voltageH1Jets μ U,
      inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (μ.restrict U) F)=
      inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (μ.restrict U) G) := by
  intro W
  rw [fieldRecombine_innerLp,fieldRecombine_innerLp]
  exact h ⟨voltageJetRecombine μ U M.transpose W.val,
    voltageJetRecombine_H1 μ U M.transpose W.property⟩

theorem voltageJetRecombine_weak (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {F : Lp FieldVector 2 (μ.restrict U)}
    (h : ∀ W : zeroVoltageJets μ U,inner ℝ W.val.2 F=0) :
    ∀ W : zeroVoltageJets μ U,
      inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (μ.restrict U) F)=0 := by
  intro W
  rw [fieldRecombine_innerLp]
  exact h ⟨voltageJetRecombine μ U M.transpose W.val,
    voltageJetRecombine_H10 μ U M.transpose W.property⟩

theorem voltageJetRecombine_constitution (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (z : VoltageJetSpace μ U)
    (F : Lp FieldVector 2 (μ.restrict U)) (σ : Coord3 → ℝ)
    (h : ∀ᵐ x∂μ.restrict U,F x=σ x • z.2 x) :
    ∀ᵐ x∂μ.restrict U,((fieldRecombine M).compLpL 2 (μ.restrict U) F) x=
      σ x • (voltageJetRecombine μ U M z).2 x := by
  filter_upwards [h,(fieldRecombine M).coeFn_compLpL F,
    (fieldRecombine M).coeFn_compLpL z.2] with x hx hF hz
  change ((fieldRecombine M).compLpL 2 (μ.restrict U) F) x=
    σ x • ((fieldRecombine M).compLpL 2 (μ.restrict U) z.2) x
  rw [hF,hz,hx,map_smul]

theorem scalar_voltage_recombine (μ : Measure Coord3) (U : Set Coord3)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (z : voltageH1Jets μ U) (z₀ : VoltageJetSpace μ U)
    (F G : Lp FieldVector 2 (μ.restrict U)) (σ : Coord3 → ℝ)
    (hz : z.val-z₀∈zeroVoltageJets μ U)
    (hconst : ∀ᵐ x∂μ.restrict U,F x=σ x • z.val.2 x)
    (hcauchy : ∀ W : voltageH1Jets μ U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (hweak : ∀ W : zeroVoltageJets μ U,inner ℝ W.val.2 F=0) :
    ∃ (z' : voltageH1Jets μ U) (F' : Lp FieldVector 2 (μ.restrict U)),
      z'.val=voltageJetRecombine μ U M z.val ∧
      F'=(fieldRecombine M).compLpL 2 (μ.restrict U) F ∧
      z'.val-voltageJetRecombine μ U M z₀∈zeroVoltageJets μ U ∧
      (∀ᵐ x∂μ.restrict U,F' x=σ x • z'.val.2 x) ∧
      (∀ W : voltageH1Jets μ U,inner ℝ W.val.2 F'=
        inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (μ.restrict U) G)) ∧
      (∀ W : zeroVoltageJets μ U,inner ℝ W.val.2 F'=0) := by
  refine ⟨⟨voltageJetRecombine μ U M z.val,voltageJetRecombine_H1 μ U M z.property⟩,
    (fieldRecombine M).compLpL 2 (μ.restrict U) F,rfl,rfl,?_,
    voltageJetRecombine_constitution μ U M z.val F σ hconst,
    voltageJetRecombine_cauchy μ U M hcauchy,voltageJetRecombine_weak μ U M hweak⟩
  rw [←map_sub]
  exact voltageJetRecombine_H10 μ U M hz

lemma voltageGradient_const (d : Fin 2 → ℝ) :
    voltageGradient (fun _ : Coord3 => d)=0 := by
  funext x
  simp only [voltageGradient,fderiv_const_apply,map_zero,Pi.zero_apply]

def voltageConstantJet (μ : Measure Coord3) (U : Set Coord3)
    [IsFiniteMeasure (μ.restrict U)] (d : Fin 2 → ℝ) : VoltageJetSpace μ U :=
  ((memLp_const d : MemLp (fun _ : Coord3 => d) 2 (μ.restrict U)).toLp _,0)

lemma voltageConstantJet_H1 (μ : Measure Coord3) (U : Set Coord3)
    [IsFiniteMeasure (μ.restrict U)] (d : Fin 2 → ℝ) :
    voltageConstantJet μ U d∈voltageH1Jets μ U := by
  apply (Submodule.span ℝ (smoothVoltageJets μ U)).le_topologicalClosure
  apply Submodule.subset_span
  have hg : MemLp (voltageGradient (fun _ : Coord3 => d)) 2 (μ.restrict U) := by
    rw [voltageGradient_const]
    exact MemLp.zero
  refine ⟨(fun _ : Coord3 => d),contDiff_const,memLp_const d,hg,?_⟩
  simp only [voltageConstantJet,voltageGradient_const,MemLp.toLp_zero]

theorem scalar_voltage_affine_recombine (μ : Measure Coord3) (U : Set Coord3)
    [IsFiniteMeasure (μ.restrict U)]
    (M : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ)
    (z : voltageH1Jets μ U) (z₀ : VoltageJetSpace μ U)
    (F G : Lp FieldVector 2 (μ.restrict U)) (σ : Coord3 → ℝ)
    (hz : z.val-z₀∈zeroVoltageJets μ U)
    (hconst : ∀ᵐ x∂μ.restrict U,F x=σ x • z.val.2 x)
    (hcauchy : ∀ W : voltageH1Jets μ U,inner ℝ W.val.2 F=inner ℝ W.val.2 G)
    (hweak : ∀ W : zeroVoltageJets μ U,inner ℝ W.val.2 F=0) :
    ∃ (z' : voltageH1Jets μ U) (F' : Lp FieldVector 2 (μ.restrict U)),
      z'.val=voltageJetRecombine μ U M z.val+voltageConstantJet μ U d ∧
      F'=(fieldRecombine M).compLpL 2 (μ.restrict U) F ∧
      z'.val-(voltageJetRecombine μ U M z₀+voltageConstantJet μ U d)∈zeroVoltageJets μ U ∧
      (∀ᵐ x∂μ.restrict U,F' x=σ x • z'.val.2 x) ∧
      (∀ W : voltageH1Jets μ U,inner ℝ W.val.2 F'=
        inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (μ.restrict U) G)) ∧
      (∀ W : zeroVoltageJets μ U,inner ℝ W.val.2 F'=0) := by
  obtain ⟨zlin,F',he,hF,hzero,hcon,hC,hW⟩ :=
    scalar_voltage_recombine μ U M z z₀ F G σ hz hconst hcauchy hweak
  let z' : voltageH1Jets μ U := ⟨zlin.val+voltageConstantJet μ U d,
    (voltageH1Jets μ U).add_mem zlin.property (voltageConstantJet_H1 μ U d)⟩
  refine ⟨z',F',?_,hF,?_,?_,hC,hW⟩
  · change zlin.val+voltageConstantJet μ U d=_
    rw [he]
  · change zlin.val+voltageConstantJet μ U d-
      (voltageJetRecombine μ U M z₀+voltageConstantJet μ U d)∈_
    simpa only [add_sub_add_right_eq_sub] using hzero
  · have hgrad : z'.val.2=zlin.val.2 := by
      change zlin.val.2+0=_
      rw [add_zero]
    rwa [hgrad]

lemma voltageGradient_affine_recombine (M : Matrix (Fin 2) (Fin 2) ℝ)
    (d : Fin 2 → ℝ) {v : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hv : DifferentiableAt ℝ v x) :
    voltageGradient (fun x => voltageRecombine M (v x)+d) x=
      fieldRecombine M (voltageGradient v x) := by
  change gradientVectorCLM (fderiv ℝ (fun x => voltageRecombine M (v x)+d) x)=_
  rw [fderiv_add_const]
  exact voltageGradient_recombine M hv

lemma voltageJetRecombine_affine_toLp (μ : Measure Coord3) (U : Set Coord3)
    [IsFiniteMeasure (μ.restrict U)]
    (M : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ) {v : Coord3 → Fin 2 → ℝ}
    (hv : Differentiable ℝ v) (hm : MemLp v 2 (μ.restrict U))
    (hg : MemLp (voltageGradient v) 2 (μ.restrict U)) :
    ∃ (hm' : MemLp (fun x => voltageRecombine M (v x)+d) 2 (μ.restrict U))
      (hg' : MemLp (voltageGradient (fun x => voltageRecombine M (v x)+d)) 2 (μ.restrict U)),
      voltageJetRecombine μ U M (hm.toLp _,hg.toLp _)+voltageConstantJet μ U d=
        (hm'.toLp _,hg'.toLp _) := by
  obtain ⟨hl,hgl,he⟩ := voltageJetRecombine_toLp μ U M hv hm hg
  have hm' : MemLp (fun x => voltageRecombine M (v x)+d) 2 (μ.restrict U) :=
    hl.add (memLp_const d)
  have hh : voltageGradient (fun x => voltageRecombine M (v x)+d)=
      voltageGradient (fun x => voltageRecombine M (v x)) := by
    funext x
    unfold voltageGradient
    rw [fderiv_add_const]
  have hg' : MemLp (voltageGradient (fun x => voltageRecombine M (v x)+d)) 2 (μ.restrict U) :=
    hh ▸ hgl
  refine ⟨hm',hg',?_⟩
  rw [he]
  apply Prod.ext
  · change hl.toLp _+(memLp_const d).toLp _=hm'.toLp _
    exact (MemLp.toLp_add hl (memLp_const d)).symm
  · change hgl.toLp _+0=hg'.toLp _
    rw [add_zero]
    apply Lp.ext
    filter_upwards [hgl.coeFn_toLp,hg'.coeFn_toLp] with x h1 h2
    rw [h1,h2,hh]

end ScalarConductivity

end
end

end OAI
