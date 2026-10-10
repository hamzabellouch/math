import OAI.Dynamics.StandardMap.TorusDynamics

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
noncomputable def circleRep (x : Circle) : ℝ := (AddCircle.equivIco 1 0 x).val
lemma circleRep_mem (x : Circle) : circleRep x∈Ico (0:ℝ) 1 := by
  have h:=(AddCircle.equivIco 1 0 x).property
  simpa only [zero_add,circleRep] using h
lemma measurable_circleRep : Measurable circleRep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
@[simp] lemma coe_circleRep (x : Circle) : (circleRep x : Circle)=x := AddCircle.coe_equivIco
@[simp] lemma circleRep_coe (x : ℝ) : circleRep (x:Circle)=Int.fract x := by
  simpa only [div_one,mul_one,circleRep] using AddCircle.coe_equivIco_mk_apply (1:ℝ) x
lemma circleRep_coe_of_mem {x:ℝ} (hx:x∈Ico (0:ℝ) 1) : circleRep (x:Circle)=x := by
  rw [circleRep_coe,Int.fract_eq_self.mpr hx]
noncomputable def torusRep (z:Torus) : CurvePlane := (circleRep z.1,circleRep z.2)
lemma torusRep_mem (z:Torus) : torusRep z∈Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1 := ⟨circleRep_mem _,circleRep_mem _⟩
@[simp] lemma liftProjection_torusRep (z:Torus) : liftProjection (torusRep z)=z := by
  ext <;> simp [liftProjection,torusRep]
lemma torusRep_projection {z:CurvePlane} (hz:z∈Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1) :
    torusRep (liftProjection z)=z := Prod.ext (circleRep_coe_of_mem hz.1) (circleRep_coe_of_mem hz.2)
noncomputable def gridIndex (Q:ℕ) (hQ:0<Q) (x:Circle) : Fin Q :=
  ⟨⌊(Q:ℝ)*circleRep x⌋₊,(Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (circleRep_mem x).1)).mpr
    (by nlinarith [(circleRep_mem x).2,(Nat.cast_pos.mpr hQ : (0:ℝ)<Q)])⟩
lemma measurable_gridIndex (Q:ℕ) (hQ:0<Q) : Measurable (gridIndex Q hQ) := by
  apply measurable_to_countable
  intro y
  have h:Measurable (fun x:Circle=>⌊(Q:ℝ)*circleRep x⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.mul measurable_circleRep)
  convert h (measurableSet_singleton (gridIndex Q hQ y).val) using 1
  ext x
  simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,gridIndex]
noncomputable def gridLabel (Q:ℕ) (hQ:0<Q) (z:Torus) : Fin (Q*Q+1) :=
  (finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)).castSucc
lemma measurable_gridLabel (Q:ℕ) (hQ:0<Q) : Measurable (gridLabel Q hQ) := by
  exact (measurable_of_finite (fun i:Fin Q×Fin Q=>(finProdFinEquiv i).castSucc)).comp
    (((measurable_gridIndex Q hQ).comp measurable_fst).prodMk ((measurable_gridIndex Q hQ).comp measurable_snd))
noncomputable def gridPartition (Q:ℕ) (hQ:0<Q) : FinitePartition (Q*Q) :=
  ⟨gridLabel Q hQ,measurable_gridLabel Q hQ⟩
lemma gridLabel_eq_iff (Q:ℕ) (hQ:0<Q) (z w:Torus) :
    gridLabel Q hQ z=gridLabel Q hQ w ↔
      gridIndex Q hQ z.1=gridIndex Q hQ w.1 ∧ gridIndex Q hQ z.2=gridIndex Q hQ w.2 := by
  constructor
  · intro h
    have hv := congrArg (fun i:Fin (Q*Q+1)=>i.val) h
    have he:finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)=
        finProdFinEquiv (gridIndex Q hQ w.1,gridIndex Q hQ w.2) := Fin.ext hv
    exact Prod.mk.inj (finProdFinEquiv.injective he)
  · rintro ⟨h1,h2⟩; simp only [gridLabel,h1,h2]
lemma gridIndex_bounds (Q:ℕ) (hQ:0<Q) (x:Circle) :
    (gridIndex Q hQ x:ℝ)/(Q:ℝ)≤circleRep x ∧ circleRep x<((gridIndex Q hQ x:ℝ)+1)/(Q:ℝ) := by
  have hq:(0:ℝ)<Q := Nat.cast_pos.mpr hQ
  constructor
  · apply (div_le_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.floor_le (mul_nonneg hq.le (circleRep_mem x).1)
  · apply (lt_div_iff₀ hq).mpr
    simpa only [mul_comm,gridIndex] using Nat.lt_floor_add_one ((Q:ℝ)*circleRep x)
lemma gridIndex_close (Q:ℕ) (hQ:0<Q) {x y:Circle} (h:gridIndex Q hQ x=gridIndex Q hQ y) :
    |circleRep x-circleRep y|≤1/(Q:ℝ) := by
  have hx:=gridIndex_bounds Q hQ x
  have hy:=gridIndex_bounds Q hQ y
  rw [h] at hx
  rw [add_div] at hx hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma gridLabel_close (Q:ℕ) (hQ:0<Q) {z w:Torus} (h:gridLabel Q hQ z=gridLabel Q hQ w) :
    ‖torusRep z-torusRep w‖≤1/(Q:ℝ) := by
  obtain ⟨h1,h2⟩:=(gridLabel_eq_iff Q hQ z w).mp h
  exact max_le (gridIndex_close Q hQ h1) (gridIndex_close Q hQ h2)
lemma projection_wrappedBox (δ:ℝ) (x:CurvePlane) (z:Torus) (h:‖torusRep (liftProjection x)-torusRep z‖≤δ) :
    wrappedBox δ (torusRep z) x := by
  refine ⟨(⌊x.1⌋,⌊x.2⌋),?_⟩
  have he:x-((torusRep z).1+(⌊x.1⌋:ℝ),(torusRep z).2+(⌊x.2⌋:ℝ))=
      torusRep (liftProjection x)-torusRep z := by
    ext <;> simp only [torusRep,liftProjection,circleRep_coe,Prod.fst_sub,Prod.snd_sub,Int.fract] <;> ring
  rw [he]; exact h
lemma unit_ico_cell_integral (g:Torus → ℝ≥0∞) (hg:Measurable g) :
    (∫⁻z in Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1,g (liftProjection z))=∫⁻z,g z ∂area := by
  have h:=unit_cell_integral g hg 0 0
  simp only [zero_add] at h
  change (∫⁻z,g (liftProjection z) ∂(volume.prod volume).restrict (Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1))=_
  rw [← Measure.prod_restrict,restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict]
  exact h
noncomputable def gridInterval (Q:ℕ) (hQ:0<Q) (i:Fin Q) : CurveInterval where
  left := (i:ℝ)/(Q:ℝ)
  right := ((i:ℝ)+1)/(Q:ℝ)
  left_nonneg := by positivity
  ordered := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  right_le := (div_le_one (Nat.cast_pos.mpr hQ)).mpr (by exact_mod_cast i.isLt)
lemma gridInterval_length (Q:ℕ) (hQ:0<Q) (i:Fin Q) : (gridInterval Q hQ i).length=1/(Q:ℝ) := by
  dsimp [gridInterval,CurveInterval.length]; ring
lemma gridInterval_mem (Q:ℕ) (hQ:0<Q) (x:Circle) :
    circleRep x∈Icc (gridInterval Q hQ (gridIndex Q hQ x)).left (gridInterval Q hQ (gridIndex Q hQ x)).right :=
  ⟨(gridIndex_bounds Q hQ x).1,(gridIndex_bounds Q hQ x).2.le⟩
end StandardMapEntropy

end OAI
