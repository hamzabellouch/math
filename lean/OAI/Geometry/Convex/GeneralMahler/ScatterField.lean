import OAI.Geometry.Convex.GeneralMahler.Scatter

namespace OAI
/-! Two projection maps implementing Scatter. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Metric Real
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma s_poly : PolyBound q.shift := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨C,hC,h⟩ := layers_growth m hk.one_le
  refine ⟨C,1,hC,fun z=>?_⟩
  simpa using h q hk z
lemma loc_ends :
    ∃ M≥(1:ℝ), (∀ z x, M*(1+‖x‖)<z → op q.S x + q.shift z ∈ q.C) ∧
      (∀ z x, M*(1+‖x‖)< -z → -(op q.S x+q.shift z) ∈ q.D) := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  obtain ⟨a,ha,h⟩ := positive_cutoff m hk.one_le
  obtain ⟨b,hb,h'⟩ := negative_cutoff m hk.one_le
  refine ⟨max a b, ha.trans (le_max_left ..),fun z x hx=>?_,fun z x hx=>?_⟩
  · rw [← Z_def]; apply interior_subset
    exact h q hk z x (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left ..)
      (by positivity)) hx)
  rw [← Z_def]; apply interior_subset
  have hi := h' q hk (-z) x (lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) hx)
  rwa [neg_neg] at hi

omit [NeZero m] in
lemma xt_d :
    ∀ᵐ x:Rn m,∀ᵐ z:ℝ,HasFDerivAt (q.XT z) ((op (q.Pmat z x)).comp (op q.S)) x := by
  let F (p:ℝ×Rn m) := affineN q.root (q.shift p.1) p.2
  let S := {x| DifferentiableAt ℝ (coneProj q.C) x}
  have hm : MeasurableSet (F⁻¹' S) :=
    (measurableSet_of_differentiableAt ..).preimage
      (((q.root.continuous.comp continuous_snd).add
        (q.shift_cd.continuous.comp continuous_fst)).measurable)
  have ha : ∀ᵐ x:Rn m,x∈S := (coneProj_lip q.C).ae_differentiableAt
  have he : ∀ᵐ z:ℝ,∀ᵐ x ∂normal m,(z,x)∈F⁻¹' S :=
    ae_of_all _ fun z=> (tendsto_ae_affineN q.root (q.shift z)).eventually ha
  have hi : ∀ᵐ x ∂normal m, ∀ᵐ z:ℝ,(z,x)∈F⁻¹' S := by
    rw [← ae_prod_mem_iff_ae_ae_mem] at he
    · have ha : ∀ᵐ p∂(normal m).prod (volume : Measure ℝ), p.swap∈F⁻¹' S :=
        measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually he
      exact ae_ae_of_ae_prod ha
    exact hm
  apply ac_normal.ae_le
  filter_upwards [hi] with x hx
  filter_upwards [hx] with z hz
  change DifferentiableAt ℝ (coneProj q.C) (affineN q.root (q.shift z) x) at hz
  have hu := hz.hasFDerivAt.comp x
    (q.root.hasFDerivAt.add_const (q.shift z))
  simp only [XT,Pmat,projJac_op]
  rw [← q.matrix_eq]
  exact hu
omit [NeZero m] in
lemma S_inj : Function.Injective (op q.S) := by rw [← q.matrix_eq]; apply q.root.injective
def primalMap : Scatter m where
  toEdge := q.edge
  cone := q.C
  B := q.S
  inj := q.S_inj
  d := q.shift
  dp := q.s_poly
  dc := q.shift_cd.continuous
  M := q.loc_ends.choose
  hm := q.loc_ends.choose_spec.1
  in_cone := q.loc_ends.choose_spec.2.1
  opp := q.loc_ends.choose_spec.2.2
  diff := by
    have h (z:ℝ) : (fun x=>coneProj q.C (op q.S x+q.shift z))=q.XT z := by
      ext x; rw [← q.Z_def]; rfl
    simp_rw [h]; exact q.xt_d

def dualMap : Scatter m where
  toEdge := q.edge.ref
  cone := q.D
  B := -q.S
  inj := by
    rw [_root_.map_neg]
    intro x y h
    exact q.S_inj (neg_injective h)
  d := fun z=> - q.shift (-z)
  dp := (q.s_poly.comp PolyBound.id.neg).neg
  dc := (q.shift_cd.continuous.comp continuous_neg).neg
  M := q.loc_ends.choose
  hm := q.loc_ends.choose_spec.1
  in_cone := by
    intro z x hz
    rw [_root_.map_neg]
    convert q.loc_ends.choose_spec.2.2 (-z) x (by simpa using hz)
    simp [add_comm]
  opp := by
    intro z x hz
    rw [show posDual q.D = q.C from ProperCone.innerDual_innerDual _,_root_.map_neg]
    convert q.loc_ends.choose_spec.2.1 (-z) x hz
    simp [add_comm]
  diff := by
    filter_upwards [q.xt_d] with x hx
    have hh := (measurePreserving_neg volume).quasiMeasurePreserving.tendsto_ae.eventually hx
    filter_upwards [hh] with z hz
    change HasFDerivAt (q.XT (-z)) ((op (q.Pmat (-z) x)).comp (op q.S)) x at hz
    have hf := hz.sub ((op q.S).hasFDerivAt.add_const (q.shift (-z)))
    have he : (fun y=> coneProj q.D (op (-q.S) y+ - q.shift (-z))) =
        q.XT (-z) - (fun y=>op q.S y+q.shift (-z)) := by
      funext y
      change coneProj q.D (op (-q.S) y + -_) = q.XT _ y - (op q.S y+q.shift (-z))
      rw [_root_.map_neg,_root_.neg_apply]
      rw [show - (op q.S y) + - q.shift (-z) = -(op q.S y + q.shift (-z)) by abel]
      rw [proj_moreau]
      rw [← q.Z_def]; rfl
    have hv : (op (1-q.Pmat (-z) x)).comp (op (-q.S)) =
        (op (q.Pmat (-z) x)).comp (op q.S) - op q.S := by
      change op (1-q.Pmat (-z) x)*op (-q.S)=op (q.Pmat (-z) x)*op q.S-op q.S
      have hi : (1-q.Pmat (-z) x)*(-q.S)= (q.Pmat (-z) x)*q.S-q.S := by noncomm_ring
      calc
        _ = op ((1-q.Pmat (-z) x)* (-q.S)) := Eq.symm (_root_.map_mul ..)
        _ = _ := by rw [hi,_root_.map_sub,_root_.map_mul]
    change HasFDerivAt (fun y=>coneProj q.D (op (-q.S) y+ - q.shift (-z)))
      ((op (1-q.Pmat (-z) x)).comp (op (-q.S))) x
    rw [he,hv]; exact hf

lemma X_sc (z:ℝ) : q.primalMap.y z=q.XT z := by
  unfold Scatter.y primalMap
  ext x; simp_rw [← q.Z_def]; rfl
lemma Y_sc (z:ℝ) : q.dualMap.y z=q.YT (-z) := by
  ext x
  unfold Scatter.y dualMap YT
  dsimp
  rw [_root_.map_neg]
  simp [q.Z_def,add_comm]
end ProjField
end GeneralMahler

end

end OAI
