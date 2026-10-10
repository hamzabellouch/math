import Mathlib
import OAI.Analysis.HardSphere.Geometry.BoxWeight

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
namespace Rescaling
attribute [local instance] Classical.propDecidable

def circle (L J : Length) : AddCircle L.val ≃+ AddCircle J.val :=
  AddCircle.equivAddCircle L.val J.val L.property.ne' J.property.ne'
def torus (L J : Length) : Torus L ≃+ Torus J := AddEquiv.piCongrRight fun _ ↦ circle L J
def config (N : ℕ) (L J : Length) : Configuration N L ≃+ Configuration N J :=
  AddEquiv.piCongrRight fun _ ↦ torus L J
def configHomeo (N : ℕ) (L J : Length) : Configuration N L ≃ₜ Configuration N J :=
  Homeomorph.piCongrRight fun _ ↦ Homeomorph.piCongrRight fun _ ↦
    AddCircle.homeomorphAddCircle L.val J.val L.property.ne' J.property.ne'

lemma configHomeo_toFun (N : ℕ) (L J : Length) : (configHomeo N L J : Configuration N L → Configuration N J)=config N L J := rfl
lemma config_continuous (N : ℕ) (L J : Length) : Continuous (config N L J) := (configHomeo N L J).continuous

lemma circle_project (L J : Length) (x : ℝ) : circle L J (x : AddCircle L.val)=((J.val/L.val*x : ℝ) : AddCircle J.val) := by
  simp only [circle,AddCircle.equivAddCircle_apply_mk]
  congr 1
  ring
lemma config_project (N : ℕ) (L J : Length) (X : LiftedConfiguration N) :
    config N L J (project N L X)=project N J ((J.val/L.val) • X) := by
  ext i j
  exact circle_project L J _

lemma circle_representative (L J : Length) (x : AddCircle L.val) :
    (AddCircle.equivIco J.val 0 (circle L J x)).val=
      J.val/L.val*(AddCircle.equivIco L.val 0 x).val := by
  have hLp := L.property
  have hJp := J.property
  let y := (AddCircle.equivIco L.val 0 x).val
  have hy : y∈Ico 0 L.val := by simpa only [zero_add] using (AddCircle.equivIco L.val 0 x).property
  have he : x=(y : AddCircle L.val) := AddCircle.coe_equivIco.symm
  conv_lhs => rw [he,circle_project]
  have hm : J.val/L.val*y∈Ico 0 (0+J.val) := by
    constructor
    · exact mul_nonneg (by positivity) hy.1
    · have hh := mul_lt_mul_of_pos_left hy.2 (by positivity : 0<J.val/L.val)
      have hn : J.val/L.val*L.val=J.val := by field_simp [hLp.ne']
      simpa only [hn,zero_add] using hh
  rw [AddCircle.equivIco_coe_eq hm]
lemma config_representative (N : ℕ) (L J : Length) (X : Configuration N L) :
    representative N J (config N L J X)=(J.val/L.val) • representative N L X := by
  ext i j
  exact circle_representative L J _

lemma circle_distance (L J : Length) (x y : AddCircle L.val) :
    dist (circle L J x) (circle L J y)=J.val/L.val*dist x y := by
  have hLp := L.property
  have hJp := J.property
  rw [dist_eq_norm,←map_sub,dist_eq_norm]
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (x-y)
  rw [←hz,circle_project]
  have hj : J.val=J.val/L.val*L.val := by field_simp [hLp.ne']
  have hh := AddCircle.norm_coe_mul L.val z (J.val/L.val)
  rw [←hj,abs_of_pos (by positivity : 0<J.val/L.val)] at hh
  exact hh
lemma torus_distance (L J : Length) (x y : Torus L) :
    torusDistance J (torus L J x) (torus L J y)=(J.val/L.val)*torusDistance L x y := by
  have hLp := L.property
  have hJp := J.property
  unfold torusDistance
  simp only [torus,AddEquiv.piCongrRight_apply,circle_distance,mul_pow,←Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
lemma config_allowed (N : ℕ) (L J : Length) (a : ℝ) (X : Configuration N L) :
    config N L J X∈allowed N J ((J.val/L.val)*a) ↔ X∈allowed N L a := by
  have hLp := L.property
  have hJp := J.property
  simp only [allowed,mem_ofPred_eq]
  have h : 0<J.val/L.val := by positivity
  simp only [config,AddEquiv.piCongrRight_apply,torus_distance,mul_lt_mul_iff_right₀ h]

lemma volume_config (N : ℕ) (L : Length) :
    (volume : Measure (Configuration N L)) univ=ENNReal.ofReal ((L.val^3)^N) := by
  have hLp := L.property
  rw [show (volume : Measure (Configuration N L))=Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))) from rfl,Measure.pi_univ]
  simp only [BathSlice.volume_torus,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ←ENNReal.ofReal_pow (by positivity : 0≤L.val^3)]

def jacobian (N : ℕ) (L J : Length) : ℝ := (L.val^3/J.val^3)^N
lemma jacobian_pos (N : ℕ) (L J : Length) : 0<jacobian N L J := by
  have hLp := L.property
  have hJp := J.property
  unfold jacobian; positivity
instance config_haar (N : ℕ) (L : Length) : Measure.IsAddHaarMeasure (volume : Measure (Configuration N L)) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (Torus L)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

lemma config_preserving (N : ℕ) (L J : Length) :
    MeasurePreserving (config N L J) volume (ENNReal.ofReal (jacobian N L J) • volume) := by
  have hLp := L.property
  have hJp := J.property
  let : NeZero (ENNReal.ofReal (jacobian N L J)) := ⟨(ENNReal.ofReal_pos.mpr (jacobian_pos N L J)).ne'⟩
  let : Measure.IsAddHaarMeasure (ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) :=
    Measure.IsAddHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (jacobian_pos N L J)).ne' ENNReal.ofReal_ne_top
  apply AddMonoidHom.measurePreserving (μ:=(volume : Measure (Configuration N L)))
    (ν:= ENNReal.ofReal (jacobian N L J) • (volume : Measure (Configuration N J))) (f:=(config N L J).toAddMonoidHom) (config_continuous N L J) (config N L J).surjective
  rw [volume_config,Measure.smul_apply,smul_eq_mul,volume_config,
    ←ENNReal.ofReal_mul (jacobian_pos N L J).le]
  congr 1
  unfold jacobian
  rw [div_pow]
  field_simp [hJp.ne']

end Rescaling
end HardSphere
end
end

end OAI
