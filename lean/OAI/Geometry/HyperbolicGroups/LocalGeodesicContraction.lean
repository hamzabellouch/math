import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicCover

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] {o : X}

def initial (s : I) (a : LocalGeodesic o) : LocalGeodesic o :=
  ofReal (a.localSegment.reparam (s:=0) (t:=s) (by norm_num) s.property)
    (by simpa using a.start)

@[simp] lemma prefix_apply (s t : I) (a : LocalGeodesic o) :
    initial s a t = a (t*s) := by
  change extend a.val ((1-(t:ℝ))*0+(t:ℝ)*s)=a (t*s)
  simp only [mul_zero,zero_add]
  exact extend_coe a.val (t*s)
@[simp] lemma prefix_zero (a : LocalGeodesic o) : initial 0 a=constant o := by
  ext t
  simp [a.start]
@[simp] lemma prefix_one (a : LocalGeodesic o) : initial 1 a=a := by
  ext t
  simp
@[simp] lemma endpoint_prefix (s : I) (a : LocalGeodesic o) : endpoint (initial s a)=a s := by
  simp [endpoint]
@[simp] lemma length_prefix (s : I) (a : LocalGeodesic o) : (initial s a).length=(s:ℝ)*a.length := by
  rw [initial,ofReal_length]
  simp [abs_of_nonneg s.property.1]

lemma prefix_continuous : Continuous (fun q : I × LocalGeodesic o => initial q.1 q.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun data : (I × LocalGeodesic o) × I => initial data.1.1 data.1.2 data.2)
  simp only [prefix_apply]
  exact continuous_eval.comp ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk (continuous_snd.mul (continuous_fst.comp continuous_fst)))

def contraction : (ContinuousMap.const (LocalGeodesic o) (constant o)).Homotopy (ContinuousMap.id _) :=
  ⟨⟨fun q => initial q.1 q.2,prefix_continuous⟩,prefix_zero,prefix_one⟩

instance : ContractibleSpace (LocalGeodesic o) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨constant o,⟨contraction.symm⟩⟩

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
