import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicContraction
import OAI.Geometry.HyperbolicGroups.LocalGeodesicRebase
import OAI.Geometry.HyperbolicGroups.LocalGeodesicLength

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

omit [CompactSpace X] in
@[simp] lemma constant_length (x : X) : (constant x).length=0 := ofReal_length _ _

omit [CompactSpace X] in
lemma eq_constant_of_length_zero {a : LocalGeodesic o} (ha : a.length=0) : a=constant o := by
  ext t
  have hh:=a.localSegment.dist_le t.property (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  simp only [extend_coe,extend_zero,a.start,ha,mul_zero] at hh
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

def joining (a b : LocalGeodesic o) : C(I,LocalGeodesic o) :=
  ⟨fun t => rebase hr hc g a (initial t ((rebase hr hc g a).symm b)),
    (rebase hr hc g a).continuous.comp (prefix_continuous.comp (continuous_id.prodMk continuous_const))⟩

@[simp] lemma joining_zero (a b : LocalGeodesic o) : joining hr hc g a b 0=a := by
  simp [joining]
@[simp] lemma joining_one (a b : LocalGeodesic o) : joining hr hc g a b 1=b := by
  simp [joining]
@[simp] lemma joining_endpoint (a b : LocalGeodesic o) (t : I) :
    endpoint (joining hr hc g a b t)=((rebase hr hc g a).symm b) t := by
  simp [joining]

def intrinsicDist (a b : LocalGeodesic o) : ℝ := ((rebase hr hc g a).symm b).length
lemma intrinsicDist_nonneg (a b : LocalGeodesic o) : 0≤ intrinsicDist hr hc g a b := length_nonneg _
@[simp] lemma intrinsicDist_self (a : LocalGeodesic o) : intrinsicDist hr hc g a a=0 := by simp [intrinsicDist]
lemma intrinsicDist_eq_zero {a b : LocalGeodesic o} (h : intrinsicDist hr hc g a b=0) : a=b := by
  have hh := eq_constant_of_length_zero h
  have hh' := congrArg (rebase hr hc g a) hh
  simpa using hh'.symm

lemma intrinsicDist_variation (x a b : LocalGeodesic o) :
    |intrinsicDist hr hc g x a-intrinsicDist hr hc g x b|≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let ρ : C(I,LocalGeodesic (endpoint x)) := (⟨(rebase hr hc g x).symm,(rebase hr hc g x).symm.continuous⟩ : C(_, _)).comp (joining hr hc g a b)
  have hh := length_variation hr hc g c.localSegment ρ
    (fun t => by simp [ρ,c]) 0 1
  simpa [ρ,intrinsicDist,c] using hh

lemma intrinsicDist_comm (a b : LocalGeodesic o) : intrinsicDist hr hc g a b=intrinsicDist hr hc g b a := by
  apply le_antisymm
  · have hh := intrinsicDist_variation hr hc g a b a
    simpa [abs_of_nonneg (intrinsicDist_nonneg hr hc g a b)] using hh
  · have hh := intrinsicDist_variation hr hc g b a b
    simpa [abs_of_nonneg (intrinsicDist_nonneg hr hc g b a)] using hh
lemma intrinsicDist_triangle (a b c : LocalGeodesic o) :
    intrinsicDist hr hc g a c≤ intrinsicDist hr hc g a b+intrinsicDist hr hc g b c := by
  have hh := intrinsicDist_variation hr hc g a c b
  rw [intrinsicDist_comm hr hc g c b] at hh
  have hle := (abs_le.mp hh).2
  linarith

lemma ordinary_dist_le_intrinsic (a b : LocalGeodesic o) : dist a b≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let ρ := joining hr hc g a b
  obtain ⟨ε,hε,he⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ρ.continuous) (r/10) (by positivity)
  have hh := @local_dist_le_global (LocalGeodesic o) _ (fun u => ρ (projIcc 0 1 zero_le_one u)) c.length ε hε
    (by intro u hu v hv huv
        rw [projIcc_of_mem zero_le_one hu,projIcc_of_mem zero_le_one hv]
        rw [←close_isometry hr hc g (he (by simpa [Subtype.dist_eq,Real.dist_eq] using huv))]
        simp only [ρ,joining_endpoint]
        have hh:=c.localSegment.dist_le hu hv
        simpa only [extend_mem _ hu,extend_mem _ hv] using hh)
    (s:=0) (t:=1) (by norm_num) (by norm_num)
  simpa [ρ,c,intrinsicDist] using hh

end HyperbolicObstruction.LocalGeodesic
end
end

section

end

end OAI
