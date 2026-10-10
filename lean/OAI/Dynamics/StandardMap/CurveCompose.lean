import OAI.Dynamics.StandardMap.CurveSubdivision

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
namespace CurveInterval
noncomputable def comp (I J : CurveInterval) : CurveInterval where
  left := I.parameter J.left
  right := I.parameter J.right
  left_nonneg := (I.parameter_mem ⟨J.left_nonneg,J.ordered.trans J.right_le⟩).1
  ordered := by
    have h:0≤I.length*(J.right-J.left) := mul_nonneg I.length_nonneg J.length_nonneg
    rw [← I.parameter_sub] at h
    exact sub_nonneg.mp h
  right_le := (I.parameter_mem ⟨J.left_nonneg.trans J.ordered,J.right_le⟩).2
lemma comp_length (I J : CurveInterval) : (I.comp J).length=I.length*J.length := by
  exact I.parameter_sub J.right J.left
lemma comp_parameter (I J : CurveInterval) (t : ℝ) :
    (I.comp J).parameter t=I.parameter (J.parameter t) := by
  dsimp [parameter,comp,affineParameter]; ring
lemma comp_velocity (I J : CurveInterval) (v : ℝ → CurvePlane) (t : ℝ) :
    (I.comp J).velocity v t=J.velocity (I.velocity v) t := by
  rw [velocity,comp_length,comp_parameter,velocity,velocity,smul_smul,mul_comm]
lemma comp_mem (I J : CurveInterval) {t : ℝ} (ht : t∈Icc J.left J.right) :
    I.parameter t∈Icc (I.comp J).left (I.comp J).right := by
  change I.parameter J.left≤I.parameter t ∧ I.parameter t≤I.parameter J.right
  constructor
  · apply sub_nonneg.mp
    rw [I.parameter_sub]
    exact mul_nonneg I.length_nonneg (sub_nonneg.mpr ht.1)
  · apply sub_nonneg.mp
    rw [I.parameter_sub]
    exact mul_nonneg I.length_nonneg (sub_nonneg.mpr ht.2)
end CurveInterval
lemma curve_wrap_integer (x y c δ : ℝ) (hxy : |x-y|≤1) (hδ : δ≤1)
    (m : ℤ) (hm : |y-(c+m)|≤δ) :
    ∃i:Fin 7,m=⌊x-c⌋+(i:ℤ)-3 := by
  have h1:=Int.floor_le (x-c)
  have h2:=Int.lt_floor_add_one (x-c)
  have hp:|x-c-(m:ℝ)|≤2 := by
    have h:=abs_add_le (x-y) (y-(c+m))
    have he:(x-y)+(y-(c+m))=x-c-m := by ring
    rw [he] at h
    linarith
  have hlo:⌊x-c⌋-3≤ m := by
    have h:((⌊x-c⌋:ℤ):ℝ)-3≤ m := by linarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
    exact_mod_cast h
  have hhi:m≤⌊x-c⌋+3 := by
    have h:(m:ℝ)≤⌊x-c⌋+3 := by linarith [(abs_le.mp hp).1,(abs_le.mp hp).2]
    exact_mod_cast h
  let q:ℤ:=m-⌊x-c⌋+3
  have hq0:0≤q := by dsimp [q]; omega
  have hq7:q<7 := by dsimp [q]; omega
  refine ⟨⟨q.toNat,by omega⟩,?_⟩
  change m=⌊x-c⌋+(q.toNat:ℤ)-3
  rw [Int.toNat_of_nonneg hq0]
  dsimp [q]; ring
noncomputable def wrappedCurveCenter (c x : CurvePlane) (i : Fin 7×Fin 7) : CurvePlane :=
  (c.1+(⌊x.1-c.1⌋+(i.1:ℤ)-3:ℤ), c.2+(⌊x.2-c.2⌋+(i.2:ℤ)-3:ℤ))
def wrappedBox (δ : ℝ) (c x : CurvePlane) : Prop :=
  ∃m:ℤ×ℤ,‖x-(c.1+(m.1:ℝ),c.2+(m.2:ℝ))‖≤δ
lemma wrappedBox_finite_cover (δ : ℝ) (hδ : δ≤1) (c x y : CurvePlane)
    (hxy : ‖x-y‖≤1) (hy : wrappedBox δ c y) :
    ∃i:Fin 7×Fin 7,‖y-wrappedCurveCenter c x i‖≤δ := by
  obtain ⟨m,hm⟩:=hy
  obtain ⟨i,hi⟩:=curve_wrap_integer x.1 y.1 c.1 δ
    ((norm_fst_le (x-y)).trans hxy) hδ m.1 ((norm_fst_le _).trans hm)
  obtain ⟨j,hj⟩:=curve_wrap_integer x.2 y.2 c.2 δ
    ((norm_snd_le (x-y)).trans hxy) hδ m.2 ((norm_snd_le _).trans hm)
  refine ⟨(i,j),?_⟩
  simpa only [wrappedCurveCenter,← hi,← hj] using hm
end StandardMapEntropy

end OAI
