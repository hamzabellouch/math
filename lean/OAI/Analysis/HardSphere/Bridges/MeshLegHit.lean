import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.PathDiameter
import OAI.Analysis.HardSphere.Bridges.SegmentSimplify

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def combinedSegmentHit (t : ℝ) (y : Point) (B : Set Point) (s w : Time)
    (c : C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  if (s:ℝ)≤1/2 then jointSegmentHit t y s w c r C
  else Prod.swap ⁻¹' uniformSegmentHit t y s w c r B

lemma combined_segment_sum_bound {m : ℕ} (y : Fin m→Point) (s w : Time)
    (c : C(Time,Point)) {t r C A ε : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hε : 0<ε)
    (hsep : ∀i j,i≠j→ε^2≤ square (y i-y j))
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ)→‖c q-c 0‖≤r*A)
    (hdrift : (s:ℝ)≤1/2 → (w:ℝ)*C≤r)
    (hlatedrift : ((1-(s:ℝ))*(w:ℝ))*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i v,v∈B→‖v-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (combinedSegmentHit t (y i) B s w c r C)) ≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*((ε⁻¹^3+(m:ℝ))+1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))))) := by
  by_cases hs1 : (s:ℝ)≤1/2
  · simp only [combinedSegmentHit,ite_eq_left hs1]
    apply (joint_segment_sum_bound y s w c ht hr hC hA0 hs hs1 hε hsep hA (hdrift hs1) hscale hB).trans
    apply ENNReal.ofReal_le_ofReal
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hc : 0≤hitConstant*r^3*(1+A)^3 := by have := hitConstant_pos; positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  · simp only [combinedSegmentHit,ite_eq_right hs1]
    have hb i : ((volume.restrict B).prod law) (Prod.swap ⁻¹' uniformSegmentHit t (y i) s w c r B) ≤
        ENNReal.ofReal (hitConstant*r^3*(1+A)^3) := by
      rw [←Measure.map_apply measurable_swap (uniformSegmentHit_measurable t (y i) s w c r hBm),Measure.prod_swap]
      exact uniform_segment_simplified (y i) s w c B ht hr hC hA0 (le_of_lt (lt_of_not_ge hs1)) (hBdist i) hA hlatedrift hscale
    apply (Finset.sum_le_sum (fun i _↦hb i)).trans
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    apply ENNReal.ofReal_le_ofReal
    have ha : 0≤hitConstant*r^3*(1+A)^3 := by have := hitConstant_pos; positivity
    have hh : (m:ℝ) ≤ (ε⁻¹^3+m)+1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))) := by
      have hε0 : 0≤ε⁻¹^3 := by positivity
      have hd : 0≤1/(t*(s:ℝ)*Real.sqrt (t*(s:ℝ))) := by positivity
      linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh ha

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

def meshRemainder {n : ℕ} (j : Fin n) : Time :=
  ⟨1/((n:ℝ)-(j:ℝ)),by
    have hj : (1:ℝ)≤(n:ℝ)-(j:ℝ) := by
      have h : (j:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show j.val+1≤n by omega)
      linarith
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hj⟩⟩

lemma meshRemainder_pos {n : ℕ} (j : Fin n) : 0<(meshRemainder j:ℝ) := by
  have hj : (j:ℝ)<(n:ℝ) := by exact_mod_cast j.isLt
  exact one_div_pos.mpr (sub_pos.mpr hj)

lemma meshStart_lt_one {n : ℕ} (j : Fin n) : (meshTime j 0:ℝ)<1 := by
  have hn : (0:ℝ)<n := by exact_mod_cast j.pos
  simpa [meshTime] using (div_lt_one hn).mpr (show (j:ℝ)<n by exact_mod_cast j.isLt)

lemma mesh_suffix_time {n : ℕ} (j : Fin n) (q : Time) :
    suffixTime (meshTime j 0) (prefixTime (meshRemainder j) q)=meshTime j q := by
  apply Subtype.ext
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  have hj : (n:ℝ)-(j:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt j.isLt))
  simp only [suffixTime,prefixTime,ContinuousMap.coe_mk,meshTime,meshRemainder,show ((0:Time):ℝ)=0 from rfl,add_zero]
  field_simp

lemma mesh_remaining {n : ℕ} (j : Fin n) :
    (1-(meshTime j 0:ℝ))*(meshRemainder j:ℝ)=1/(n:ℝ) := by
  have hn : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt j.pos)
  have hj : (n:ℝ)-(j:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt j.isLt))
  dsimp [meshTime,meshRemainder]
  field_simp
  ring

lemma mesh_covers {n : ℕ} (hn : 0<n) (s : Time) : ∃j : Fin n,∃q : Time,meshTime j q=s := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hs : (s:ℝ)=1
  · let j : Fin n := ⟨n-1,by omega⟩
    refine ⟨j,1,Subtype.ext ?_⟩
    simp only [meshTime,j,show ((1:Time):ℝ)=1 from rfl,Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
    rw [sub_add_cancel,div_self hn'.ne',hs]
  · have hs' : (s:ℝ)<1 := lt_of_le_of_ne s.property.2 hs
    let k : ℕ := ⌊(n:ℝ)*(s:ℝ)⌋₊
    have hk0 : (k:ℝ)≤(n:ℝ)*(s:ℝ) := Nat.floor_le (mul_nonneg hn'.le s.property.1)
    have hk1 : (n:ℝ)*(s:ℝ)<(k:ℝ)+1 := Nat.lt_floor_add_one _
    have hk : k<n := by
      have : (k:ℝ)<(n:ℝ) := hk0.trans_lt (by nlinarith)
      exact_mod_cast this
    let q : Time := ⟨(n:ℝ)*(s:ℝ)-(k:ℝ),⟨sub_nonneg.mpr hk0,by linarith⟩⟩
    refine ⟨⟨k,hk⟩,q,Subtype.ext ?_⟩
    dsimp [meshTime,q]
    field_simp
    ring

end HardSphere.Bridge

namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma inverse_heat_antitone {x y : ℝ} (hx : 0<x) (hxy : x≤y) :
    1/(y*Real.sqrt y)≤1/(x*Real.sqrt x) := by
  exact one_div_le_one_div_of_le (mul_pos hx (Real.sqrt_pos.mpr hx))
    (mul_le_mul hxy (Real.sqrt_le_sqrt hxy) (Real.sqrt_nonneg _) (hx.le.trans hxy))

lemma inverse_heat_tail (n k : ℕ) (hk : 0<k) {τ : ℝ} (hτ : 0<τ) :
    (∑j∈Finset.range n,1/(((k+j+1:ℕ):ℝ)*τ*Real.sqrt (((k+j+1:ℕ):ℝ)*τ)))≤
      2/(τ*Real.sqrt ((k:ℝ)*τ)) := by
  have hx : 0<(k:ℝ)*τ := mul_pos (by exact_mod_cast hk) hτ
  convert singular_sum_bound n hx hτ using 1
  congr 1
  funext j
  push_cast
  congr 2 <;> ring_nf

def meshHitUnion {n : ℕ} (I : Finset (Fin n)) (t : ℝ) (y : Point) (B : Set Point)
    (c : Fin n→C(Time,Point)) (r C : ℝ) : Set (Point×Noise) :=
  ⋃j∈I,combinedSegmentHit t y B (meshTime j 0) (meshRemainder j) (c j) r C

lemma mesh_hit_sum {m n : ℕ} (y : Fin m→Point) (I : Finset (Fin n))
    (c : Fin n→C(Time,Point)) (A : Fin n→ℝ) {t r C ε : ℝ}
    (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hε : 0<ε)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (hA0 : ∀j∈I,0≤A j) (hstart : ∀j∈I,0<(meshTime j 0:ℝ))
    (hA : ∀j∈I,∀q : Time,(q:ℝ)≤(meshRemainder j:ℝ) → ‖c j q-c j 0‖≤r*A j)
    (hdrift : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → (meshRemainder j:ℝ)*C≤r)
    (hlate : t/(n:ℝ)≤r^2) (hdrift' : C/(n:ℝ)≤r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i v,v∈B → ‖v-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (meshHitUnion I t (y i) B c r C))≤
      ENNReal.ofReal (hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*(∑j∈I,(1+A j)^3)+
        ∑j∈I,(1+A j)^3/(t*(meshTime j 0:ℝ)*Real.sqrt (t*(meshTime j 0:ℝ))))) := by
  have hb i : ((volume.restrict B).prod law) (meshHitUnion I t (y i) B c r C)≤
      ∑j∈I,((volume.restrict B).prod law) (combinedSegmentHit t (y i) B (meshTime j 0) (meshRemainder j) (c j) r C) := by
    exact measure_biUnion_finset_le I _
  apply (Finset.sum_le_sum (fun i _↦hb i)).trans
  rw [Finset.sum_comm]
  have hj j (hj : j∈I) := combined_segment_sum_bound y (meshTime j 0) (meshRemainder j) (c j)
    ht hr hC (hA0 j hj) (hstart j hj) hε hsep (hA j hj) (hdrift j hj)
    (by rw [mesh_remaining]; simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using hdrift')
    (by rw [mul_assoc,mesh_remaining]; simpa only [div_eq_mul_inv,one_div,one_mul] using hlate)
    hBm hB hBdist
  apply (Finset.sum_le_sum hj).trans_eq
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ by
    have hh := hitConstant_pos; have ha := hA0 j hj; have hs := hstart j hj; positivity)]
  congr 1
  rw [Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HardSphere.Bridge

end

end OAI
