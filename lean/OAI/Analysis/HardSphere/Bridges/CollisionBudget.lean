import Mathlib
import OAI.Analysis.HardSphere.Bridges.MeshCollision
import OAI.Analysis.HardSphere.Bridges.TrialCutoff

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma mesh_collision_budget {m n k : ℕ} {t r ε Creg R h : ℝ}
    (hn : 0<n) (ht : 0<t) (hr : 0<r) (hε : 0<ε) (hCreg : 0≤Creg) (hR : 0≤R) (hh : 0<h)
    (hnscale : (n:ℝ)*r^2≤2*t) (hk : h/4≤(k:ℝ)*(t/(n:ℝ))) :
    hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*(2*Creg*(n:ℝ))+
      2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ))))) ≤
    hitConstant*(4*Creg*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt h) := by
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hs : 0<Real.sqrt h := Real.sqrt_pos.mpr hh
  have hk' : 0<(k:ℝ)*(t/(n:ℝ)) := lt_of_lt_of_le (by positivity) hk
  have hv : Real.sqrt h/2≤Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := by
    have h := Real.sqrt_le_sqrt hk
    rw [Real.sqrt_div hh.le] at h
    rw [show Real.sqrt 4=2 by norm_num] at h
    exact h
  have hroot : Real.sqrt h≤2*Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := by linarith
  have hmain : r^3*((ε⁻¹^3+(m:ℝ))*(2*Creg*(n:ℝ)))≤4*Creg*t*r*(ε⁻¹^3+(m:ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hnscale (show 0≤2*Creg*r*(ε⁻¹^3+(m:ℝ)) by positivity)
    nlinarith
  have htail : r^3*(2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))≤8*r*(1+R)^3/Real.sqrt h := by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos (div_pos ht hn') (Real.sqrt_pos.mpr hk')) hs).mpr
    have hb : (n:ℝ)*r^2*Real.sqrt h ≤ 4*t*Real.sqrt ((k:ℝ)*(t/(n:ℝ))) := calc
      _ ≤ (n:ℝ)*r^2*(2*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ ≤ 2*t*(2*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) :=
        mul_le_mul_of_nonneg_right hnscale (by positivity)
      _ = _ := by ring
    have hmul := mul_le_mul_of_nonneg_right hb (show 0≤2*r*(1+R)^3 by positivity)
    apply (mul_le_mul_iff_right₀ hn').mp
    convert hmul using 1 <;> field_simp
    ring

  have hc := hitConstant_pos.le
  nlinarith

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

def torusLegHit {L : Length} (t : ℝ) (y v : Point) (B : Set Point) (ω : ConfigurationPath 1 L)
    (r C h : ℝ) : Set (Point×Noise) :=
  {p | p.1∈B ∧ (∀s : Time,‖leg t y p.1 p.2 s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y p.1 p.2 s)) (projectPoint L v)≤10) ∧
    (∀s : Time,‖leg t y p.1 p.2 s-p.1‖≤ C) ∧
    ∃s : Time,h≤(s:ℝ) ∧ torusDistance L (projectPoint L (leg t y p.1 p.2 s)) (ω s 0)≤ r}

lemma torusLegHit_subset {L : Length} {n : ℕ} (hn : 0< n) (I : Finset (Fin n))
    (t : ℝ) (y v : Point) (B : Set Point) (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (hζ : IsPathLift ω ζ) {r C h : ℝ} (hL : 50< L.val) (hr : r≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤1)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I) :
    torusLegHit t y v B ω r C h⊆meshHitUnion I t y B (meshLocalLift ω ζ v) r C := by
  rintro ⟨u,β⟩ ⟨hu,hconf,hconf',s,hs,hit⟩
  obtain ⟨j,q,hq⟩ := mesh_covers hn s
  have hj : j∈I := hI j q (by simpa only [hq] using hs)
  have hh := (mesh_torus_hit_local hζ v (leg t y u β (meshTime j q)) j q hL
    (le_refl 1) (hdiam j hj) (hconf (meshTime j q)).1 (hconf (meshTime j q)).2 hr
    (by simpa only [hq] using hit)).2
  change (u,β)∈⋃j∈I,combinedSegmentHit t y B (meshTime j 0) (meshRemainder j) (meshLocalLift ω ζ v j) r C
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,?_⟩⟩
  by_cases hearly : (meshTime j 0:ℝ)≤1/2
  · simp only [combinedSegmentHit,ite_eq_left hearly,jointSegmentHit,mem_ofPred_eq,segmentHit]
    exact ⟨hconf' _,prefixTime (meshRemainder j) q,prefixTime_le _ _,by simpa only [mesh_suffix_time] using hh⟩
  · simp only [combinedSegmentHit,ite_eq_right hearly,mem_preimage,uniformSegmentHit,mem_ofPred_eq,Prod.swap_prod_mk]
    exact ⟨hu,prefixTime (meshRemainder j) q,prefixTime_le _ _,by simpa only [mesh_suffix_time] using hh⟩

lemma torusLegHit_sum {L : Length} {m n k : ℕ} (hn : 0< n) (hk : 0< k)
    (y : Fin m→Point) (v : Point) (I : Finset (Fin n)) (ω : ConfigurationPath 1 L) (A : Fin n→ℝ)
    {t r C ε h R J : ℝ}
    (hL : 50< L.val) (ht : 0< t) (hr : 0< r) (hr1 : r≤1) (hC : 0≤ C) (hε : 0<ε) (hR : 0≤ R)
    (hsep : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I)
    (hlow : ∀j∈I,k< j.val)
    (hA0 : ∀j∈I,0≤ A j) (hAmax : ∀j∈I,A j≤ R) (hAsum : (∑j∈I,(1+A j)^3)≤ J)
    (hsmall : ∀j∈I,r*A j≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤ r*A j)
    (hdrift : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → (meshRemainder j:ℝ)*C≤ r)
    (hlate : t/(n:ℝ)≤ r^2) (hdrift' : C/(n:ℝ)≤ r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i u,u∈B → ‖u-y i‖≤ C) :
    (∑i,((volume.restrict B).prod law) (torusLegHit t (y i) v B ω r C h))≤
      ENNReal.ofReal (hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*J+
        2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))) := by
  obtain ⟨ζ,hζ⟩ := exists_pathLift ω
  have hstart j (hj : j∈I) : 0<(meshTime j 0:ℝ) := by
    change 0<((j:ℝ)+0)/(n:ℝ)
    exact div_pos (by exact_mod_cast (lt_trans hk (hlow j hj))) (by exact_mod_cast hn)
  apply (Finset.sum_le_sum (fun i _ ↦ measure_mono (torusLegHit_subset hn I t (y i) v B ω ζ hζ hL hr1
    (fun j hj ↦ (hdiam j hj).trans (hsmall j hj)) hI))).trans
  apply (mesh_hit_sum y I (meshLocalLift ω ζ v) A ht hr hC hε hsep hA0 hstart
    (fun j hj q hq ↦ meshLocalLift_increment hζ v j (by linarith [hsmall j hj]) (hdiam j hj) q hq)
    hdrift hlate hdrift' hBm hB hBdist).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hitConstant_pos.le (pow_nonneg hr.le _))
  exact add_le_add (mul_le_mul_of_nonneg_left hAsum (by positivity))
    (mesh_tail_bound I A hk ht hR hlow hAmax hA0)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def meshCount (t r : ℝ) : ℕ := ⌈t/r^2⌉₊
lemma meshCount_pos {t r : ℝ} (ht : 0< t) (hr : 0< r) : 0< meshCount t r := by
  exact Nat.ceil_pos.mpr (div_pos ht (sq_pos_of_pos hr))
lemma meshCount_lower {t r : ℝ} (ht : 0< t) (hr : 0< r) :
    t/(meshCount t r:ℝ)≤ r^2 := by
  have hn : (0:ℝ)< meshCount t r := by exact_mod_cast meshCount_pos ht hr
  apply (div_le_iff₀ hn).mpr
  have h := Nat.le_ceil (t/r^2)
  have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp h
  simpa only [meshCount,mul_comm] using hh
lemma meshCount_upper {t r : ℝ} (ht : 0< t) (hr : 0< r) (hsmall : r^2≤ t) :
    (meshCount t r:ℝ)*r^2≤2*t := by
  have h := (Nat.ceil_lt_add_one (div_nonneg ht.le (sq_nonneg r)))
  have hh := mul_lt_mul_of_pos_right h (sq_pos_of_pos hr)
  dsimp [meshCount]
  have he : (t/r^2+1)*r^2=t+r^2 := by field_simp
  rw [he] at hh
  linarith

lemma mesh_endpoint_index {n : ℕ} (j : Fin n) (q : Time) {t h : ℝ}
    (ht : 0< t) (hh : 2*(t/(n:ℝ))≤ h) (hs : h/t≤(meshTime j q:ℝ)) :
    h/(2*t)≤(meshTime j 0:ℝ) := by
  have hn : (0:ℝ)< n := by exact_mod_cast j.pos
  have hs' : h*(n:ℝ)≤ t*((j:ℝ)+(q:ℝ)) := by
    change h/t≤((j:ℝ)+(q:ℝ))/(n:ℝ) at hs
    simpa only [mul_comm t] using (div_le_div_iff₀ ht hn).mp hs
  have hh' : 2*t≤ h*(n:ℝ) := by
    have := (div_le_iff₀ hn).mp (show 2*t/(n:ℝ)≤ h by simpa [mul_div_assoc] using hh)
    linarith
  change h/(2*t)≤((j:ℝ)+0)/(n:ℝ)
  rw [add_zero]
  apply (div_le_div_iff₀ (by positivity : 0<2*t) hn).mpr
  have hq := q.property.2
  nlinarith

def endpointIndex (n : ℕ) (t h : ℝ) : ℕ := ⌊(n:ℝ)*h/(4*t)⌋₊
lemma endpointIndex_pos {n : ℕ} {t h : ℝ} (ht : 0< t)
    (hlarge : 8*t≤(n:ℝ)*h) : 0< endpointIndex n t h := by
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ (by positivity : 0<4*t)).mpr
  linarith
lemma endpointIndex_gap {n : ℕ} (j : Fin n) {t h : ℝ} (ht : 0< t) (hh : 0< h)
    (hj : h/(2*t)≤(meshTime j 0:ℝ)) : endpointIndex n t h< j.val := by
  have hn : (0:ℝ)< n := by exact_mod_cast j.pos
  have hk := Nat.floor_le (show 0≤(n:ℝ)*h/(4*t) by positivity)
  have hj' : h*(n:ℝ)≤(j:ℝ)*(2*t) := by
    change h/(2*t)≤((j:ℝ)+0)/(n:ℝ) at hj
    rw [add_zero] at hj
    exact (div_le_div_iff₀ (by positivity : 0<2*t) hn).mp hj
  have hc : (endpointIndex n t h:ℝ)<(j:ℝ) := by
    apply lt_of_le_of_lt hk
    apply (div_lt_iff₀ (by positivity : 0<4*t)).mpr
    nlinarith
  exact_mod_cast hc
lemma endpointIndex_scale {n : ℕ} (hn : 0< n) {t h : ℝ} (ht : 0< t)
    (hlarge : 8*t≤(n:ℝ)*h) : h/8≤(endpointIndex n t h:ℝ)*(t/(n:ℝ)) := by
  have hn' : (0:ℝ)< n := by exact_mod_cast hn
  have hk : (n:ℝ)*h/(4*t)<(endpointIndex n t h:ℝ)+1 := Nat.lt_floor_add_one _
  have hk' := (div_lt_iff₀ (by positivity : 0<4*t)).mp hk
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hn').mpr
  change h/8*(n:ℝ)≤(endpointIndex n t h:ℝ)*t
  nlinarith

end HardSphere.Bridge

end
end

end

end OAI
