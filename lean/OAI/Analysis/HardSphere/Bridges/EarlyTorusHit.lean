import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalLegCollision

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking
attribute [local irreducible] torusDistance

def earlyTorusHit {L : Length} (t : ℝ) (y z v : Point) (ω : ConfigurationPath 1 L)
    (r C h : ℝ) : Set Noise :=
  {β | (∀s : Time,‖leg t y z β s-v‖≤10 ∧
      torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10) ∧
    (∀s : Time,‖leg t y z β s-z‖≤C) ∧
    ∃s : Time,h≤(s:ℝ) ∧ (s:ℝ)≤1/2 ∧ torusDistance L (projectPoint L (leg t y z β s)) (ω s 0)≤r}

lemma earlyTorusHit_subset {L : Length} {n : ℕ} (hn : 0<n) (I : Finset (Fin n))
    (t : ℝ) (y z v : Point) (ω : ConfigurationPath 1 L) (ζ : EuclideanPath)
    (hζ : IsPathLift ω ζ) {r C h : ℝ} (hL : 50<L.val) (hr : r≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤1)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → (meshTime j q:ℝ)≤1/2 → j∈I) :
    earlyTorusHit t y z v ω r C h⊆⋃j∈I,segmentHit t y z (meshTime j 0) (meshRemainder j)
      (meshLocalLift ω ζ v j) r C := by
  rintro β ⟨hconf,hconf',s,hs,hs1,hit⟩
  obtain ⟨j,q,hq⟩ := mesh_covers hn s
  have hj : j∈I := hI j q (by simpa only [hq] using hs) (by simpa only [hq] using hs1)
  have hh := (mesh_torus_hit_local hζ v (leg t y z β (meshTime j q)) j q hL
    (le_refl 1) (hdiam j hj) (hconf (meshTime j q)).1 (hconf (meshTime j q)).2 hr
    (by simpa only [hq] using hit)).2
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,?_⟩⟩
  exact ⟨hconf' _,prefixTime (meshRemainder j) q,prefixTime_le _ _,by simpa only [mesh_suffix_time] using hh⟩

lemma early_segment_bound (y z : Point) (s w : Time) (c : Time→Point)
    {t r C A : ℝ} (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hA0 : 0≤A)
    (hs : 0<(s:ℝ)) (hs1 : (s:ℝ)≤1/2)
    (hA : ∀q : Time,(q:ℝ)≤(w:ℝ) → ‖c q-c 0‖≤r*A)
    (hdrift : (w:ℝ)*C≤r) (hscale : t*(1-(s:ℝ))*(w:ℝ)≤r^2) :
    law (segmentHit t y z s w c r C)≤
      ENNReal.ofReal (hitConstant*r^3*(1+A)^3*(1+1/((t*(s:ℝ))*Real.sqrt (t*(s:ℝ))))) := by
  convert segment_sum_simplified (fun _ : Fin 1 ↦ y) z s w c ht hr hC hA0 hs hs1
    (by norm_num : (0:ℝ)<1) (fun i j h ↦ (h (Subsingleton.elim _ _)).elim) hA hdrift hscale using 1 <;> simp

lemma earlyTorusHit_bound {L : Length} {n k : ℕ} (hn : 0<n) (hk : 0<k)
    (y z v : Point) (I : Finset (Fin n)) (ω : ConfigurationPath 1 L) (A : Fin n→ℝ)
    {t r C h R J : ℝ} (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1)
    (hC : 0≤C) (hR : 0≤R)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → (meshTime j q:ℝ)≤1/2 → j∈I)
    (hlow : ∀j∈I,k<j.val) (hearly : ∀j∈I,(meshTime j 0:ℝ)≤1/2)
    (hA0 : ∀j∈I,0≤A j) (hAmax : ∀j∈I,A j≤R) (hAsum : (∑j∈I,(1+A j)^3)≤J)
    (hsmall : ∀j∈I,r*A j≤1)
    (hdiam : ∀j∈I,intervalDiameter (meshTime j 0) (meshTime j 1) ω≤r*A j)
    (hdrift : ∀j∈I,(meshRemainder j:ℝ)*C≤r)
    (hscale : t/(n:ℝ)≤r^2) :
    law (earlyTorusHit t y z v ω r C h)≤
      ENNReal.ofReal (hitConstant*r^3*(J+2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))) := by
  obtain ⟨ζ,hζ⟩ := exists_pathLift ω
  have hstart j (hj : j∈I) : 0<(meshTime j 0:ℝ) := by
    change 0<((j:ℝ)+0)/(n:ℝ)
    exact div_pos (by exact_mod_cast lt_trans hk (hlow j hj)) (by exact_mod_cast hn)
  apply ((measure_mono (earlyTorusHit_subset hn I t y z v ω ζ hζ hL hr1
    (fun j hj ↦ (hdiam j hj).trans (hsmall j hj)) hI)).trans (measure_biUnion_finset_le I _)).trans
  have hb j (hj : j∈I) := early_segment_bound y z (meshTime j 0) (meshRemainder j) (meshLocalLift ω ζ v j)
    ht hr hC (hA0 j hj) (hstart j hj) (hearly j hj)
    (fun q hq ↦ meshLocalLift_increment hζ v j (by linarith [hsmall j hj]) (hdiam j hj) q hq)
    (hdrift j hj) (by rw [mul_assoc,mesh_remaining]; simpa only [div_eq_mul_inv,one_div,one_mul] using hscale)
  apply (Finset.sum_le_sum hb).trans
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j hj ↦ by
    have hh := hitConstant_pos; have ha := hA0 j hj; have hs := hstart j hj; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : (∑j∈I,hitConstant*r^3*(1+A j)^3*(1+1/((t*(meshTime j 0:ℝ))*Real.sqrt (t*(meshTime j 0:ℝ)))))=
      hitConstant*r^3*((∑j∈I,(1+A j)^3)+∑j∈I,(1+A j)^3/(t*(meshTime j 0:ℝ)*Real.sqrt (t*(meshTime j 0:ℝ)))) := by
    rw [mul_add,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hitConstant_pos.le (pow_nonneg hr.le _))
  exact add_le_add hAsum (mesh_tail_bound I A hk ht hR hlow hAmax hA0)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma physical_early_collision {L : Length} {n : ℕ} (hn : 0<n)
    (y z v : Point) (ω : ConfigurationPath 1 L) {t r C h R Creg : ℝ}
    (hL : 50<L.val) (ht : 0<t) (hr : 0<r) (hr1 : r≤1) (hC : 0≤C)
    (hR : 0≤R) (hCreg : 0≤Creg) (hh : 0<h)
    (hreg : MeshRegular n r R Creg ω) (hsmall : r*R≤1)
    (hτr : t/(n:ℝ)≤r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*C/(n:ℝ)≤r) :
    law (earlyTorusHit t y z v ω r C (h/t))≤
      ENNReal.ofReal (hitConstant*(4*Creg*t*r+8*r*(1+R)^3/Real.sqrt (h/2))) := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter (fun j ↦ h/(2*t)≤(meshTime j 0:ℝ) ∧ (meshTime j 0:ℝ)≤1/2)
  let A : Fin n→ℝ := fun j ↦ diameterRatio r (meshSegment j ω)
  have hI j (hj : j∈I) := (Finset.mem_filter.mp hj).2
  have hA0 j : 0≤A j := diameterRatio_nonneg hr.le _
  have hAsum : (∑j∈I,(1+A j)^3)≤2*Creg*(n:ℝ) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ ↦ by have := hA0 j; positivity)).trans
    exact hreg.2.trans (by nlinarith)
  have hdi j : intervalDiameter (meshTime j 0) (meshTime j 1) ω≤r*A j := by
    rw [meshInterval_diameter]
    dsimp [A,diameterRatio]
    rw [mul_div_cancel₀ _ hr.ne']
  have hhit := earlyTorusHit_bound hn (endpointIndex_pos ht hlarge) y z v I ω A hL ht hr hr1 hC hR
    (fun j q hq hs ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,mesh_endpoint_index j q ht hwindow hq,
      (show (meshTime j 0:ℝ)≤(meshTime j q:ℝ) from by
        change ((j:ℝ)+0)/(n:ℝ)≤((j:ℝ)+(q:ℝ))/(n:ℝ)
        exact div_le_div_of_nonneg_right (add_le_add (le_refl _) q.property.1)
          (Nat.cast_nonneg n)).trans hs⟩)
    (fun j hj ↦ endpointIndex_gap j ht hh (hI j hj).1)
    (fun j hj ↦ (hI j hj).2)
    (fun j _ ↦ hA0 j) (fun j _ ↦ hreg.1 j) hAsum
    (fun j _ ↦ (mul_le_mul_of_nonneg_left (hreg.1 j) hr.le).trans hsmall)
    (fun j _ ↦ hdi j)
    (fun j hj ↦ (mul_le_mul_of_nonneg_right (meshRemainder_early_bound j (hI j hj).2) hC).trans
      (by simpa [div_mul_eq_mul_div] using hdrift)) hτr
  apply hhit.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := mesh_collision_budget (m:=0) (ε:=1) hn ht hr (by norm_num) hCreg hR
    (show 0<h/2 by positivity) hnscale (by
      simpa only [div_div,show (2:ℝ)*4=8 by norm_num] using endpointIndex_scale hn ht hlarge)
  simpa using hb

end HardSphere.Bridge

end
end

end

end OAI
