import Mathlib
import OAI.Analysis.HardSphere.Bridges.MeshLegHit

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma weighted_heat_tail {n k : ℕ} (I : Finset (Fin n)) (A : Fin n→ℝ)
    {τ M : ℝ} (hk : 0<k) (hτ : 0<τ) (hM : 0≤M)
    (hlow : ∀j∈I,k<j.val) (hA : ∀j∈I,A j≤M) :
    (∑j∈I,A j/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ)))≤
      M*2/(τ*Real.sqrt ((k:ℝ)*τ)) := by
  have hn j (hj : j∈I) : 0<(j:ℝ)*τ :=
    mul_pos (by exact_mod_cast (lt_trans hk (hlow j hj))) hτ
  calc
    _ ≤ ∑j∈I,M*(1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ))) := Finset.sum_le_sum (fun j hj ↦ by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (hA j hj) (by positivity))
    _ = M*(∑j∈I,1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ M*(2/(τ*Real.sqrt ((k:ℝ)*τ))) := by
      apply mul_le_mul_of_nonneg_left _ hM
      let f (l : ℕ) : ℝ := 1/(((k+l+1:ℕ):ℝ)*τ*Real.sqrt (((k+l+1:ℕ):ℝ)*τ))
      have he : (∑j∈I,1/((j:ℝ)*τ*Real.sqrt ((j:ℝ)*τ)))=
          ∑l∈I.image (fun j ↦ j.val-k-1),f l := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro j hj
          have hj' := hlow j hj
          have ee : k+(j.val-k-1)+1=j.val := by omega
          simp only [f,ee]
        · intro i hi j hj he
          apply Fin.ext
          have hi' := hlow i hi
          have hj' := hlow j hj
          change i.val-k-1=j.val-k-1 at he
          omega
      rw [he]
      apply (Finset.sum_le_sum_of_subset_of_nonneg (t:=Finset.range n) ?_ ?_).trans
        (inverse_heat_tail n k hk hτ)
      · intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro j hj _
        positivity
    _ = _ := by ring

lemma hit_mem_mesh_union {n : ℕ} (hn : 0<n) (I : Finset (Fin n))
    (t : ℝ) (y u : Point) (β : Noise) (c : C(Time,Point)) (r C h : ℝ)
    {B : Set Point} (hu : u∈B) (s : Time) (hs : h≤(s:ℝ))
    (hit : ‖leg t y u β s-c s‖≤r)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I)
    (hconf : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → ‖leg t y u β (meshTime j 0)-u‖≤C) :
    (u,β)∈meshHitUnion I t y B (fun j ↦ c.comp (suffixTime (meshTime j 0))) r C := by
  obtain ⟨j,q,hq⟩ := mesh_covers hn s
  have hj : j∈I := hI j q (by simpa only [hq] using hs)
  change (u,β)∈⋃j∈I,combinedSegmentHit t y B (meshTime j 0) (meshRemainder j) (c.comp (suffixTime (meshTime j 0))) r C
  refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,?_⟩⟩
  let w := prefixTime (meshRemainder j) q
  have hw : (w:ℝ)≤(meshRemainder j:ℝ) := prefixTime_le (meshRemainder j) q
  have he : suffixTime (meshTime j 0) w=s := (mesh_suffix_time j q).trans hq
  by_cases hearly : (meshTime j 0:ℝ)≤1/2
  · simp only [combinedSegmentHit,ite_eq_left hearly,jointSegmentHit,mem_ofPred_eq,segmentHit]
    exact ⟨hconf j hj hearly,w,hw,by simpa only [ContinuousMap.comp_apply,he] using hit⟩
  · simp only [combinedSegmentHit,ite_eq_right hearly,mem_preimage,uniformSegmentHit,mem_ofPred_eq,Prod.swap_prod_mk]
    exact ⟨hu,w,hw,by simpa only [ContinuousMap.comp_apply,he] using hit⟩

def legWindowCollision (t : ℝ) (y : Point) (B : Set Point) (c : C(Time,Point))
    (r C h S : ℝ) : Set (Point×Noise) :=
  {p | p.1∈B ∧ (∀s : Time, ‖leg t y p.1 p.2 s-p.1‖≤C) ∧
    (∀s : Time,(s:ℝ)≤h → ‖leg t y p.1 p.2 s-y‖≤S) ∧
    ∃s : Time,‖leg t y p.1 p.2 s-c s‖≤r}

lemma endpoint_no_hit {r S : ℝ} {x y z w : Point}
    (hsep : r+2*S<‖y-z‖) (hx : ‖x-y‖≤S) (hw : ‖w-z‖≤S) :
    ¬‖x-w‖≤r := by
  intro hit
  have htri : ‖y-z‖≤‖x-y‖+‖x-w‖+‖w-z‖ := by
    calc
      _ = ‖(y-x)+(x-w)+(w-z)‖ := by congr 1; abel
      _ ≤ ‖y-x‖+‖x-w‖+‖w-z‖ := by
        have h₁ := norm_add_le ((y-x)+(x-w)) (w-z)
        have h₂ := norm_add_le (y-x) (x-w)
        linarith
      _ = _ := by rw [norm_sub_rev y x]
  linarith

lemma windowCollision_subset {n : ℕ} (hn : 0<n) (I : Finset (Fin n))
    {t r C h S : ℝ} (y : Point) (B : Set Point) (c : C(Time,Point))
    (hsep : r+2*S<‖y-c 0‖)
    (hcwin : ∀s : Time,(s:ℝ)≤h → ‖c s-c 0‖≤S)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I) :
    legWindowCollision t y B c r C h S ⊆
      meshHitUnion I t y B (fun j ↦ c.comp (suffixTime (meshTime j 0))) r C := by
  rintro ⟨u,β⟩ ⟨hu,hconf,hwin,s,hit⟩
  have hs : h<(s:ℝ) := lt_of_not_ge (fun hh ↦ endpoint_no_hit hsep (hwin s hh) (hcwin s hh) hit)
  exact hit_mem_mesh_union hn I t y u β c r C h hu s hs.le hit hI (fun j _ _ ↦ hconf _)

lemma mesh_tail_bound {n k : ℕ} (I : Finset (Fin n)) (A : Fin n→ℝ)
    {t R : ℝ} (hk : 0<k) (ht : 0<t) (hR : 0≤R)
    (hlow : ∀j∈I,k<j.val) (hA : ∀j∈I,A j≤R) (hA0 : ∀j∈I,0≤A j) :
    (∑j∈I,(1+A j)^3/(t*(meshTime j 0:ℝ)*Real.sqrt (t*(meshTime j 0:ℝ))))≤
      2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))) := by
  by_cases hn : 0<n
  · have htau : 0<t/(n:ℝ) := div_pos ht (by exact_mod_cast hn)
    have hh := weighted_heat_tail I (fun j ↦ (1+A j)^3) hk htau (show 0≤(1+R)^3 by positivity) hlow
      (fun j hj ↦ pow_le_pow_left₀ (by linarith [hA0 j hj]) (by linarith [hA j hj]) 3)
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro j hj
      have he : t*(meshTime j 0:ℝ)=(j:ℝ)*(t/(n:ℝ)) := by simp only [meshTime,show ((0:Time):ℝ)=0 from rfl,add_zero]; ring
      rw [he]
    · ring
  · have hn0 : n=0 := by omega
    subst n
    have he : I=∅ := Finset.eq_empty_of_forall_notMem (fun j ↦ Fin.elim0 j)
    simp [he]

lemma windowCollision_sum {m n k : ℕ} (hn : 0<n) (hk : 0<k)
    (y : Fin m→Point) (I : Finset (Fin n)) (c : C(Time,Point)) (A : Fin n→ℝ)
    {t r C ε h S R J : ℝ}
    (ht : 0<t) (hr : 0<r) (hC : 0≤C) (hε : 0<ε) (hR : 0≤R)
    (hsep : ∀i j,i≠j → ε^2 ≤ square (y i-y j))
    (houter : ∀i,r+2*S<‖y i-c 0‖)
    (hcwin : ∀s : Time,(s:ℝ)≤h → ‖c s-c 0‖≤S)
    (hI : ∀j : Fin n,∀q : Time,h≤(meshTime j q:ℝ) → j∈I)
    (hlow : ∀j∈I,k<j.val)
    (hA0 : ∀j∈I,0≤A j) (hAmax : ∀j∈I,A j≤R)
    (hAsum : (∑j∈I,(1+A j)^3)≤J)
    (hA : ∀j∈I,∀q : Time,(q:ℝ)≤(meshRemainder j:ℝ) →
      ‖c (suffixTime (meshTime j 0) q)-c (meshTime j 0)‖≤r*A j)
    (hdrift : ∀j∈I,(meshTime j 0:ℝ)≤1/2 → (meshRemainder j:ℝ)*C≤r)
    (hlate : t/(n:ℝ)≤r^2) (hdrift' : C/(n:ℝ)≤r)
    {B : Set Point} (hBm : MeasurableSet B) (hB : (volume : Measure Point) B≤1)
    (hBdist : ∀i v,v∈B → ‖v-y i‖≤C) :
    (∑i,((volume.restrict B).prod law) (legWindowCollision t (y i) B c r C h S))≤
      ENNReal.ofReal (hitConstant*r^3*((ε⁻¹^3+(m:ℝ))*J+
        2*(1+R)^3/((t/(n:ℝ))*Real.sqrt ((k:ℝ)*(t/(n:ℝ)))))) := by
  have hstart j (hj : j∈I) : 0<(meshTime j 0:ℝ) := by
    change 0<((j:ℝ)+0)/(n:ℝ)
    exact div_pos (by exact_mod_cast (lt_trans hk (hlow j hj))) (by exact_mod_cast hn)
  apply (Finset.sum_le_sum (fun i _ ↦ measure_mono (windowCollision_subset hn I (y i) B c
    (houter i) hcwin hI))).trans
  apply (mesh_hit_sum y I (fun j ↦ c.comp (suffixTime (meshTime j 0))) A ht hr hC hε hsep hA0 hstart
    (fun j hj q hq ↦ by simpa only [ContinuousMap.comp_apply,suffixTime_zero] using hA j hj q hq)
    hdrift hlate hdrift' hBm hB hBdist).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hitConstant_pos.le (pow_nonneg hr.le _))
  exact add_le_add (mul_le_mul_of_nonneg_left hAsum (by positivity))
    (mesh_tail_bound I A hk ht hR hlow hAmax hA0)

end HardSphere.Bridge

end

end OAI
