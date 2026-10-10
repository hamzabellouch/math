import Mathlib
import OAI.Geometry.Cannon.CirclePacking.Det

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem open_euclidean_fan (n : ℕ) (L α d : ℕ → ℝ)
    (hL : ∀ k≤n,0<L k) (hd : ∀ k<n,0<d k)
    (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hcos : ∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2) :
    (∀ k≤n,dist (0:ℂ) (fanRay L α k)=L k) ∧
    ∀ k<n,dist (fanRay L α k) (fanRay L α (k+1))=d k ∧
      0<orientedArea 0 (fanRay L α k) (fanRay L α (k+1)) := by
  constructor
  · intro k hk; rw [dist_zero_left]; exact fanRay_norm (hL k hk).le
  · intro k hk
    constructor
    · have he := fanRay_dist_sq L α k
      rw [hcos k hk] at he
      nlinarith [dist_nonneg (x:=fanRay L α k) (y:=fanRay L α (k+1)),hd k hk]
    · rw [fanRay_orientedArea]
      exact mul_pos (mul_pos (hL k (by omega)) (hL (k+1) (by omega)))
        (Real.sin_pos_of_pos_of_lt_pi (hα k hk).1 (hα k hk).2)

theorem open_fan_global_frame (n : ℕ) (hn : 0<n) (L α d : ℕ → ℝ)
    (hL : ∀ k≤n,0<L k) (hd : ∀ k<n,0<d k)
    (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hcos : ∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2)
    (A : ℂ) (B : ℕ → ℂ)
    (hAB : ∀ k≤n,dist A (B k)=L k)
    (hBC : ∀ k<n,dist (B k) (B (k+1))=d k)
    (hop : ∀ k,k+1<n → orientedArea A (B (k+1)) (B k)*
      orientedArea A (B (k+1)) (B (k+2))<0) :
    ∃ e : ℂ≃ᵢℂ,e A=0 ∧ ∀ k≤n,e (B k)=fanRay L α k := by
  obtain ⟨hR,hD⟩:=open_euclidean_fan n L α d hL hd hα hcos
  obtain ⟨e,heA,he0,he1⟩:=congruent_triangle_isometry A (B 0) (B 1) 0 (fanRay L α 0) (fanRay L α 1)
    (by intro H; have HH:=hAB 0 (by omega); rw [H,dist_self] at HH; exact (hL 0 (by omega)).ne' HH.symm)
    ((hAB 0 (by omega)).trans (hR 0 (by omega)).symm)
    ((hAB 1 (by omega)).trans (hR 1 (by omega)).symm)
    ((hBC 0 hn).trans (hD 0 hn).1.symm)
  refine ⟨e,heA,?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases h0 : k=0
    · subst k; exact he0
    by_cases h1 : k=1
    · subst k; exact he1
    obtain ⟨j,rfl⟩ : ∃ j,k=j+2 := ⟨k-2,by omega⟩
    have Hj:=ih j (by omega) (by omega)
    have Hj1:=ih (j+1) (by omega) (by omega)
    have hneg : orientedArea 0 (fanRay L α (j+1)) (fanRay L α j)<0 := by
      rw [orientedArea_swap]
      exact neg_neg_of_pos (hD j (by omega)).2
    apply point_unique_of_two_distances_and_side 0 (fanRay L α (j+1)) (e (B (j+2))) (fanRay L α (j+2))
      (by intro H; have HH:=hR (j+1) (by omega); rw [←H,dist_self] at HH; exact (hL _ (by omega)).ne' HH.symm)
      (orientedArea 0 (fanRay L α (j+1)) (fanRay L α j))
    · calc
        dist 0 (e (B (j+2))) = dist A (B (j+2)) := by rw [←heA,e.dist_eq]
        _ = L (j+2) := hAB _ hk
        _ = dist 0 (fanRay L α (j+2)) := (hR _ hk).symm
    · calc
        dist (fanRay L α (j+1)) (e (B (j+2))) = dist (B (j+1)) (B (j+2)) := by rw [←Hj1,e.dist_eq]
        _ = d (j+1) := hBC _ (by omega)
        _ = dist (fanRay L α (j+1)) (fanRay L α (j+2)) := (hD (j+1) (by omega)).1.symm
    · have H := isometry_orientedArea_product e A (B (j+1)) (B (j+2)) (B j)
      rw [heA,Hj1,Hj] at H
      rw [H,mul_comm]
      exact hop j (by omega)
    · exact mul_neg_of_pos_of_neg (hD (j+1) (by omega)).2 hneg

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem open_fan_cones_cover (n : ℕ) (L α : ℕ → ℝ)
    (hL : ∀ k≤n,0<L k) (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs : (∑ k∈Finset.range n,α k)∈Ioo (0:ℝ) Real.pi) (p : ℂ)
    (hp0 : 0<orientedArea 0 (fanRay L α 0) p)
    (hpn : 0<orientedArea 0 p (fanRay L α n)) :
    ∃ k,k<n ∧ 0≤orientedArea 0 (fanRay L α k) p ∧
      0≤orientedArea 0 p (fanRay L α (k+1)) := by
  obtain ⟨t,ht,hthi,hp⟩ := polar_nonnegative_arg p
  let s := ∑ k∈Finset.range n,α k
  have hsin : 0<Real.sin t := by
    rw [hp,fanRay_zero,polar_orientedArea] at hp0
    exact pos_of_mul_pos_right hp0 (mul_nonneg (hL 0 (by omega)).le (norm_nonneg p))
  have htpi : t<Real.pi := by
    by_contra h
    have hh : Real.sin (t-Real.pi)≥0 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hh
    linarith
  have hsin' : 0<Real.sin (s-t) := by
    rw [hp] at hpn
    change 0<orientedArea 0 ((‖p‖:ℂ)*(Circle.exp t:ℂ)) ((L n:ℂ)*(Circle.exp s:ℂ)) at hpn
    rw [show s=t+(s-t) by ring,rotated_polar_orientedArea] at hpn
    exact pos_of_mul_pos_right hpn (mul_nonneg (norm_nonneg p) (hL n le_rfl).le)
  have hts : t<s := by
    by_contra h
    have hh := Real.sin_nonpos_of_nonpos_of_neg_pi_le (show s-t≤0 by linarith)
      (show -Real.pi ≤ s-t by dsimp [s]; linarith [hs.1])
    exact (not_lt_of_ge hh) hsin'
  obtain ⟨k,hk,hlo,hhi⟩:=sum_range_partition α n ht hts
  let u := ∑ j∈Finset.range k,α j
  have hnext : (∑ j∈Finset.range (k+1),α j)=u+α k := Finset.sum_range_succ α k
  rw [hnext] at hhi
  have hleft : t-u∈Icc (0:ℝ) Real.pi :=
    ⟨sub_nonneg.mpr hlo, by linarith [(hα k hk).2]⟩
  have hright : u+α k-t∈Icc (0:ℝ) Real.pi := ⟨by linarith,by linarith [(hα k hk).2]⟩
  refine ⟨k,hk,?_,?_⟩
  · rw [hp]
    change 0≤orientedArea 0 ((L k:ℂ)*(Circle.exp u:ℂ)) ((‖p‖:ℂ)*(Circle.exp t:ℂ))
    rw [show t=u+(t-u) by ring,rotated_polar_orientedArea]
    exact mul_nonneg (mul_nonneg (hL k (by omega)).le (norm_nonneg p))
      (Real.sin_nonneg_of_nonneg_of_le_pi hleft.1 hleft.2)
  · rw [hp]
    change 0≤orientedArea 0 ((‖p‖:ℂ)*(Circle.exp t:ℂ))
      ((L (k+1):ℂ)*(Circle.exp (∑ j∈Finset.range (k+1),α j):ℂ))
    rw [hnext,show u+α k=t+(u+α k-t) by ring,rotated_polar_orientedArea]
    exact mul_nonneg (mul_nonneg (norm_nonneg p) (hL (k+1) (by omega)).le)
      (Real.sin_nonneg_of_nonneg_of_le_pi hright.1 hright.2)

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem open_star_ball_cover (n : ℕ) (hn : 0<n) (r : ℝ) (s α : ℕ → ℝ)
    (hr : 0<r) (hs : ∀ k≤n,0<s k) (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hsum : (∑ k∈Finset.range n,α k)∈Ioo (0:ℝ) Real.pi)
    (hcos : ∀ k<n,2*(r+s k)*(r+s (k+1))*Real.cos (α k)=
      (r+s k)^2+(r+s (k+1))^2-(s k+s (k+1))^2)
    (A : ℂ) (B : ℕ → ℂ)
    (hAB : ∀ k≤n,dist A (B k)=r+s k)
    (hBC : ∀ k<n,dist (B k) (B (k+1))=s k+s (k+1))
    (hop : ∀ k,k+1<n → orientedArea A (B (k+1)) (B k)*
      orientedArea A (B (k+1)) (B (k+2))<0)
    {p : ℂ} (hp : dist A p<r) (houter : TriInterior A (B 0) (B n) p)
    (hgen : ∀ k≤n,orientedArea A (B k) p≠0) :
    ∃ k,k<n ∧ TriInterior A (B k) (B (k+1)) p := by
  let L := fun k=>r+s k
  let d := fun k=>s k+s (k+1)
  have hL (k : ℕ) (hk : k≤n) : 0<L k := add_pos hr (hs k hk)
  have hd (k : ℕ) (hk : k<n) : 0<d k := add_pos (hs _ (by omega)) (hs _ (by omega))
  obtain ⟨e,heA,heB⟩:=open_fan_global_frame n hn L α d hL hd hα hcos A B hAB hBC hop
  obtain ⟨hR,hD⟩:=open_euclidean_fan n L α d hL hd hα hcos
  have hpos : 0<orientedArea 0 (fanRay L α 0) (fanRay L α n) := by
    rw [fanRay_zero]
    change 0<orientedArea 0 (L 0:ℂ)
      ((L n:ℂ)*(Circle.exp (∑ k∈Finset.range n,α k):ℂ))
    rw [polar_orientedArea]
    exact mul_pos (mul_pos (hL _ (by omega)) (hL _ le_rfl))
      (Real.sin_pos_of_pos_of_lt_pi hsum.1 hsum.2)
  have H:= (TriInterior.isometry e A (B 0) (B n) p).mpr houter
  rw [heA,heB 0 (by omega),heB n le_rfl] at H
  have hp0 : 0<orientedArea 0 (fanRay L α 0) (e p) := pos_of_mul_pos_left H.1 hpos.le
  have hpn : 0<orientedArea 0 (e p) (fanRay L α n) := by
    have hp1 := pos_of_mul_pos_left H.2.2 (by rw [orientedArea_cyclic,orientedArea_cyclic]; exact hpos.le)
    rw [orientedArea_cyclic,orientedArea_cyclic] at hp1; exact hp1
  obtain ⟨k,hk,h1,h2⟩:=open_fan_cones_cover n L α hL hα hsum (e p) hp0 hpn
  have hcur := heB k (by omega)
  have hnext := heB (k+1) (by omega)
  have ha : 0<orientedArea 0 (e (B k)) (e p) := by
    rw [←hcur] at h1
    exact lt_of_le_of_ne h1 (by simpa only [heA] using (isometry_area_ne_zero e (hgen k (by omega))).symm)
  have hb : 0<orientedArea (e (B (k+1))) 0 (e p) := by
    rw [←hnext,orientedArea_swap,neg_nonneg] at h2
    have hh : orientedArea 0 (e (B (k+1))) (e p)≠0 := by
      simpa only [heA] using isometry_area_ne_zero e (hgen _ (by omega))
    rw [orientedArea_cyclic,orientedArea_cyclic,orientedArea_swap]
    exact neg_pos.mpr (lt_of_le_of_ne h2 hh)
  have hD' : 0<orientedArea 0 (e (B k)) (e (B (k+1))) := by
    rw [hcur,hnext]; exact (hD k hk).2
  have hc : 0<orientedArea (e (B k)) (e (B (k+1))) (e p) := by
    rw [orientedArea_eq_det]
    apply CannonTangentWedges.wedge_ball_opposite_positive (a:=0) hr (hs k (by omega)) (hs (k+1) (by omega))
    · rw [←heA,e.dist_eq]; exact hAB k (by omega)
    · rw [←heA,e.dist_eq]; exact hAB (k+1) (by omega)
    · rw [e.dist_eq]; exact hBC k hk
    · rwa [←orientedArea_eq_det]
    · rwa [←heA,e.dist_eq]
    · rw [←orientedArea_eq_det]; exact ha.le
    · rw [←orientedArea_eq_det]; exact hb.le
  refine ⟨k,hk,?_⟩
  apply (TriInterior.isometry e A (B k) (B (k+1)) p).mp
  rw [heA]
  exact TriInterior.of_positive hD' ha hc hb

end CannonPackingGeometry

end
end
end
end

end OAI
