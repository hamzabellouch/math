import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Crossing

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem cyclic_folded_frames_positions (n:ℕ) (hn:0<n) (L α d:ℕ→ℝ)
    (hL:∀ k≤n,0<L k) (hd:∀ k<n,0<d k)
    (hα:∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs:∑ k∈Finset.range n,α k=2*Real.pi) (hp:L n=L 0)
    (hcos:∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2)
    (A B C:Fin n→ℂ)
    (hAB:∀ i,dist (A i) (B i)=L i.val)
    (hAC:∀ i,dist (A i) (C i)=L (i.val+1))
    (hBC:∀ i,dist (B i) (C i)=d i.val)
    (K:Fin n→(ℂ≃ᵢℂ))
    (hKA:∀ i,K i (A i)=A (fanSucc hn i))
    (hKC:∀ i,K i (C i)=B (fanSucc hn i))
    (hKB:∀ i,orientedArea (A (fanSucc hn i)) (B (fanSucc hn i)) (K i (B i))*
      orientedArea (A (fanSucc hn i)) (B (fanSucc hn i)) (C (fanSucc hn i))<0) :
    ∃ e:Fin n→(ℂ≃ᵢℂ),
      (∀ i,e i (A i)=0 ∧ e i (B i)=fanRay L α i.val ∧ e i (C i)=fanRay L α (i.val+1)) ∧
      ∀ i,K i*(e i).symm=(e (fanSucc hn i)).symm := by
  obtain ⟨hclose,hR,hD⟩ := closed_euclidean_fan n L α d hL hd hα hs hp hcos
  obtain ⟨e,he⟩ := fan_triangle_frames n L α d hL hd hα hs hp hcos A B C hAB hAC hBC
  have harea (i:Fin n) : orientedArea (A i) (B i) (C i)≠0 := by
    have hh := isometry_orientedArea_product (e i) (A i) (B i) (C i) (C i)
    rw [(he i).1,(he i).2.1,(he i).2.2] at hh
    intro hz
    rw [hz,mul_zero] at hh
    exact mul_ne_zero (hD i.val i.isLt).2.ne' (hD i.val i.isLt).2.ne' hh
  refine ⟨e,he,fun i=>?_⟩
  let j := fanSucc hn i
  have hray : fanRay L α (i.val+1)=fanRay L α j.val := fanRay_succ hn L α hclose i
  apply folded_frames_compatible (a:=A i) (b:=C i) (c:=B i)
    (A:=A j) (B:=B j) (C:=C j) (P:=0) (Q:=fanRay L α j.val)
    (e:=e i) (f:=e j)
  · intro hh
    have hh' := hAC i
    rw [hh,dist_self] at hh'
    exact (hL (i.val+1) (by omega)).ne' hh'.symm
  · calc dist (A i) (C i) = dist ((e i) (A i)) ((e i) (C i)) :=
          ((e i).dist_eq _ _).symm
         _ = dist ((e j) (A j)) ((e j) (B j)) := by
          rw [(he i).1,(he i).2.2,(he j).1,(he j).2.1,hray]
         _ = dist (A j) (B j) := (e j).dist_eq _ _
  · rw [orientedArea_swap]
    exact neg_ne_zero.mpr (harea i)
  · exact harea j
  · exact hKA i
  · exact hKC i
  · exact hKB i
  · exact (he i).1
  · exact (he i).2.2.trans hray
  · exact (he j).1
  · exact (he j).2.1
  · rw [(he i).2.1,(he j).2.2,←hray,orientedArea_swap 0 (fanRay L α (i.val+1))]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (hD i.val i.isLt).2)
      (by rw [hray]; exact (hD j.val j.isLt).2)

theorem cyclic_fan_global_frame (n : ℕ) (hn : 0<n) (L α d : ℕ → ℝ)
    (hL : ∀ k≤n,0<L k) (hd : ∀ k<n,0<d k)
    (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs : ∑ k∈Finset.range n,α k=2*Real.pi) (hp : L n=L 0)
    (hcos : ∀ k<n,2*L k*L (k+1)*Real.cos (α k)=(L k)^2+(L (k+1))^2-(d k)^2)
    (A : ℂ) (B : Fin n → ℂ)
    (hAB : ∀ i,dist A (B i)=L i.val)
    (hBC : ∀ i,dist (B i) (B (fanSucc hn i))=d i.val)
    (hLnext : ∀ i,L (i.val+1)=L (fanSucc hn i).val)
    (hop : ∀ i, orientedArea A (B (fanSucc hn i)) (B i)*
      orientedArea A (B (fanSucc hn i)) (B (fanSucc hn (fanSucc hn i)))<0) :
    ∃ e : ℂ≃ᵢℂ,e A=0 ∧ ∀ i,e (B i)=fanRay L α i.val := by
  obtain ⟨e,he,hstep⟩ := cyclic_folded_frames_positions n hn L α d hL hd hα hs hp hcos
    (fun _=>A) B (fun i=>B (fanSucc hn i)) hAB
    (fun i=>(hAB (fanSucc hn i)).trans (hLnext i).symm) hBC
    (fun _=>1) (fun _=>rfl) (fun _=>rfl) hop
  have heq (i j : Fin n) : e i=e j := by
    have H := CannonCycleOrder.eq_of_steps hn (fun i=>(e i).symm)
      (fun i=>by simpa only [one_mul,fanSucc,CannonCycleOrder.next] using hstep i) i j
    exact congrArg IsometryEquiv.symm H
  let i : Fin n := ⟨0,hn⟩
  refine ⟨e i,(he i).1,?_⟩
  intro j
  rw [heq i j]
  exact (he j).2.1

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

lemma sum_range_partition (a : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : 0≤t) (hn : t<∑ i∈Finset.range n,a i) :
    ∃ k,k<n ∧ (∑ i∈Finset.range k,a i)≤t ∧ t<∑ i∈Finset.range (k+1),a i := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty] at hn; exact (not_lt_of_ge ht hn).elim
  | succ n ih =>
    by_cases h : t<∑ i∈Finset.range n,a i
    · obtain ⟨k,hk,hlo,hhi⟩ := ih h
      exact ⟨k,by omega,hlo,hhi⟩
    · exact ⟨n,by omega,le_of_not_gt h,hn⟩

lemma polar_nonnegative_arg (p : ℂ) :
    ∃ t : ℝ,0≤t ∧ t<2*Real.pi ∧ p=(‖p‖:ℂ)*(Circle.exp t:ℂ) := by
  have hpi := Real.pi_pos
  by_cases h : Complex.arg p<0
  · refine ⟨Complex.arg p+2*Real.pi,by linarith [Complex.neg_pi_lt_arg p],by linarith,?_⟩
    rw [Circle.exp_add,Circle.exp_two_pi,mul_one]
    simpa only [Circle.coe_exp] using (Complex.norm_mul_exp_arg_mul_I p).symm
  · refine ⟨Complex.arg p,le_of_not_gt h,by linarith [Complex.arg_le_pi p],?_⟩
    simpa only [Circle.coe_exp] using (Complex.norm_mul_exp_arg_mul_I p).symm

theorem closed_fan_cones_cover (n : ℕ) (L α : ℕ → ℝ)
    (hL : ∀ k≤n,0<L k) (hα : ∀ k<n,α k∈Ioo (0:ℝ) Real.pi)
    (hs : ∑ k∈Finset.range n,α k=2*Real.pi) (p : ℂ) :
    ∃ k,k<n ∧ 0≤orientedArea 0 (fanRay L α k) p ∧
      0≤orientedArea 0 p (fanRay L α (k+1)) := by
  obtain ⟨t,ht,hthi,hp⟩ := polar_nonnegative_arg p
  obtain ⟨k,hk,hlo,hhi⟩ := sum_range_partition α n ht (by rwa [hs])
  let s := ∑ j∈Finset.range k,α j
  have hnext : (∑ j∈Finset.range (k+1),α j)=s+α k := Finset.sum_range_succ α k
  rw [hnext] at hhi
  have hleft : t-s∈Icc (0:ℝ) Real.pi := ⟨sub_nonneg.mpr hlo,by dsimp [s] at *; linarith [(hα k hk).2]⟩
  have hright : s+α k-t∈Icc (0:ℝ) Real.pi := ⟨by linarith,by linarith [(hα k hk).2]⟩
  refine ⟨k,hk,?_,?_⟩
  · rw [hp]
    change 0≤orientedArea 0 ((L k:ℂ)*(Circle.exp s:ℂ)) ((‖p‖:ℂ)*(Circle.exp t:ℂ))
    rw [show t=s+(t-s) by ring,rotated_polar_orientedArea]
    exact mul_nonneg (mul_nonneg (hL k (by omega)).le (norm_nonneg p))
      (Real.sin_nonneg_of_nonneg_of_le_pi hleft.1 hleft.2)
  · rw [hp]
    change 0≤orientedArea 0 ((‖p‖:ℂ)*(Circle.exp t:ℂ))
      ((L (k+1):ℂ)*(Circle.exp (∑ j∈Finset.range (k+1),α j):ℂ))
    rw [hnext,show s+α k=t+(s+α k-t) by ring,rotated_polar_orientedArea]
    exact mul_nonneg (mul_nonneg (norm_nonneg p) (hL (k+1) (by omega)).le)
      (Real.sin_nonneg_of_nonneg_of_le_pi hright.1 hright.2)

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonTangentWedges
open Set

def det (a b c : ℂ) : ℝ := (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)

lemma barycentric {a b c p : ℂ} (hd : det a b c≠0) :
    p=a+(det c a p/det a b c) • (b-a)+(det a b p/det a b c) • (c-a) := by
  apply Complex.ext
  all_goals simp only [Complex.add_re,Complex.smul_re,Complex.sub_re,Complex.add_im,Complex.smul_im,Complex.sub_im,smul_eq_mul]
  all_goals field_simp
  all_goals dsimp [det]; ring

lemma combination_norm_sq (b c : ℂ) (u v : ℝ) :
    ‖u • b+v • c‖^2=u^2*‖b‖^2+v^2*‖c‖^2+u*v*(‖b‖^2+‖c‖^2-‖b-c‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,Complex.sub_re,Complex.sub_im,smul_eq_mul]
  ring

theorem wedge_ball_opposite_positive {a b c p : ℂ} {r s t : ℝ}
    (hr : 0<r) (hs : 0<s) (ht : 0<t) (hab : dist a b=r+s)
    (hac : dist a c=r+t) (hbc : dist b c=s+t) (hD : 0<det a b c)
    (hp : dist a p<r) (h1 : 0≤det a b p) (h2 : 0≤det c a p) :
    0<det b c p := by
  let u := det c a p/det a b c
  let v := det a b p/det a b c
  have hu : 0≤u := div_nonneg h2 hD.le
  have hv : 0≤v := div_nonneg h1 hD.le
  have hp' : p-a=u • (b-a)+v • (c-a) := by
    have H := barycentric (p:=p) hD.ne'
    change p=a+u • (b-a)+v • (c-a) at H
    rw [H]; abel
  have hn := combination_norm_sq (b-a) (c-a) u v
  rw [←hp',←dist_eq_norm b a,←dist_eq_norm c a,
    show b-a-(c-a)=b-c by abel,←dist_eq_norm b c,
    dist_comm b a,dist_comm c a,hab,hac,hbc,←dist_eq_norm p a,dist_comm p a] at hn
  have heq : dist a p^2=r^2*(u+v)^2+2*r*(u+v)*(u*s+v*t)+(u*s-v*t)^2 := by
    rw [hn]; ring
  by_contra h
  have hsum : det a b p+det b c p+det c a p=det a b c := by dsimp [det]; ring
  have huv : 1≤u+v := by
    dsimp [u,v]
    rw [←add_div]
    apply (le_div_iff₀ hD).mpr
    linarith [le_of_not_gt h]
  have hsq : (1:ℝ)≤(u+v)^2 := by nlinarith
  have hterm := mul_le_mul_of_nonneg_left hsq (sq_nonneg r)
  have hpos : 0≤2*r*(u+v)*(u*s+v*t) := by positivity
  have hrem := sq_nonneg (u*s-v*t)
  have hdist := dist_nonneg (x:=a) (y:=p)
  nlinarith

end CannonTangentWedges

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

lemma orientedArea_eq_det (a b c : ℂ) : orientedArea a b c=CannonTangentWedges.det a b c := by
  simp only [orientedArea,CannonTangentWedges.det,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sub_re,Complex.sub_im]
  ring
lemma orientedArea_cyclic (a b c : ℂ) : orientedArea b c a=orientedArea a b c := by
  simp only [orientedArea_eq_det,CannonTangentWedges.det]; ring
lemma orientedArea_swap_first (a b c : ℂ) : orientedArea b a c= -orientedArea a b c := by
  simp only [orientedArea_eq_det,CannonTangentWedges.det]; ring
lemma winding_area_eq (a b c : ℂ) : CannonTriangleWinding.area a b c=orientedArea a b c := by
  rw [orientedArea_eq_det]; rfl

def TriInterior (a b c p : ℂ) : Prop :=
  0<orientedArea a b p*orientedArea a b c ∧
  0<orientedArea b c p*orientedArea b c a ∧
  0<orientedArea c a p*orientedArea c a b

lemma TriInterior.isometry (e : ℂ≃ᵢℂ) (a b c p : ℂ) :
    TriInterior (e a) (e b) (e c) (e p) ↔ TriInterior a b c p := by
  simp only [TriInterior,isometry_orientedArea_product]

lemma TriInterior.of_positive {a b c p : ℂ} (hD : 0<orientedArea a b c)
    (h1 : 0<orientedArea a b p) (h2 : 0<orientedArea b c p) (h3 : 0<orientedArea c a p) :
    TriInterior a b c p := by
  exact ⟨mul_pos h1 hD,mul_pos h2 (by rwa [orientedArea_cyclic]),
    mul_pos h3 (by rwa [orientedArea_cyclic,orientedArea_cyclic])⟩

lemma TriInterior.inside {a b c p : ℂ} (hD : 0<CannonTriangleWinding.area a b c)
    (h : TriInterior a b c p) : CannonTriangleWinding.Inside a b c p := by
  simp only [winding_area_eq] at hD
  change 0<CannonTriangleWinding.area a b p ∧ 0<CannonTriangleWinding.area b c p ∧ 0<CannonTriangleWinding.area c a p
  simp only [winding_area_eq]
  exact ⟨pos_of_mul_pos_left h.1 hD.le,
    pos_of_mul_pos_left h.2.1 (by rw [orientedArea_cyclic]; exact hD.le),
    pos_of_mul_pos_left h.2.2 (by rw [orientedArea_cyclic,orientedArea_cyclic]; exact hD.le)⟩

lemma TriInterior.edge_positive {a b c p x y z : ℂ} (h : TriInterior a b c p)
    (hx : x∈({a,b,c}:Finset ℂ)) (hy : y∈({a,b,c}:Finset ℂ)) (hz : z∈({a,b,c}:Finset ℂ))
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) : 0<orientedArea x y p*orientedArea x y z := by
  classical
  have hrev (a b c : ℂ) : orientedArea b a p*orientedArea b a c=orientedArea a b p*orientedArea a b c := by
    rw [orientedArea_swap_first a b p,orientedArea_swap_first a b c,neg_mul_neg]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy hz
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;> rcases hz with rfl|rfl|rfl
  all_goals first
    | exact (hxy rfl).elim
    | exact (hxz rfl).elim
    | exact (hyz rfl).elim
    | exact h.1
    | exact h.2.1
    | exact h.2.2
    | rw [hrev]; exact h.1
    | rw [hrev]; exact h.2.1
    | rw [hrev]; exact h.2.2

lemma TriInterior.of_vertices {a b c p x y z : ℂ} (h : TriInterior a b c p)
    (hx : x∈({a,b,c}:Finset ℂ)) (hy : y∈({a,b,c}:Finset ℂ)) (hz : z∈({a,b,c}:Finset ℂ))
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) : TriInterior x y z p :=
  ⟨h.edge_positive hx hy hz hxy hxz hyz,
    h.edge_positive hy hz hx hyz hxy.symm hxz.symm,
    h.edge_positive hz hx hy hxz.symm hyz.symm hxy⟩

lemma isometry_area_ne_zero (e : ℂ≃ᵢℂ) {a b c : ℂ} (h : orientedArea a b c≠0) :
    orientedArea (e a) (e b) (e c)≠0 := by
  intro hh
  have H := isometry_orientedArea_product e a b c c
  rw [hh,zero_mul] at H
  exact mul_ne_zero h h H.symm

end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem finite_star_ball_cover {n : ℕ} (hn : 0<n) (r : ℝ) (s α : Fin n → ℝ)
    (hr : 0<r) (hs : ∀ i,0<s i) (hα : ∀ i,α i∈Ioo (0:ℝ) Real.pi)
    (hsum : ∑ i,α i=2*Real.pi)
    (hcos : ∀ i,2*(r+s i)*(r+s (CannonCycleOrder.next hn i))*Real.cos (α i)=
      (r+s i)^2+(r+s (CannonCycleOrder.next hn i))^2-(s i+s (CannonCycleOrder.next hn i))^2)
    (A : ℂ) (B : Fin n → ℂ)
    (hAB : ∀ i,dist A (B i)=r+s i)
    (hBC : ∀ i,dist (B i) (B (CannonCycleOrder.next hn i))=s i+s (CannonCycleOrder.next hn i))
    (hop : ∀ i,orientedArea A (B (CannonCycleOrder.next hn i)) (B i)*
      orientedArea A (B (CannonCycleOrder.next hn i)) (B (CannonCycleOrder.next hn (CannonCycleOrder.next hn i)))<0)
    {p : ℂ} (hp : dist A p<r) (hgen : ∀ i,orientedArea A (B i) p≠0) :
    ∃ i,TriInterior A (B i) (B (CannonCycleOrder.next hn i)) p := by
  let nx:=CannonCycleOrder.next hn
  let atN (k:ℕ):Fin n := ⟨k%n,Nat.mod_lt _ hn⟩
  have hat (i:Fin n):atN i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hat' (i:Fin n):atN (i.val+1)=nx i := Fin.ext (CannonCycleOrder.next_mod hn i).symm
  let L : ℕ → ℝ := fun k=>r+s (atN k)
  let al : ℕ → ℝ := fun k=>α (atN k)
  let d : ℕ → ℝ := fun k=>s (atN k)+s (nx (atN k))
  have hL (k : ℕ) (hk : k≤n) : 0<L k := add_pos hr (hs _)
  have hd (k : ℕ) (hk : k<n) : 0<d k := add_pos (hs _) (hs _)
  have hal (k : ℕ) (hk : k<n) : al k∈Ioo (0:ℝ) Real.pi := hα _
  have htotal : ∑ k∈Finset.range n,al k=2*Real.pi := by
    rw [Finset.sum_range]
    simpa only [al,hat] using hsum
  have hperiod : L n=L 0 := by simp [L,atN]
  have hcosN (k : ℕ) (hk : k<n) :
      2*L k*L (k+1)*Real.cos (al k)=(L k)^2+(L (k+1))^2-(d k)^2 := by
    have h0:=hat ⟨k,hk⟩
    have h1:=hat' ⟨k,hk⟩
    simpa only [L,al,d,h0,h1] using hcos ⟨k,hk⟩
  obtain ⟨e,heA,heB⟩ := cyclic_fan_global_frame n hn L al d hL hd hal htotal hperiod hcosN A B
    (fun i=>by simpa only [L,hat] using hAB i)
    (fun i=>by simpa only [d,hat,nx,fanSucc,CannonCycleOrder.next] using hBC i)
    (fun i=>by simp only [L,hat',hat]; rfl) hop
  obtain ⟨hclose,hR,hD⟩:=closed_euclidean_fan n L al d hL hd hal htotal hperiod hcosN
  obtain ⟨k,hk,h1,h2⟩:=closed_fan_cones_cover n L al hL hal htotal (e p)
  let i : Fin n:=⟨k,hk⟩
  have hnext : fanRay L al (k+1)=e (B (nx i)) := by
    rw [heB]
    exact fanRay_succ hn L al hclose i
  have hcur : fanRay L al k=e (B i) := (heB i).symm
  have ha : 0<orientedArea 0 (e (B i)) (e p) := by
    rw [hcur] at h1
    exact lt_of_le_of_ne h1 (by simpa only [heA] using (isometry_area_ne_zero e (hgen i)).symm)
  have hb : 0<orientedArea (e (B (nx i))) 0 (e p) := by
    rw [hnext,orientedArea_swap,neg_nonneg] at h2
    have hh : orientedArea 0 (e (B (nx i))) (e p)≠0 := by
      simpa only [heA] using isometry_area_ne_zero e (hgen (nx i))
    rw [orientedArea_cyclic,orientedArea_cyclic,orientedArea_swap]
    exact neg_pos.mpr (lt_of_le_of_ne h2 hh)
  have hD' : 0<orientedArea 0 (e (B i)) (e (B (nx i))) := by
    rw [←hcur,←hnext]; exact (hD k hk).2
  have hc : 0<orientedArea (e (B i)) (e (B (nx i))) (e p) := by
    rw [orientedArea_eq_det]
    apply CannonTangentWedges.wedge_ball_opposite_positive (a:=0) hr (hs i) (hs (nx i))
    · rw [←heA,e.dist_eq]; exact hAB i
    · rw [←heA,e.dist_eq]; exact hAB (nx i)
    · rw [e.dist_eq]; exact hBC i
    · rwa [←orientedArea_eq_det]
    · rwa [←heA,e.dist_eq]
    · rw [←orientedArea_eq_det]; exact ha.le
    · rw [←orientedArea_eq_det]; exact hb.le
  refine ⟨i,?_⟩
  apply (TriInterior.isometry e A (B i) (B (nx i)) p).mp
  rw [heA]
  exact TriInterior.of_positive hD' ha hc hb

end CannonPackingGeometry

end
end
end
end

end OAI
