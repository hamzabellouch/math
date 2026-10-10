import Mathlib
import OAI.Geometry.Cannon.CirclePacking.Det

namespace OAI

section
section
section
namespace CannonPackingGeometry
open Set Metric

noncomputable section

def petalAngle (s t : ℝ) : ℝ := 2 * Real.arcsin (Real.sqrt (s*t))

@[simp] lemma petalAngle_zero_left (t : ℝ) : petalAngle 0 t = 0 := by
  simp [petalAngle]
@[simp] lemma petalAngle_zero_right (t : ℝ) : petalAngle t 0 = 0 := by
  simp [petalAngle]

lemma petalAngle_continuous : Continuous (fun p : ℝ × ℝ => petalAngle p.1 p.2) := by
  unfold petalAngle
  fun_prop

def RingData (n : ℕ) (t α : ℕ → ℝ) : Prop :=
  (∀ i, t i ∈ Icc (0:ℝ) 1) ∧
  (∀ i, α i ∈ Icc (0:ℝ) (2*Real.pi)) ∧
  α 0 = 0 ∧ α n = 2*Real.pi ∧ t n = t 0 ∧
  (∀ i, i < n → α (i+1) = α i + petalAngle (t i) (t (i+1))) ∧
  (∀ i, i < n → ∀ j, j < n → i ≠ j →
    Real.cos (α i - α j) ≤ 1-2*t i*t j)

lemma interval_constant (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → f (k+1) = f k) : f b = f a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    exact (h b hab (Nat.lt_succ_self b)).trans (ih (fun k hk hk' => h k hk (by omega)))

theorem RingData.first_pos {n : ℕ} {t α : ℕ → ℝ} (h : RingData n t α) : 0 < t 0 := by
  classical
  rcases h with ⟨ht,hα,hzero,hend,htend,hstep,hdisj⟩
  by_contra! hnpos
  have htzero : t 0 = 0 := le_antisymm hnpos (ht 0).1
  have hn : 0 < n := by
    by_contra! hh
    have : n=0 := by omega
    subst n
    linarith [Real.pi_pos]
  have hpos : ∃ i ∈ Finset.range n, 0 < t i := by
    by_contra! hh
    have hall : ∀ i < n, t i = 0 := by
      intro i hi
      exact le_antisymm (hh i (Finset.mem_range.mpr hi)) (ht i).1
    have heq := interval_constant α (Nat.zero_le n) (fun k _ hk => by
      simpa [hall k hk] using hstep k hk)
    linarith [Real.pi_pos]
  let S := (Finset.range n).filter (fun i => 0 < t i)
  have hSne : S.Nonempty := by
    obtain ⟨i,hi,hpi⟩ := hpos
    exact ⟨i,Finset.mem_filter.mpr ⟨hi,hpi⟩⟩
  let m := S.min' hSne
  let M := S.max' hSne
  have hm : m ∈ S := Finset.min'_mem S hSne
  have hM : M ∈ S := Finset.max'_mem S hSne
  have hmpos : 0 < t m := (Finset.mem_filter.mp hm).2
  have hMpos : 0 < t M := (Finset.mem_filter.mp hM).2
  have hmn : m < n := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hMn : M < n := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
  have hbefore : ∀ i, i < m → t i = 0 := by
    intro i hi
    have hin : i < n := hi.trans hmn
    by_contra hne
    have hp : 0 < t i := lt_of_le_of_ne (ht i).1 (Ne.symm hne)
    have hh : m ≤ i := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hp⟩)
    omega
  have hafter : ∀ i, M < i → i ≤ n → t i = 0 := by
    intro i hi hin
    by_cases heq : i=n
    · simpa [heq,htend] using htzero
    · have hil : i < n := lt_of_le_of_ne hin heq
      by_contra hne
      have hp : 0 < t i := lt_of_le_of_ne (ht i).1 (Ne.symm hne)
      have hh : i ≤ M := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hil,hp⟩)
      omega
  have hmangle : α m = 0 := by
    have hh := interval_constant α (Nat.zero_le m) (fun k _ hk => by
      simpa [hbefore k hk] using hstep k (hk.trans hmn))
    exact hh.trans hzero
  have hMangle : α M = 2*Real.pi := by
    have hh := interval_constant α hMn.le (fun k hk hkn => by
      simpa [hafter (k+1) (by omega) (by omega)] using hstep k hkn)
    exact hh.symm.trans hend
  by_cases heq : m=M
  · rw [heq,hMangle] at hmangle
    linarith [Real.pi_pos]
  · have hh := hdisj m hmn M hMn heq
    rw [hmangle,hMangle] at hh
    norm_num [Real.cos_two_pi] at hh
    nlinarith [mul_pos hmpos hMpos]

lemma ringData_closed (n : ℕ) : IsClosed {p : (ℕ → ℝ) × (ℕ → ℝ) | RingData n p.1 p.2} := by
  unfold RingData
  simp only [ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_
    (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)))))
  · simpa only [ofPred_forall,Set.preimage] using isClosed_iInter (fun i : ℕ =>
      isClosed_Icc.preimage (show Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i) by fun_prop))
  · simpa only [ofPred_forall,Set.preimage] using isClosed_iInter (fun i : ℕ =>
      isClosed_Icc.preimage (show Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i) by fun_prop))
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_eq (by fun_prop) (by unfold petalAngle; fun_prop)))
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_iInter (fun _ => isClosed_le (by fun_prop) (by fun_prop))))))

lemma ringData_compact (n : ℕ) : IsCompact {p : (ℕ → ℝ) × (ℕ → ℝ) | RingData n p.1 p.2} := by
  have ht : IsCompact (pi univ (fun _ : ℕ => Icc (0:ℝ) 1)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hα : IsCompact (pi univ (fun _ : ℕ => Icc (0:ℝ) (2*Real.pi))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply (ht.prod hα).of_isClosed_subset (ringData_closed n)
  intro p hp
  exact ⟨by simpa only [mem_pi,mem_univ,true_implies] using hp.1,
    by simpa only [mem_pi,mem_univ,true_implies] using hp.2.1⟩

theorem exists_ring_constant (n : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ t α : ℕ → ℝ, RingData n t α → c ≤ t 0 := by
  classical
  let K := {p : (ℕ → ℝ) × (ℕ → ℝ) | RingData n p.1 p.2}
  by_cases hK : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := (ringData_compact n).exists_isMinOn hK
      (show ContinuousOn (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 0) K from
        (by fun_prop : Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 0)).continuousOn)
    exact ⟨p.1 0,RingData.first_pos hp,fun t α h => hmin (show (t,α) ∈ K from h)⟩
  · exact ⟨1,zero_lt_one,fun t α h => (hK ⟨(t,α),h⟩).elim⟩

end
end CannonPackingGeometry

end
section
noncomputable section
namespace CannonPackingGeometry
open Set

lemma RingData.pos {n : ℕ} {t α : ℕ → ℝ} (h : RingData n t α) {i : ℕ} (hi : i<n) : 0<t i := by
  classical
  have hfirst := h.first_pos
  rcases h with ⟨ht,hα,hzero,hend,htend,hstep,hdisj⟩
  by_contra! hnpos
  have hti : t i=0 := le_antisymm hnpos (ht i).1
  have hi0 : 0 < i := by
    by_contra! hh
    have heq : i=0 := by omega
    subst i
    linarith
  let S := (Finset.range i).filter (fun j=>0<t j)
  have hS : S.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0,hfirst⟩⟩
  let m := S.max' hS
  have hm : m∈S := Finset.max'_mem S hS
  have hmi : m < i := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hmp : 0<t m := (Finset.mem_filter.mp hm).2
  let T := (Finset.Icc (i+1) n).filter (fun j=>0<t j)
  have hT : T.Nonempty := ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,by rwa [htend]⟩⟩
  let M := T.min' hT
  have hM : M∈T := Finset.min'_mem T hT
  have hiM : i < M := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hM).1).1; omega
  have hMn : M≤n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hM).1).2
  have hMp : 0<t M := (Finset.mem_filter.mp hM).2
  have hnull : ∀ k,m < k → k < M → t k=0 := by
    intro k hmk hkM
    by_cases hki : k=i
    · simpa only [hki] using hti
    by_contra hk
    have hkp : 0<t k := lt_of_le_of_ne (ht k).1 (Ne.symm hk)
    by_cases hki' : k < i
    · have H := Finset.le_max' S k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hki',hkp⟩)
      change k ≤ m at H
      omega
    · have H := Finset.min'_le T k (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hkp⟩)
      change M ≤ k at H
      omega
  have ham : α M=α m := interval_constant α (by omega) (fun k hmk hkM=>by
    by_cases hkm : k=m
    · have H:=hstep k (by omega)
      have hz : t (k+1)=0 := hnull (k+1) (by omega) (by omega)
      simpa only [hz,petalAngle_zero_right,add_zero] using H
    · simpa only [hnull k (by omega) hkM,petalAngle_zero_left,add_zero] using hstep k (by omega))
  by_cases hMn' : M<n
  · have H := hdisj m (by omega) M hMn' (by omega)
    rw [ham,sub_self,Real.cos_zero] at H
    nlinarith [mul_pos hmp hMp]
  · have hMeq : M=n := by omega
    have ham' : α m=2*Real.pi := ham.symm.trans (hMeq ▸ hend)
    by_cases hm0 : m=0
    · rw [hm0,hzero] at ham'; linarith [Real.pi_pos]
    · have H := hdisj m (by omega) 0 (by omega) hm0
      rw [ham',hzero,sub_zero,Real.cos_two_pi] at H
      nlinarith [mul_pos hmp hfirst]

theorem exists_bounded_ring_constant (N : ℕ) : ∃ c : ℝ,0<c ∧ c≤1 ∧
    ∀ n≤N,∀ t α : ℕ → ℝ,RingData n t α → ∀ i<n,c≤t i := by
  classical
  have hex (n : Fin (N+1)) (i : Fin n.val) : ∃ c : ℝ,0<c ∧
      ∀ t α : ℕ → ℝ,RingData n.val t α → c≤t i.val := by
    let K := {p : (ℕ → ℝ) × (ℕ → ℝ) | RingData n.val p.1 p.2}
    by_cases hK : K.Nonempty
    · obtain ⟨p,hp,hmin⟩ := (ringData_compact n.val).exists_isMinOn hK
        (show ContinuousOn (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i.val) K from (by fun_prop : Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i.val)).continuousOn)
      exact ⟨p.1 i.val,RingData.pos hp i.isLt,fun t α h=>hmin (show (t,α)∈K from h)⟩
    · exact ⟨1,zero_lt_one,fun t α h=>(hK ⟨(t,α),h⟩).elim⟩
  choose c hc using hex
  let S := Finset.univ.image (fun p : (n : Fin (N+1)) × Fin n.val=>c p.1 p.2)
  let T := insert 1 S
  have hT : T.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨T.min' hT,?_,Finset.min'_le T 1 (Finset.mem_insert_self _ _),?_⟩
  · have hmem:=Finset.min'_mem T hT
    rcases Finset.mem_insert.mp hmem with h|h
    · rw [h]; exact zero_lt_one
    · obtain ⟨p,-,hp⟩:=Finset.mem_image.mp h
      rw [←hp]; exact (hc p.1 p.2).1
  · intro n hn t α h i hi
    exact (Finset.min'_le T (c ⟨n,by omega⟩ ⟨i,hi⟩)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨⟨n,by omega⟩,⟨i,hi⟩⟩,Finset.mem_univ _,rfl⟩))).trans
        ((hc ⟨n,by omega⟩ ⟨i,hi⟩).2 t α h)
end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

lemma radius_fraction_mem {r s : ℝ} (hr : 0<r) (hs : 0<s) : s/(r+s)∈Ioo (0:ℝ) 1 :=
  ⟨div_pos hs (add_pos hr hs),(div_lt_one (add_pos hr hs)).mpr (by linarith)⟩

lemma tangent_petal_angle {r s t a : ℝ} (hr : 0<r) (hs : 0<s) (ht : 0<t)
    (ha : a∈Ioo (0:ℝ) Real.pi)
    (hc : 2*(r+s)*(r+t)*Real.cos a=(r+s)^2+(r+t)^2-(s+t)^2) :
    a=petalAngle (s/(r+s)) (t/(r+t)) := by
  let u:=s/(r+s)
  let v:=t/(r+t)
  have hu : u∈Ioo (0:ℝ) 1 := radius_fraction_mem hr hs
  have hv : v∈Ioo (0:ℝ) 1 := radius_fraction_mem hr ht
  have huv : u*v∈Ioo (0:ℝ) 1 := ⟨mul_pos hu.1 hv.1,lt_trans (mul_lt_mul_of_pos_left hv.2 hu.1) (by simpa using hu.2)⟩
  have hsq : Real.sqrt (u*v)∈Ioo (0:ℝ) 1 := ⟨Real.sqrt_pos.mpr huv.1,(Real.sqrt_lt huv.1.le (by norm_num)).mpr (by nlinarith [huv.2])⟩
  have has : 0<Real.arcsin (Real.sqrt (u*v)) := Real.arcsin_pos.mpr hsq.1
  have hat : Real.arcsin (Real.sqrt (u*v))<Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hsq.2
  apply Real.injOn_cos ⟨ha.1.le,ha.2.le⟩ (show petalAngle u v∈Icc (0:ℝ) Real.pi from ⟨by dsimp [petalAngle]; linarith,by dsimp [petalAngle]; linarith⟩)
  change Real.cos a=Real.cos (2*Real.arcsin (Real.sqrt (u*v)))
  rw [Real.cos_two_mul_eq_one_sub,Real.sin_arcsin (by linarith [hsq.1]) hsq.2.le,Real.sq_sqrt huv.1.le]
  dsimp [u,v]
  field_simp
  nlinarith

lemma fanRay_dist_sq_pair (L α : ℕ → ℝ) (i j : ℕ) :
    dist (fanRay L α i) (fanRay L α j)^2=(L i)^2+(L j)^2-
      2*L i*L j*Real.cos ((∑ k∈Finset.range i,α k)-(∑ k∈Finset.range j,α k)) := by
  have H:=rotate_polar_dist (L i) (L j) (∑ k∈Finset.range i,α k)
    ((∑ k∈Finset.range j,α k)-(∑ k∈Finset.range i,α k))
  simp only [add_sub_cancel] at H
  change dist ((L i:ℂ)*(Circle.exp (∑ k∈Finset.range i,α k):ℂ))
    ((L j:ℂ)*(Circle.exp (∑ k∈Finset.range j,α k):ℂ))^2=_
  rw [H,polar_distance_sq]
  congr 2
  have hh:=Real.cos_neg ((∑ k∈Finset.range i,α k)-(∑ k∈Finset.range j,α k))
  rw [neg_sub] at hh
  exact hh

lemma tangent_nonoverlap_cosine {r s t a D : ℝ} (hr : 0<r) (hs : 0<s) (ht : 0<t)
    (hD : s+t≤D)
    (hc : D^2=(r+s)^2+(r+t)^2-2*(r+s)*(r+t)*Real.cos a) :
    Real.cos a≤1-2*(s/(r+s))*(t/(r+t)) := by
  have hp : 0<(r+s)*(r+t) := mul_pos (add_pos hr hs) (add_pos hr ht)
  apply (mul_le_mul_iff_of_pos_right hp).mp
  have he : (1-2*(s/(r+s))*(t/(r+t)))*((r+s)*(r+t))=(r+s)*(r+t)-2*s*t := by
    field_simp
  rw [he]
  have hsquare : (s+t)^2≤D^2 := sq_le_sq₀ (by positivity) (by linarith) |>.mpr hD
  nlinarith only [hc,hsquare]

theorem actual_fan_ringData {n : ℕ} (hn : 0<n) (r : ℝ) (s α : Fin n → ℝ)
    (hr : 0<r) (hs : ∀ i,0<s i) (hα : ∀ i,α i∈Ioo (0:ℝ) Real.pi)
    (hsum : ∑ i,α i=2*Real.pi)
    (hcos : ∀ i,2*(r+s i)*(r+s (CannonCycleOrder.next hn i))*Real.cos (α i)=
      (r+s i)^2+(r+s (CannonCycleOrder.next hn i))^2-(s i+s (CannonCycleOrder.next hn i))^2)
    (A : ℂ) (B : Fin n → ℂ)
    (hAB : ∀ i,dist A (B i)=r+s i)
    (hBC : ∀ i,dist (B i) (B (CannonCycleOrder.next hn i))=s i+s (CannonCycleOrder.next hn i))
    (hop : ∀ i,orientedArea A (B (CannonCycleOrder.next hn i)) (B i)*
      orientedArea A (B (CannonCycleOrder.next hn i)) (B (CannonCycleOrder.next hn (CannonCycleOrder.next hn i)))<0)
    (hdis : ∀ i j : Fin n,i≠j → s i+s j≤dist (B i) (B j)) :
    ∃ t β : ℕ → ℝ,RingData n t β ∧ ∀ i : Fin n,t i.val=s i/(r+s i) := by
  let nx:=CannonCycleOrder.next hn
  let atN (k:ℕ):Fin n := ⟨k%n,Nat.mod_lt _ hn⟩
  have hat (i:Fin n):atN i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hat' (i:Fin n):atN (i.val+1)=nx i := Fin.ext (CannonCycleOrder.next_mod hn i).symm
  let L : ℕ → ℝ := fun k=>r+s (atN k)
  let al : ℕ → ℝ := fun k=>α (atN k)
  let d : ℕ → ℝ := fun k=>s (atN k)+s (nx (atN k))
  have hL (k : ℕ) (_ : k≤n) : 0<L k := add_pos hr (hs _)
  have hd (k : ℕ) (_ : k<n) : 0<d k := add_pos (hs _) (hs _)
  have hal (k : ℕ) (_ : k<n) : al k∈Ioo (0:ℝ) Real.pi := hα _
  have htotal : ∑ k∈Finset.range n,al k=2*Real.pi := by
    rw [Finset.sum_range]
    simpa only [al,hat] using hsum
  have hperiod : L n=L 0 := by simp [L,atN]
  have hcosN (k : ℕ) (hk : k<n) :
      2*L k*L (k+1)*Real.cos (al k)=(L k)^2+(L (k+1))^2-(d k)^2 := by
    have h0:=hat ⟨k,hk⟩
    have h1:=hat' ⟨k,hk⟩
    simp only at h0 h1
    simpa only [L,al,d,h0,h1] using hcos ⟨k,hk⟩
  obtain ⟨e,heA,heB⟩ := cyclic_fan_global_frame n hn L al d hL hd hal htotal hperiod hcosN A B
    (fun i=>by simpa only [L,hat] using hAB i)
    (fun i=>by simpa only [d,hat,nx,fanSucc,CannonCycleOrder.next] using hBC i)
    (fun i=>by simp only [L,hat',hat]; rfl) hop
  let t : ℕ → ℝ := fun k=>s (atN k)/(r+s (atN k))
  let β : ℕ → ℝ := fun k=>∑ j∈Finset.range (min k n),al j
  have halp (j : ℕ) : 0≤al j := (hα (atN j)).1.le
  have hb (k : ℕ) : β k∈Icc (0:ℝ) (2*Real.pi) := by
    refine ⟨Finset.sum_nonneg (fun j _=>halp j),?_⟩
    rw [←htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right k n)) (fun j _ _=>halp j)
  refine ⟨t,β,⟨fun k=>⟨(radius_fraction_mem hr (hs _)).1.le,(radius_fraction_mem hr (hs _)).2.le⟩,
    hb,by simp [β],by simpa [β] using htotal,by simp [t,atN],?_,?_⟩,fun i=>by simp only [t,hat]⟩
  · intro k hk
    dsimp [β]
    rw [min_eq_left (show k+1≤n by omega),min_eq_left hk.le,Finset.sum_range_succ]
    congr 1
    have heq := tangent_petal_angle hr (hs (atN k)) (hs (nx (atN k))) (hα (atN k)) (hcos (atN k))
    have hc : atN (k+1)=nx (atN k) := by
      simpa only [hat (⟨k,hk⟩:Fin n)] using hat' (⟨k,hk⟩:Fin n)
    simpa only [al,t,hc] using heq
  · intro i hi j hj hij
    have hneq : (⟨i,hi⟩:Fin n)≠⟨j,hj⟩ := fun hh=>hij (congrArg Fin.val hh)
    have hD := hdis ⟨i,hi⟩ ⟨j,hj⟩ hneq
    have hsq := fanRay_dist_sq_pair L al i j
    rw [←heB ⟨i,hi⟩,←heB ⟨j,hj⟩,e.dist_eq] at hsq
    have H := tangent_nonoverlap_cosine hr (hs ⟨i,hi⟩) (hs ⟨j,hj⟩) hD
      (by simpa only [L,hat (⟨i,hi⟩:Fin n),hat (⟨j,hj⟩:Fin n)] using hsq)
    simpa only [β,t,min_eq_left hi.le,min_eq_left hj.le,hat (⟨i,hi⟩:Fin n),hat (⟨j,hj⟩:Fin n)] using H

end CannonPackingGeometry

end
end
end
end

end OAI
