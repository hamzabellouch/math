import Mathlib
import OAI.Geometry.Cannon.CirclePacking.OpenEuclideanFan
import OAI.Geometry.Cannon.CirclePacking.PetalAngle

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set

def SectorRingData (n : ℕ) (t α : ℕ → ℝ) : Prop :=
  (∀ i,t i∈Icc (0:ℝ) 1) ∧ (∀ i,α i∈Icc (0:ℝ) Real.pi) ∧
  t 0=1/2 ∧ t n=1/2 ∧ α 0=0 ∧ α n=Real.pi/3 ∧
  (∀ i,i<n → α (i+1)=α i+petalAngle (t i) (t (i+1))) ∧
  ∀ i,i≤n → ∀ j,j≤n → i≠j → Real.cos (α i-α j)≤1-2*t i*t j

lemma SectorRingData.pos {n : ℕ} {t α : ℕ → ℝ} (h : SectorRingData n t α)
    {i : ℕ} (hi : i≤n) : 0<t i := by
  classical
  rcases h with ⟨ht,_hα,ht0,htn,_hzero,_hend,hstep,hdisj⟩
  by_contra! hnpos
  have hti : t i=0 := le_antisymm hnpos (ht i).1
  have hfirst : 0<t 0 := by rw [ht0]; norm_num
  have hlast : 0<t n := by rw [htn]; norm_num
  have hi0 : 0 < i := by
    by_contra! hh
    have heq : i=0 := by omega
    subst i
    linarith
  have hin : i<n := by
    by_contra! hh
    have heq : i=n := by omega
    subst i
    linarith
  let S := (Finset.range i).filter (fun j=>0<t j)
  have hS : S.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi0,hfirst⟩⟩
  let m := S.max' hS
  have hm : m∈S := Finset.max'_mem S hS
  have hmi : m < i := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hmp : 0<t m := (Finset.mem_filter.mp hm).2
  let T := (Finset.Icc (i+1) n).filter (fun j=>0<t j)
  have hT : T.Nonempty := ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,hlast⟩⟩
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
  have H := hdisj m (by omega) M hMn (by omega)
  rw [ham,sub_self,Real.cos_zero] at H
  nlinarith [mul_pos hmp hMp]

lemma sectorRingData_closed (n : ℕ) :
    IsClosed {p : (ℕ → ℝ) × (ℕ → ℝ) | SectorRingData n p.1 p.2} := by
  unfold SectorRingData
  simp only [ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_
    (IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))))))
  · simpa only [ofPred_forall,Set.preimage] using isClosed_iInter (fun i : ℕ =>
      isClosed_Icc.preimage (show Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i) by fun_prop))
  · simpa only [ofPred_forall,Set.preimage] using isClosed_iInter (fun i : ℕ =>
      isClosed_Icc.preimage (show Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2 i) by fun_prop))
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _hi =>
      isClosed_eq (by fun_prop) (by unfold petalAngle; fun_prop)))
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _hi =>
      isClosed_iInter (fun j => isClosed_iInter (fun _hj =>
      isClosed_iInter (fun _hij => isClosed_le (by fun_prop) (by fun_prop))))))

lemma sectorRingData_compact (n : ℕ) :
    IsCompact {p : (ℕ → ℝ) × (ℕ → ℝ) | SectorRingData n p.1 p.2} := by
  have ht : IsCompact (pi univ (fun _ : ℕ => Icc (0:ℝ) 1)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hα : IsCompact (pi univ (fun _ : ℕ => Icc (0:ℝ) Real.pi)) := isCompact_univ_pi (fun _ => isCompact_Icc)
  apply (ht.prod hα).of_isClosed_subset (sectorRingData_closed n)
  intro p hp
  exact ⟨by simpa only [mem_pi,mem_univ,true_implies] using hp.1,
    by simpa only [mem_pi,mem_univ,true_implies] using hp.2.1⟩

theorem exists_bounded_sector_constant (N : ℕ) : ∃ c : ℝ,0<c ∧ c≤1 ∧
    ∀ n≤N,∀ t α : ℕ → ℝ,SectorRingData n t α → ∀ i≤n,c≤t i := by
  classical
  have hex (n : Fin (N+1)) (i : Fin (n.val+1)) : ∃ c : ℝ,0<c ∧
      ∀ t α : ℕ → ℝ,SectorRingData n.val t α → c≤t i.val := by
    let K := {p : (ℕ → ℝ) × (ℕ → ℝ) | SectorRingData n.val p.1 p.2}
    by_cases hK : K.Nonempty
    · obtain ⟨p,hp,hmin⟩ := (sectorRingData_compact n.val).exists_isMinOn hK
        (show ContinuousOn (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i.val) K from (by fun_prop : Continuous (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1 i.val)).continuousOn)
      exact ⟨p.1 i.val,SectorRingData.pos hp (by omega),fun t α h=>hmin (show (t,α)∈K from h)⟩
    · exact ⟨1,zero_lt_one,fun t α h=>(hK ⟨(t,α),h⟩).elim⟩
  choose c hc using hex
  let S := Finset.univ.image (fun p : (n : Fin (N+1)) × Fin (n.val+1)=>c p.1 p.2)
  let T := insert 1 S
  have hT : T.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨T.min' hT,?_,Finset.min'_le T 1 (Finset.mem_insert_self _ _),?_⟩
  · have hmem:=Finset.min'_mem T hT
    rcases Finset.mem_insert.mp hmem with h|h
    · rw [h]; exact zero_lt_one
    · obtain ⟨p,-,hp⟩:=Finset.mem_image.mp h
      rw [←hp]; exact (hc p.1 p.2).1
  · intro n hn t α h i hi
    let nn : Fin (N+1) := ⟨n,by omega⟩
    let ii : Fin (nn.val+1) := ⟨i,by change i<n+1; omega⟩
    exact (Finset.min'_le T (c nn ii)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨nn,ii⟩,Finset.mem_univ _,rfl⟩))).trans
        ((hc nn ii).2 t α h)
end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

theorem actual_open_fan_sectorData {n : ℕ} (hn : 0<n) (r : ℝ) (s α : ℕ → ℝ)
    (hr : 0<r) (hs : ∀ i,0<s i) (hα : ∀ i,i<n → α i∈Ioo (0:ℝ) Real.pi)
    (hsum : ∑ i∈Finset.range n,α i=Real.pi/3) (hs0 : s 0=r) (hsn : s n=r)
    (hcos : ∀ i,i<n →2*(r+s i)*(r+s (i+1))*Real.cos (α i)=
      (r+s i)^2+(r+s (i+1))^2-(s i+s (i+1))^2)
    (A : ℂ) (B : ℕ → ℂ)
    (hAB : ∀ i,i≤n →dist A (B i)=r+s i)
    (hBC : ∀ i,i<n →dist (B i) (B (i+1))=s i+s (i+1))
    (hop : ∀ i,i+1<n → orientedArea A (B (i+1)) (B i)*
      orientedArea A (B (i+1)) (B (i+2))<0)
    (hdis : ∀ i,i≤n →∀ j,j≤n →i≠j →s i+s j≤dist (B i) (B j)) :
    ∃ t β : ℕ → ℝ,SectorRingData n t β ∧ ∀ i≤n,t i=s i/(r+s i) := by
  let L : ℕ → ℝ := fun k=>r+s k
  let d : ℕ → ℝ := fun k=>s k+s (k+1)
  obtain ⟨e,_heA,heB⟩ := open_fan_global_frame n hn L α d
    (fun k _hk=>add_pos hr (hs _)) (fun k _hk=>add_pos (hs _) (hs _)) hα hcos A B hAB hBC hop
  let t : ℕ → ℝ := fun k=>s (min k n)/(r+s (min k n))
  let β : ℕ → ℝ := fun k=>∑ j∈Finset.range (min k n),α j
  have hb (k : ℕ) : β k∈Icc (0:ℝ) Real.pi := by
    have hsmall : min k n≤n := min_le_right _ _
    have hle : β k≤Real.pi/3 := by
      rw [←hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsmall)
        (fun j hj _=>(hα j (Finset.mem_range.mp hj)).1.le)
    refine ⟨Finset.sum_nonneg (fun j hj=>(hα j (lt_of_lt_of_le (Finset.mem_range.mp hj) hsmall)).1.le),?_⟩
    linarith [Real.pi_pos]
  refine ⟨t,β,⟨fun k=>⟨(radius_fraction_mem hr (hs _)).1.le,(radius_fraction_mem hr (hs _)).2.le⟩,
    hb,?_,?_,by simp [β],by simpa [β] using hsum,?_,?_⟩,fun i hi=>by simp only [t,min_eq_left hi]⟩
  · simp only [t,zero_min,hs0]
    field_simp
    ring
  · simp only [t,min_self,hsn]
    field_simp
    ring
  · intro k hk
    dsimp [β]
    rw [min_eq_left (show k+1≤n by omega),min_eq_left hk.le,Finset.sum_range_succ]
    congr 1
    simpa only [t,min_eq_left hk.le,min_eq_left (show k+1≤n by omega)] using
      tangent_petal_angle hr (hs k) (hs (k+1)) (hα k hk) (hcos k hk)
  · intro i hi j hj hij
    have hsq := fanRay_dist_sq_pair L α i j
    rw [←heB i hi,←heB j hj,e.dist_eq] at hsq
    have H := tangent_nonoverlap_cosine hr (hs i) (hs j) (hdis i hi j hj hij) hsq
    simpa only [β,t,min_eq_left hi,min_eq_left hj] using H
end CannonPackingGeometry

end
end
end
end

end OAI
