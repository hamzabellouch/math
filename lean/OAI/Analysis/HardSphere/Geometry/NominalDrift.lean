import Mathlib
import OAI.Analysis.HardSphere.Geometry.TorusBall
import OAI.Analysis.HardSphere.Geometry.RadiusPotential

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

def nominalDrift (n : ℕ) (Δ : ℤ) (j : ℕ) : ℤ := ((j:ℤ)*Δ)/(n:ℤ)

lemma nominalDrift_step (n : ℕ) (hn : 0<n) (Δ : ℤ) (hΔ : |Δ|≤2*n) (j : ℕ) :
    |nominalDrift n Δ (j+1)-nominalDrift n Δ j|≤2 := by
  have hn' : 0<(n:ℤ) := by exact_mod_cast hn
  have hn0 := ne_of_gt hn'
  obtain ⟨hlo,hhi⟩ := abs_le.mp hΔ
  have hu := Int.ediv_le_ediv hn' (show ((j+1:ℕ):ℤ)*Δ≤(j:ℤ)*Δ+2*(n:ℤ) by push_cast; nlinarith)
  have hl := Int.ediv_le_ediv hn' (show (j:ℤ)*Δ≤((j+1:ℕ):ℤ)*Δ+2*(n:ℤ) by push_cast; nlinarith)
  rw [Int.add_mul_ediv_right _ _ hn0] at hu hl
  push_cast at hu hl
  exact abs_le.mpr ⟨by dsimp [nominalDrift]; omega,by dsimp [nominalDrift]; omega⟩

lemma nominalDrift_lipschitz (n : ℕ) (hn : 0<n) (Δ : ℤ) (hΔ : |Δ|≤2*n) (i j : ℕ) :
    |nominalDrift n Δ i-nominalDrift n Δ j|≤2*|(i:ℤ)-j| :=
  integer_step_lipschitz _ (max i j) 2 (fun k _ ↦ nominalDrift_step n hn Δ hΔ k)
    (le_max_left _ _) (le_max_right _ _)

def nominalVertices (m n : ℕ) (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : PairNoise m)
    (j : Fin (n+1)) : Vertex :=
  v + ![(j.val:ℤ), nominalDrift n Δ₂ j.val+walk m w.1 (min j.val (n-j.val)),
    nominalDrift n Δ₃ j.val+walk m w.2 (min j.val (n-j.val))]

lemma nominal_first (m n : ℕ) (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : PairNoise m) (j : Fin (n+1)) :
    nominalVertices m n v Δ₂ Δ₃ w j 0=v 0+j.val := rfl

lemma nominal_initial (m n : ℕ) (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : PairNoise m) :
    nominalVertices m n v Δ₂ Δ₃ w 0=v := by
  ext k
  fin_cases k <;> simp [nominalVertices,nominalDrift]

lemma nominal_final (m n : ℕ) (hn : 0<n) (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : PairNoise m) :
    nominalVertices m n v Δ₂ Δ₃ w (Fin.last n)=v+![(n:ℤ),Δ₂,Δ₃] := by
  have hn0 : (n:ℤ)≠0 := by omega
  ext k
  fin_cases k <;> simp [nominalVertices,nominalDrift,Int.mul_ediv_cancel_left _ hn0]

lemma nominal_speed (m n : ℕ) (hn : 0<n) (ht : n/2≤3^m)
    (v : Vertex) (Δ₂ Δ₃ : ℤ) (h₂ : |Δ₂|≤2*n) (h₃ : |Δ₃|≤2*n) (w : PairNoise m)
    (i j : Fin (n+1)) (k : Fin 3) :
    |nominalVertices m n v Δ₂ Δ₃ w i k-nominalVertices m n v Δ₂ Δ₃ w j k|≤3*|(i.val:ℤ)-j.val| := by
  have hfold (s : Fin (n+1)) : min s.val (n-s.val)≤3^m := by
    have hs := s.isLt
    omega
  have hwalk (r : TreeNoise m) :
      |walk m r (min i.val (n-i.val))-walk m r (min j.val (n-j.val))|≤|(i.val:ℤ)-j.val| :=
    (walk_lipschitz m r (hfold i) (hfold j)).trans (folded_index_lipschitz n i j)
  have htrans (Δ : ℤ) (hΔ : |Δ|≤2*n) (r : TreeNoise m) :
      |(nominalDrift n Δ i.val+walk m r (min i.val (n-i.val)))-
        (nominalDrift n Δ j.val+walk m r (min j.val (n-j.val)))|≤3*|(i.val:ℤ)-j.val| := by
    calc
      _ = |(nominalDrift n Δ i.val-nominalDrift n Δ j.val)+
        (walk m r (min i.val (n-i.val))-walk m r (min j.val (n-j.val)))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2*|(i.val:ℤ)-j.val|+|(i.val:ℤ)-j.val| :=
        add_le_add (nominalDrift_lipschitz n hn Δ hΔ _ _) (hwalk r)
      _ = _ := by ring
  fin_cases k
  · have h := abs_nonneg ((i.val:ℤ)-j.val)
    simpa [nominalVertices] using (show |(i.val:ℤ)-j.val|≤3*|(i.val:ℤ)-j.val| by omega)
  · simpa [nominalVertices] using htrans Δ₂ h₂ w.1
  · simpa [nominalVertices] using htrans Δ₃ h₃ w.2

def firstPathNoise {m : ℕ} (w : FourNoise m) : PairNoise m := (w.1.1,w.2.1)
def secondPathNoise {m : ℕ} (w : FourNoise m) : PairNoise m := (w.1.2,w.2.2)

lemma nominal_difference (m n : ℕ) (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : FourNoise m) (j : Fin (n+1)) :
    nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w) j-
      nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w) j =
      ![0,(differenceAt m (min j.val (n-j.val)) w).1,(differenceAt m (min j.val (n-j.val)) w).2] := by
  ext k
  fin_cases k <;> simp [nominalVertices,firstPathNoise,secondPathNoise,differenceAt,pairDifference]

def nominalCover {n : ℕ} (U : Fin (n+1) → Vertex) : Finset Vertex :=
  Finset.univ.biUnion fun i ↦ (torusOffsets 3).image (fun d ↦ U i+d)

lemma mem_nominalCover {n : ℕ} (U : Fin (n+1) → Vertex) (x : Vertex) :
    x∈nominalCover U ↔ ∃ i, ∀ k, |x k-U i k|≤3 := by
  constructor
  · intro hx
    obtain ⟨i,_,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨i,?_⟩
    simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,Pi.add_apply,
      add_sub_cancel_left,← abs_le,Nat.cast_ofNat] using hd
  · rintro ⟨i,hi⟩
    refine Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨x-U i,?_,?_⟩⟩
    · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,Pi.sub_apply,← abs_le,Nat.cast_ofNat] using hi
    · abel

lemma nominal_mem_cover {n : ℕ} (U : Fin (n+1) → Vertex) (i : Fin (n+1)) :
    U i∈nominalCover U := (mem_nominalCover U _).mpr ⟨i,by simp⟩

lemma nominalCover_projection {K n : ℕ} (U : Fin (n+1) → Vertex)
    {x : DiscreteTorus K} (hx : x∈(nominalCover U).image (torusProjection K)) :
    ∃ i, torusNear K 3 (torusProjection K (U i)) x := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i,hi⟩ := (mem_nominalCover U z).mp hz
  exact ⟨i,torusNear_symm (projection_near hi)⟩

lemma nominalCover_reach {n : ℕ} (U : Fin (n+1) → Vertex)
    (hspeed : ∀ i j k, |U i k-U j k|≤3*|(i.val:ℤ)-j.val|) :
    withinReach nearestStep (↑(nominalCover U)) (U 0) (U (Fin.last n)) := by
  have hpath : ∀ j : ℕ, (hj : j≤n) → withinReach nearestStep (↑(nominalCover U))
      (U 0) (U ⟨j,by omega⟩) := by
    intro j
    induction j with
    | zero => intro _; exact .refl
    | succ j ih =>
      intro hj
      have hj' : j≤n := by omega
      apply (ih hj').trans
      apply box_reach
      intro x hx
      apply (mem_nominalCover U x).mpr
      refine ⟨⟨j,by omega⟩,fun k ↦ ?_⟩
      have hs := hspeed ⟨j,by omega⟩ ⟨j+1,by omega⟩ k
      have hb : |U ⟨j,by omega⟩ k-U ⟨j+1,by omega⟩ k|≤3 := by
        simpa using hs
      have hbox := hx k
      obtain ⟨hl,hu⟩ := abs_le.mp hb
      exact abs_le.mpr ⟨by omega,by omega⟩
  exact hpath n le_rfl

lemma torusNear_least_iff {K R : ℕ} (x y : Vertex)
    (hsmall : ∀ k, 2*|x k-y k|≤K) :
    torusNear K R (torusProjection K x) (torusProjection K y) ↔ ∀ k, |x k-y k|≤R := by
  constructor
  · rintro ⟨d,hd,he⟩ k
    have hcast : (((y k-x k):ℤ):ZMod K)=(d k:ZMod K) := by
      have h := he k
      simp only [torusProjection,Int.cast_sub] at h ⊢
      linear_combination h
    rw [abs_sub_comm]
    exact (shortest_representative (by simpa only [abs_sub_comm] using hsmall k) hcast).trans (hd k)
  · exact projection_near

lemma pairDifference_abs_le (m t : ℕ) (ht : t≤3^m) (w : PairNoise m) :
    |pairDifference m t w|≤2*t := by
  exact (abs_sub_le (walk m w.1 t) 0 (walk m w.2 t)).trans (by
    simpa only [sub_zero,zero_sub,abs_neg,two_mul] using
      add_le_add (walk_abs_le m w.1 ht) (walk_abs_le m w.2 ht))

lemma nominal_near_iff {K n : ℕ} (m R : ℕ) (hnK : 2*n≤K) (ht : n/2≤3^m)
    (v : Vertex) (Δ₂ Δ₃ : ℤ) (w : FourNoise m) (j : Fin (n+1)) :
    torusNear K R (torusProjection K (nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w) j))
      (torusProjection K (nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w) j)) ↔
    differenceAt m (min j.val (n-j.val)) w ∈ square R := by
  let s := min j.val (n-j.val)
  have hj := j.isLt
  have hs : s≤n/2 := by dsimp [s]; omega
  have h₂ := pairDifference_abs_le m s (hs.trans ht) w.1
  have h₃ := pairDifference_abs_le m s (hs.trans ht) w.2
  dsimp only [s] at h₂ h₃
  have he := nominal_difference m n v Δ₂ Δ₃ w j
  have hsmall : ∀ k, 2*|nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w) j k-
      nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w) j k|≤K := by
    intro k
    have hk := congrFun he k
    simp only [Pi.sub_apply] at hk
    rw [hk]
    fin_cases k <;> simp [differenceAt] <;> omega
  rw [torusNear_least_iff _ _ hsmall]
  change (∀ k, |(nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w) j-
      nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w) j) k|≤(R:ℤ)) ↔ _
  rw [he]
  simp [square,Fin.forall_fin_succ,abs_le]

end HardSphere.Lattice

end

end OAI
