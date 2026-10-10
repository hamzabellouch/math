import Mathlib
import OAI.Analysis.HardSphere.Geometry.EndpointsExterior

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma shortest_representative {K : ℕ} {h d : ℤ}
    (hh : 2*|h|≤K) (he : (h:ZMod K)=(d:ZMod K)) : |h|≤|d| := by
  by_contra hn
  have hd : |d| < |h| := by omega
  have hab : |h-d| ≤ |h|+|d| := by simpa using abs_sub_le h 0 d
  have hsmall : |h-d|<(K:ℤ) := by omega
  have hz := small_multiple_zero (show ((h-d:ℤ):ZMod K)=0 by simp only [Int.cast_sub,he,sub_self]) hsmall
  have heq : h=d := sub_eq_zero.mp hz
  rw [heq] at hd
  exact lt_irrefl _ hd

lemma projection_near {K R : ℕ} {x y : Vertex} (h : ∀ i, |x i-y i|≤R) :
    torusNear K R (torusProjection K x) (torusProjection K y) := by
  refine ⟨y-x,fun i ↦ ?_,fun i ↦ ?_⟩
  · simpa only [Pi.sub_apply,abs_sub_comm] using h i
  · simp only [torusProjection,Pi.sub_apply,Int.cast_sub]
    abel

lemma nominal_index_bound {K n D : ℕ} (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    {i j : Fin (n+1)} (hnear : torusNear K D (torusProjection K (U i)) (torusProjection K (U' j))) :
    |(i.val:ℤ)-j.val|≤D := by
  obtain ⟨d,hd,he⟩ := hnear
  have h0 := he 0
  simp only [torusProjection,hfirst,hfirst',Int.cast_add,Int.cast_natCast] at h0
  have heq : (((j.val:ℤ)-i.val:ℤ):ZMod K)=(d 0:ZMod K) := by push_cast; linear_combination h0
  have hsmall : 2*|(j.val:ℤ)-i.val|≤(K:ℤ) := by
    have hi := i.isLt
    have hj := j.isLt
    have hb : |(j.val:ℤ)-i.val|≤n := abs_le.mpr ⟨by omega,by omega⟩
    omega
  rw [abs_sub_comm]
  exact (shortest_representative hsmall heq).trans (hd 0)

lemma nominal_equal_index {K n D : ℕ} (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    {i j : Fin (n+1)} (hnear : torusNear K D (torusProjection K (U i)) (torusProjection K (U' j))) :
    torusNear K (4*D) (torusProjection K (U i)) (torusProjection K (U' i)) := by
  have hij := nominal_index_bound hnK U U' b hfirst hfirst' hnear
  have hnear' : torusNear K (3*D) (torusProjection K (U' j)) (torusProjection K (U' i)) := by
    apply projection_near
    intro k
    have h := hspeed j i k
    rw [abs_sub_comm (j.val:ℤ) (i.val:ℤ)] at h
    push_cast
    omega
  convert torusNear_add hnear hnear' using 1; omega

def torusBall {K : ℕ} [NeZero K] (R : ℕ) (x : DiscreteTorus K) : Finset (DiscreteTorus K) :=
  Finset.univ.filter (torusNear K R x)

lemma mem_torusBall {K : ℕ} [NeZero K] (R : ℕ) (x y : DiscreteTorus K) :
    y∈torusBall R x ↔ torusNear K R x y := by simp [torusBall]

theorem nominal_encounter_bound {K n : ℕ} [NeZero K] (R : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x) :
    (encounterSet (torusNear K R) Γ Γ').card ≤
      (343*(2*R+1)^3)*
      (Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))).card := by
  let I := Finset.univ.filter (fun i ↦ torusNear K (4*(R+6))
        (torusProjection K (U i)) (torusProjection K (U' i)))
  have hsub : encounterSet (torusNear K R) Γ Γ' ⊆
      I.biUnion (fun i ↦ encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ') := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet _ _ _ _ _).mp hxy
    obtain ⟨i,hi⟩ := hcover x hx
    obtain ⟨j,hj⟩ := hcover' y hy
    have hnear : torusNear K (R+6) (torusProjection K (U i)) (torusProjection K (U' j)) := by
      convert torusNear_add (torusNear_add hi he) (torusNear_symm hj) using 1; omega
    have hiI : i∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      nominal_equal_index hnK U U' b hfirst hfirst' hspeed hnear⟩
    exact Finset.mem_biUnion.mpr ⟨i,hiI,(mem_encounterSet _ _ _ _ _).mpr
      ⟨(mem_torusBall _ _ _).mpr hi,hy,he⟩⟩
  calc
    _ ≤ (I.biUnion (fun i ↦ encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ')).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i∈I, (encounterSet (torusNear K R) (torusBall 3 (torusProjection K (U i))) Γ').card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i∈I, 343*(2*R+1)^3 := by
      apply Finset.sum_le_sum
      intro i _
      exact (encounterSet_card_le _ _ (torusNear_ball_card R) _ _).trans
        (Nat.mul_le_mul_right _ (by simpa [torusBall] using torusNear_ball_card 3 (torusProjection K (U i))))
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul]; rw [Nat.mul_comm]

lemma candidate_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {F : Finset V} (hF : F∈candidateSets G) : F.Nonempty :=
  (Finset.mem_filter.mp hF).2.1

lemma candidate_reach {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {F : Finset V} (hF : F∈candidateSets G)
    {x y : V} (hx : x∈F) (hy : y∈F) : (badGraph G F).Reachable x y :=
  (Finset.mem_filter.mp hF).2.2 x hx y hy

lemma candidate_diameter {K : ℕ} [NeZero K] (a : ℕ) {F : Finset (DiscreteTorus K)}
    (hF : F∈candidateSets (torusRangeGraph K a)) {x y : DiscreteTorus K}
    (hx : x∈F) (hy : y∈F) : torusNear K (a*(F.card-1)) x y := by
  obtain ⟨w⟩ := bad_reachable_induce _ F hx hy (candidate_reach _ hF hx hy)
  let p := w.toPath
  have hwalk : ∀ {u v : (↑F : Set (DiscreteTorus K))}
      (w : ((torusRangeGraph K a).induce (↑F)).Walk u v), torusNear K (a*w.length) u.val v.val := by
    intro u v w
    induction w with
    | nil => exact torusNear_refl _ _ _
    | @cons u v w he p ih =>
      simpa only [SimpleGraph.Walk.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        torusNear_add (show torusNear K a u.val v.val from he.2) ih
  have hlen : p.val.length<F.card := by simpa using p.isPath.length_lt
  exact torusNear_mono (Nat.mul_le_mul_left _ (by omega)) (hwalk p.val)

lemma candidate_contact_root {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    {F : Finset (DiscreteTorus K)} (hF : F∈candidateSets (torusRangeGraph K a))
    (hcontact : torusContact a F Γ) (hcontact' : torusContact a F Γ') :
    ∃ i, torusNear K ((12*a+24)*F.card) (torusProjection K (U i)) (torusProjection K (U' i)) ∧
      ∃ c∈torusBall (a+3) (torusProjection K (U i)), F∈rootedAnimals (torusRangeGraph K a) c F.card := by
  obtain ⟨c,hc,x,hx,hcx⟩ := hcontact
  obtain ⟨d,hd,y,hy,hdy⟩ := hcontact'
  obtain ⟨i,hi⟩ := hcover x hx
  obtain ⟨j,hj⟩ := hcover' y hy
  have hic : torusNear K (a+3) (torusProjection K (U i)) c := by
    convert torusNear_add hi (torusNear_symm hcx) using 1; omega
  have hdj : torusNear K (a+3) d (torusProjection K (U' j)) := torusNear_add hdy (torusNear_symm hj)
  have hm : 1≤F.card := Finset.card_pos.mpr (candidate_nonempty _ hF)
  have hnear : torusNear K ((3*a+6)*F.card) (torusProjection K (U i)) (torusProjection K (U' j)) := by
    apply torusNear_mono (show (a+3)+a*(F.card-1)+(a+3)≤(3*a+6)*F.card from ?_)
      (torusNear_add (torusNear_add hic (candidate_diameter a hF hc hd)) hdj)
    have h1 := Nat.mul_le_mul_left a (show F.card-1≤F.card by omega)
    have h2 := Nat.mul_le_mul_left (2*a+6) hm
    nlinarith
  refine ⟨i,?_,c,(mem_torusBall _ _ _).mpr hic,?_⟩
  · convert nominal_equal_index hnK U U' b hfirst hfirst' hspeed hnear using 1; ring
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc,rfl,fun y hy ↦ candidate_reach _ hF hc hy⟩

theorem contact_candidates_card {K n : ℕ} [NeZero K] (a : ℕ) (hnK : 2*n≤K)
    (U U' : Fin (n+1) → Vertex) (b : ℤ)
    (hfirst : ∀ i, U i 0=b+i.val) (hfirst' : ∀ i, U' i 0=b+i.val)
    (hspeed : ∀ i j k, |U' i k-U' j k|≤3*|(i.val:ℤ)-j.val|)
    (Γ Γ' : Finset (DiscreteTorus K))
    (hcover : ∀ x∈Γ, ∃ i, torusNear K 3 (torusProjection K (U i)) x)
    (hcover' : ∀ x∈Γ', ∃ i, torusNear K 3 (torusProjection K (U' i)) x)
    (m : ℕ) (hm : 1 ≤ m) :
    ((candidateSets (torusRangeGraph K a)).filter (fun F ↦ F.card=m ∧
      torusContact a F Γ ∧ torusContact a F Γ')).card ≤
      ((2*(a+3)+1)^3*2^((2*a+1)^3))^m *
      (Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*m)
        (torusProjection K (U i)) (torusProjection K (U' i)))).card := by
  let I := Finset.univ.filter (fun i ↦ torusNear K ((12*a+24)*m)
        (torusProjection K (U i)) (torusProjection K (U' i)))
  let G := torusRangeGraph K a
  have hsub : (candidateSets G).filter (fun F ↦ F.card=m ∧ torusContact a F Γ ∧ torusContact a F Γ') ⊆
      I.biUnion (fun i ↦ (torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m)) := by
    intro F hF
    obtain ⟨hFc,hmF,hFΓ,hFΓ'⟩ := Finset.mem_filter.mp hF
    obtain ⟨i,hi,c,hc,hroot⟩ := candidate_contact_root a hnK U U' b hfirst hfirst' hspeed Γ Γ' hcover hcover' hFc hFΓ hFΓ'
    rw [hmF] at hi hroot
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
      Finset.mem_biUnion.mpr ⟨c,hc,hroot⟩⟩
  have hp : (2*(a+3)+1)^3≤((2*(a+3)+1)^3)^m := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (I.biUnion (fun i ↦ (torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i∈I, ((torusBall (a+3) (torusProjection K (U i))).biUnion (fun c ↦ rootedAnimals G c m)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i∈I, ((2*(a+3)+1)^3*2^((2*a+1)^3))^m := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ c∈torusBall (a+3) (torusProjection K (U i)), (rootedAnimals G c m).card := Finset.card_biUnion_le
        _ ≤ ∑ _c∈torusBall (a+3) (torusProjection K (U i)), (2^((2*a+1)^3))^m :=
          Finset.sum_le_sum fun _ _ ↦ rootedAnimals_card_le G _ (torusRange_degree a) _ _
        _ = (torusBall (a+3) (torusProjection K (U i))).card*(2^((2*a+1)^3))^m := by simp
        _ ≤ (2*(a+3)+1)^3*(2^((2*a+1)^3))^m :=
          Nat.mul_le_mul_right _ (torusNear_ball_card _ _)
        _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_right _ hp
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul]; rw [Nat.mul_comm]

end HardSphere.Lattice

end

end OAI
