import Mathlib
import OAI.Analysis.HardSphere.Conditioning.PairCloseLabels
import OAI.Analysis.HardSphere.Geometry.MicroPeriod
import OAI.Analysis.HardSphere.Geometry.BadGraph

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def animalFamily (G : SimpleGraph V) (m : ℕ) : Finset (Finset V) :=
  Finset.univ.biUnion (fun r : V ↦ rootedAnimals G r m)

lemma animalFamily_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (m : ℕ) :
    (animalFamily G m).card ≤ Fintype.card V * (2^Δ)^m := by
  calc
    _ ≤ ∑ r : V, (rootedAnimals G r m).card := Finset.card_biUnion_le
    _ ≤ ∑ _r : V, (2^Δ)^m := Finset.sum_le_sum fun r _ ↦ rootedAnimals_card_le G Δ hΔ r m
    _ = _ := by simp

lemma mem_animalFamily_card (G : SimpleGraph V) (m : ℕ) {F : Finset V}
    (hF : F∈animalFamily G m) : F.card=m := by
  obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hF
  exact (Finset.mem_filter.mp hr).2.2.1

def LargeBadComponent (G : SimpleGraph V) (B : Finset V) (m : ℕ) : Prop :=
  ∃ C∈badComponents G B, m≤C.card

lemma largeBadComponent_contains_animal (G : SimpleGraph V) (B : Finset V)
    (m : ℕ) (hm : 1 ≤ m) (hB : LargeBadComponent G B m) :
    ∃ F∈animalFamily G m, F⊆B := by
  obtain ⟨C,hC,hmC⟩ := hB
  have hc := badComponents_candidate G B hC
  simp only [candidateSets,Finset.mem_filter,Finset.mem_univ,true_and] at hc
  obtain ⟨r,hr⟩ := hc.1
  obtain ⟨F,hFC,hF⟩ := exists_rooted_subanimal G C hr (hc.2 r hr) m hm hmC
  exact ⟨F,Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hF⟩,
    hFC.trans (badComponents_subset G B hC)⟩

theorem largeBadComponent_probability (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : PMF (Finset V)) (p : ℝ≥0∞)
    (hbad : JointBadLaw μ p) (m : ℕ) (hm : 1 ≤ m) :
    (∑' B, if LargeBadComponent G B m then μ B else 0) ≤
      (Fintype.card V : ℝ≥0∞) * (((2^Δ:ℕ):ℝ≥0∞)*p)^m := by
  have hpoint (B : Finset V) :
      (if LargeBadComponent G B m then μ B else 0) ≤
      ∑ F∈animalFamily G m, if F⊆B then μ B else 0 := by
    by_cases h : LargeBadComponent G B m
    · obtain ⟨F,hF,hFB⟩ := largeBadComponent_contains_animal G B m hm h
      rw [ite_eq_left h]
      calc
        μ B = if F⊆B then μ B else 0 := (ite_eq_left hFB).symm
        _ ≤ _ := Finset.single_le_sum (f := fun F : Finset V ↦ if F ⊆ B then μ B else 0)
          (fun _ _ ↦ zero_le) hF
    · rw [ite_eq_right h]
      exact zero_le
  calc
    _ ≤ ∑' B, ∑ F∈animalFamily G m, if F⊆B then μ B else 0 :=
      ENNReal.tsum_le_tsum hpoint
    _ = ∑ F∈animalFamily G m, ∑' B, if F⊆B then μ B else 0 := by
      simp only [tsum_fintype]
      exact Finset.sum_comm
    _ ≤ ∑ _F∈animalFamily G m, p^m := by
      apply Finset.sum_le_sum
      intro F hF
      simpa only [mem_animalFamily_card G m hF] using hbad F
    _ = ((animalFamily G m).card:ℝ≥0∞)*p^m := by simp
    _ ≤ ((Fintype.card V*(2^Δ)^m:ℕ):ℝ≥0∞)*p^m := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast animalFamily_card_le G Δ hΔ m
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

def parent (q : ℕ) (z : Vertex) : Vertex := fun i ↦ z i / (q : ℤ)

def coarseCenter (L : Length) (v : Vertex) : Torus L :=
  liftPoint L (fun i ↦ (v i : ℝ)+1/2)

lemma gridCorner_dist_parent {L : Length} {q : ℕ} (hq : 0 < q) (z : Vertex) :
    torusDistance L (gridCorner L (1/(q:ℝ)) z) (coarseCenter L (parent q z)) ≤ 2 := by
  change torusDistance L (liftPoint L _) (liftPoint L _) ≤ 2
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have he (i : Fin 3) : (z i : ℝ) = (q:ℝ)*(parent q z i : ℝ)+((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod (z i) q).symm
  have hlo (i : Fin 3) : (0:ℝ) ≤ ((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg (z i) hqz.ne'
  have hhi (i : Fin 3) : ((z i % (q:ℤ) : ℤ) : ℝ) < q := by
    exact_mod_cast Int.emod_lt_of_pos (z i) hqz
  have hbound (i : Fin 3) : |1/(q:ℝ)*(z i : ℝ)-1/2 - ((parent q z i : ℝ)+1/2)| ≤ 1 := by
    apply abs_le.mpr
    have hmul : (q:ℝ)*(1/(q:ℝ)*(z i : ℝ)- (parent q z i : ℝ)) = ((z i % (q:ℤ) : ℤ) : ℝ) := by
      rw [mul_sub]; field_simp; nlinarith [he i]
    constructor <;> nlinarith [hlo i,hhi i]
  simpa only [mul_one] using torusDistance_lift_le_two (by norm_num : (0:ℝ)≤1) hbound

lemma witnesses_pairClose {m : ℕ} {L : Length} {r s : ℝ} {Y : Configuration m L}
    {z : Vertex} {q : ℕ} (hq : 0 < q) (hrs : 6*r ≤ s) {A : Finset (Fin m)}
    (hnear : ∀ i ∈ A, torusDistance L (Y i) (gridCorner L (1/(q:ℝ)) z) ≤ 1)
    (hpartner : ∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) :
    A ⊆ pairCloseLabels L s (coarseCenter L (parent q z)) Y := by
  classical
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,?_,?_⟩
  · have hc := gridCorner_dist_parent (L := L) hq z
    have ht := torusDistance_triangle' L (Y i) (gridCorner L (1/(q:ℝ)) z)
      (coarseCenter L (parent q z))
    have hn := hnear i hi
    linarith
  · obtain ⟨j,_,hji,hj⟩ := hpartner i hi
    exact ⟨j,hji,hj.trans hrs⟩

lemma pairClose_card_mono {m n : ℕ} (L : Length) (s : ℝ) (v : Torus L)
    (e : Fin m ↪ Fin n) (X : Configuration n L) :
    (pairCloseLabels L s v (fun i ↦ X (e i))).card ≤ (pairCloseLabels L s v X).card := by
  classical
  have hs : (pairCloseLabels L s v (fun i ↦ X (e i))).map e ⊆ pairCloseLabels L s v X := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨_,hv,k,hkj,hk⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hv,e k,fun he ↦ hkj (e.injective he),hk⟩
  simpa only [Finset.card_map] using Finset.card_le_card hs

theorem large_component_forces_close {m n K : ℕ} {L : Length} {r s D θ : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hrs : 6*r ≤ s) (hθ : θ*D ≤ 1/(1372*r))
    (e : Fin m ↪ Fin n) (X : Configuration n L) {z : Vertex}
    (hz : z ∈ bad (microMesh r) r (fun i ↦ X (e i)))
    (hlarge : ¬ (liftedBadComponent (bad (microMesh r) r (fun i ↦ X (e i))) z).Finite ∨
      ∃ C, IsBadComponent (bad (microMesh r) r (fun i ↦ X (e i))) C ∧ z ∈ C ∧
        ¬ SmallComponent (microMesh r) C) :
    θ*D ≤ ((pairCloseLabels L s (coarseCenter L (parent (microPeriod r) z)) X).card:ℝ) := by
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨hh,hhr,hrh⟩ := microMesh_bounds hr hr1
  have hq : (microPeriod r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast microPeriod_pos hr)
  have hperiod : L.val = microMesh r * ((K*microPeriod r : ℕ) : ℝ) := by
    rw [hLK,Nat.cast_mul,microMesh]; field_simp
  obtain ⟨A,hA,hnear,hpartner⟩ := large_component_witnesses hh hhr hrh hrsmall
    hperiod hL (fun i ↦ X (e i)) hz hlarge
  have hsub := witnesses_pairClose (microPeriod_pos hr) hrs hnear hpartner
  have hcard : (A.card:ℝ) ≤ ((pairCloseLabels L s
      (coarseCenter L (parent (microPeriod r) z)) X).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (pairClose_card_mono L s _ e X)
  apply hθ.trans
  have hmul := mul_le_mul_of_nonneg_left hcard hr.le
  apply (div_le_iff₀ (by positivity : (0:ℝ)<1372*r)).mpr
  nlinarith

end HardSphere.BathSlice

end

end OAI
