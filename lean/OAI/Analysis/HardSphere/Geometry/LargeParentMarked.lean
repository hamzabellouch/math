import Mathlib
import OAI.Analysis.HardSphere.Geometry.ParentStep

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

def LargeParentMarked {n K : ℕ} {L : Length} (q : ℕ) (h r : ℝ)
    (Y : Configuration n L) (B : Finset (DiscreteTorus K)) : Prop :=
  ∀ z ∈ bad h r Y,
    (¬ (liftedBadComponent (bad h r Y) z).Finite ∨
      ∃ C, IsBadComponent (bad h r Y) C ∧ z ∈ C ∧ ¬ SmallComponent h C) →
    torusProjection K (parent q z) ∈ B

theorem finite_components_of_no_large {n q K M : ℕ} [NeZero K] {L : Length} {h r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hMK : M ≤ K) (Y : Configuration n L)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q h r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M) :
    FiniteBadComponents (bad h r Y) := by
  intro z hz
  by_contra hinf
  let D := liftedBadComponent (bad h r Y) z
  have hzD : z ∈ D := liftedBadComponent_self hz
  have hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B := by
    intro w hw
    apply hmark w hw.2.1 (Or.inl ?_)
    rw [liftedBadComponent_eq_of_mem hw]
    exact hinf
  exact hinf (finite_of_parent_component_small hq hK
    (liftedBadComponent_connected _ _) hzD B hDB
    ((own_badComponent_card_lt _ B he (hDB z hzD)).trans_le hMK))

theorem large_finite_parent_lift {n q K M : ℕ} [NeZero K] {L : Length} {h r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hMK : M ≤ K) (Y : Configuration n L)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q h r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M)
    {C : Finset Vertex} (hC : IsBadComponent (bad h r Y) C)
    (hlarge : ¬SmallComponent h C) {z : Vertex} (hz : z ∈ C) :
    let S := badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))
    1 ≤ S.card ∧ S ∈ rootedAnimals (torusRangeGraph K 1)
      (torusProjection K (parent q z)) S.card ∧ S ⊆ B ∧
      ∀ w ∈ C, ∀ i, |parent q w i-parent q z i| ≤ (S.card:ℤ)-1 := by
  classical
  let v := torusProjection K (parent q z)
  let S := badComponent (torusRangeGraph K 1) B v
  have hDB : ∀ w ∈ C, torusProjection K (parent q w) ∈ B :=
    fun w hw ↦ hmark w (hC.subset hw) (Or.inr ⟨C,hC,hw,hlarge⟩)
  have hv : v ∈ B := hDB z hz
  have hvS : v ∈ S := mem_own_badComponent _ B hv
  have hc : 1 ≤ S.card := Finset.one_le_card.mpr ⟨v,hvS⟩
  obtain ⟨T,hT,_,hspan⟩ := parent_component_lift hq hK hC.connected hz B hDB
    ((own_badComponent_card_lt _ B he hv).trans_le hMK)
  refine ⟨hc,?_,badComponent_subset _ B v,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hvS,rfl,?_⟩
    intro w hw
    exact reachable_inside_component _ B ((mem_badComponent _ B v w).mp hw).2
  · intro w hw i
    exact hspan _ (hT w hw) _ (hT z hz) i

def rootBox (L : Length) (v : Vertex) (R : ℝ) : Set (Torus L) :=
  Set.univ.pi fun i ↦ Metric.closedBall (((v i : ℝ)+1/2 : ℝ) : AddCircle L.val) R

lemma volume_rootBox_le (L : Length) (v : Vertex) {R : ℝ} (hR : 0 ≤ R) :
    (volume : Measure (Torus L)) (rootBox L v R) ≤ ENNReal.ofReal ((2*R)^3) := by
  unfold rootBox
  rw [volume_pi_pi]
  simp only [AddCircle.volume_closedBall]
  calc
    _ ≤ ∏ _i : Fin 3, ENNReal.ofReal (2*R) := by
      exact Finset.prod_le_prod fun _ _ ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = _ := by simp [ENNReal.ofReal_pow (by positivity : 0 ≤ 2*R)]

lemma scaled_parent_bounds {q : ℕ} (hq : 0 < q) (z : Vertex) (i : Fin 3) :
    (parent q z i : ℝ) ≤ 1/(q:ℝ)*(z i : ℝ) ∧
    1/(q:ℝ)*((z i : ℝ)+1) ≤ (parent q z i : ℝ)+1 := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have he : (z i : ℝ) = (q:ℝ)*(parent q z i : ℝ)+((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod (z i) q).symm
  have hlo : (0:ℝ) ≤ ((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg (z i) hqz.ne'
  have hhi : ((z i % (q:ℤ) : ℤ) : ℝ)+1 ≤ q := by
    exact_mod_cast (show z i % (q:ℤ)+1 ≤ q by have := Int.emod_lt_of_pos (z i) hqz; omega)
  constructor
  · rw [one_div,←div_eq_inv_mul]
    apply (le_div_iff₀ hqr).mpr
    nlinarith
  · rw [one_div,←div_eq_inv_mul]
    apply (div_le_iff₀ hqr).mpr
    nlinarith

lemma filledRegion_subset_rootBox {L : Length} {q : ℕ} (hq : 0 < q)
    (C : Finset Vertex) (v : Vertex) {m : ℕ}
    (hspan : ∀ w ∈ C, ∀ i, |parent q w i-v i| ≤ (m:ℤ)) :
    filledRegion L (1/(q:ℝ)) C ⊆ rootBox L v (m+1) := by
  intro x hx
  obtain ⟨z,hz,ux,hux,rfl⟩ := Set.mem_iUnion₂.mp hx
  intro i _
  apply (coordinate_dist_lift_le L (ux i) ((v i : ℝ)+1/2)).trans
  apply abs_le.mpr
  obtain ⟨⟨cl,hcl,hclz⟩,⟨cu,hcu,hzcu⟩⟩ := fill_subset_coordinateBox C hz i
  have hbl := (scaled_parent_bounds hq cl i).1
  have hbu := (scaled_parent_bounds hq cu i).2
  have hsl : - (m:ℝ) ≤ (parent q cl i : ℝ)-(v i : ℝ) := by
    exact_mod_cast (abs_le.mp (hspan cl hcl i)).1
  have hsu : (parent q cu i : ℝ)-(v i : ℝ) ≤ (m:ℝ) := by
    exact_mod_cast (abs_le.mp (hspan cu hcu i)).2
  have hclz' : (cl i : ℝ) ≤ z i := by exact_mod_cast hclz
  have hzcu' : (z i : ℝ) ≤ cu i := by exact_mod_cast hzcu
  have hlo := hux.1 i
  have hhi := hux.2 i
  have hqnn : 0 ≤ 1/(q:ℝ) := by positivity
  constructor <;> dsimp [Point,liftedCube] at * <;> nlinarith

lemma coarseCenter_eq_of_projection {L : Length} {K : ℕ}
    (hLK : L.val=(K:ℝ)) {w z : Vertex}
    (he : torusProjection K w = torusProjection K z) :
    coarseCenter L w = coarseCenter L z := by
  ext j
  change (((w j : ℝ)+1/2 : ℝ) : AddCircle L.val) =
    (((z j : ℝ)+1/2 : ℝ) : AddCircle L.val)
  obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w j) (z j) K).mp (congrFun he j)
  have hkr : (z j : ℝ)-(w j : ℝ)=(K:ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hr : (z j : ℝ)+1/2=((w j : ℝ)+1/2)+(k:ℝ)*L.val := by
    rw [hLK]; linarith
  rw [hr]
  have hz : (((k:ℝ)*L.val:ℝ) : AddCircle L.val)=0 := by
    rw [←zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  simp only [AddCircle.coe_add,hz,add_zero]

lemma rootBox_eq_of_projection {L : Length} {K : ℕ}
    (hLK : L.val=(K:ℝ)) {w z : Vertex}
    (he : torusProjection K w = torusProjection K z) (R : ℝ) :
    rootBox L w R = rootBox L z R := by
  have hc := coarseCenter_eq_of_projection hLK he
  change (Set.univ.pi fun i ↦ Metric.closedBall (coarseCenter L w i) R) =
    (Set.univ.pi fun i ↦ Metric.closedBall (coarseCenter L z i) R)
  rw [hc]

def siteRep {K : ℕ} (v : DiscreteTorus K) : Vertex := fun i ↦ (v i).val

lemma siteRep_projection {K : ℕ} [NeZero K] (v : DiscreteTorus K) :
    torusProjection K (siteRep v)=v := by
  ext i
  change (((v i).val:ℤ):ZMod K)=v i
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

def siteCenter {K : ℕ} (L : Length) (v : DiscreteTorus K) : Torus L :=
  coarseCenter L (siteRep v)

def closeSet {n K : ℕ} [NeZero K] (L : Length) (s T : ℝ)
    (X : Configuration n L) : Finset (DiscreteTorus K) := by
  classical
  exact Finset.univ.filter fun v ↦ T ≤ ((pairCloseLabels L s (siteCenter L v) X).card:ℝ)

theorem actual_large_parent_marked {m n K : ℕ} [NeZero K] {L : Length} {r s D θ : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hrs : 6*r ≤ s) (hθ : θ*D ≤ 1/(1372*r))
    (e : Fin m ↪ Fin n) (X : Configuration n L) :
    LargeParentMarked (microPeriod r) (microMesh r) r (fun i ↦ X (e i))
      (closeSet (K := K) L s (θ*D) X) := by
  intro z hz hlarge
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have hc : siteCenter L (torusProjection K (parent (microPeriod r) z)) =
      coarseCenter L (parent (microPeriod r) z) :=
    coarseCenter_eq_of_projection hLK (siteRep_projection _)
  rw [hc]
  exact large_component_forces_close hr hrsmall hL hLK hrs hθ e X hz hlarge

def largeBoxUnion {K : ℕ} [NeZero K] (L : Length) (B : Finset (DiscreteTorus K)) : Set (Torus L) :=
  ⋃ m : ℕ, ⋃ v : DiscreteTorus K, ⋃ S ∈ rootedAnimals (torusRangeGraph K 1) v (m+1),
    ⋃ (_ : S ⊆ B), rootBox L (siteRep v) ((m:ℝ)+2)

theorem omitted_subset_small_and_boxes {n q K M : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hLK : L.val=(K:ℝ)) (hMK : M ≤ K)
    (Y : Configuration n L) (hY : Y ∈ allowed n L r)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q (1/(q:ℝ)) r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M) :
    omitted (1/(q:ℝ)) r Y ⊆ smallFills (1/(q:ℝ)) r Y ∪ largeBoxUnion L B := by
  intro x hx
  rcases hx with hex | ⟨C,hC,z,hz,hxz⟩
  · exact (hex.elim (fun h ↦ h hY) (fun h ↦ h
      (finite_components_of_no_large hq hK hMK Y B hmark he))).elim
  by_cases hsmall : SmallComponent (1/(q:ℝ)) C
  · exact Or.inl ⟨C,hC,hsmall,Set.mem_iUnion₂.mpr ⟨z,hz,hxz⟩⟩
  right
  obtain ⟨w,hw,_⟩ := fill_column_meets C hz 0
  let v := torusProjection K (parent q w)
  let S := badComponent (torusRangeGraph K 1) B v
  obtain ⟨hSpos,hSan,hSB,hspan⟩ := large_finite_parent_lift hq hK hMK Y B hmark he hC hsmall hw
  change 1 ≤ S.card at hSpos
  change S ∈ rootedAnimals (torusRangeGraph K 1) v S.card at hSan
  change S ⊆ B at hSB
  change ∀ u ∈ C, ∀ i, |parent q u i-parent q w i| ≤ (S.card:ℤ)-1 at hspan
  have hxbox : x ∈ rootBox L (parent q w) ((S.card:ℝ)+1) := by
    apply filledRegion_subset_rootBox hq C (parent q w) (m := S.card)
      (fun u hu i ↦ (hspan u hu i).trans (by omega))
    exact Set.mem_iUnion₂.mpr ⟨z,hz,hxz⟩
  have hrad : ((S.card-1:ℕ):ℝ)+2=(S.card:ℝ)+1 := by
    rw [Nat.cast_sub hSpos]; push_cast; ring
  change x ∈ ⋃ m : ℕ, ⋃ v : DiscreteTorus K, ⋃ S ∈ rootedAnimals (torusRangeGraph K 1) v (m+1),
    ⋃ (_ : S ⊆ B), rootBox L (siteRep v) ((m:ℝ)+2)
  refine Set.mem_iUnion.mpr ⟨S.card-1,Set.mem_iUnion.mpr ⟨v,
    Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨?_,Set.mem_iUnion.mpr ⟨hSB,?_⟩⟩⟩⟩⟩
  · simpa only [Nat.sub_add_cancel hSpos] using hSan
  · rw [hrad,rootBox_eq_of_projection hLK (siteRep_projection v)]
    exact hxbox

end HardSphere.BathSlice

end

end OAI
