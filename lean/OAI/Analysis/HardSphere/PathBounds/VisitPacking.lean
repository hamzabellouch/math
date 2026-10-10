import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ReverseConfigurationPath
import OAI.Analysis.HardSphere.Bridges.NormalizedPrefix
import OAI.Analysis.HardSphere.Geometry.LargeParentMarked

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital

def packingBox (c : Fin 3 → ℝ) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊c j - 1/2⌋ - 14) (fun j ↦ ⌊c j - 1/2⌋ + 14)

lemma card_packingBox (c : Fin 3 → ℝ) : (packingBox c).card=29^3 := by
  unfold packingBox
  rw [Pi.card_Icc]
  have hc (j : Fin 3) : (Finset.Icc (⌊c j-1/2⌋-14) (⌊c j-1/2⌋+14)).card=29 := by
    rw [Int.card_Icc]
    omega
  simp only [hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma site_packing_witness {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (c : Fin 3 → ℝ) (v : DiscreteTorus K)
    (hv : ∀ j, dist (siteCenter L v j) ((c j:ℝ):AddCircle L.val)≤13) :
    ∃ z ∈ packingBox c, torusProjection K z=v := by
  let k : Vertex := fun j ↦ round (L.val⁻¹*((((v j).val:ℝ)+1/2)-c j))
  let z : Vertex := fun j ↦ ((v j).val:ℤ)-k j*(K:ℤ)
  refine ⟨z,?_,?_⟩
  · apply Finset.mem_Icc.mpr
    have hz (j : Fin 3) : ⌊c j-1/2⌋-14 ≤ z j ∧ z j ≤ ⌊c j-1/2⌋+14 := by
      have hd := hv j
      change dist ((((v j).val:ℝ)+1/2:ℝ):AddCircle L.val) ((c j:ℝ):AddCircle L.val)≤13 at hd
      rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq] at hd
      have hd' : |(z j:ℝ)-(c j-1/2)|≤13 := by
        convert hd using 1
        dsimp [z,k]
        push_cast
        rw [hL]
        ring_nf
      have hl := Int.floor_le (c j-1/2)
      have hu := Int.lt_floor_add_one (c j-1/2)
      obtain ⟨h₁,h₂⟩ := abs_le.mp hd'
      constructor <;> (apply (Int.cast_le (R := ℝ)).mp; push_cast; linarith)
    exact ⟨fun j ↦ (hz j).1,fun j ↦ (hz j).2⟩
  · ext j
    simp [torusProjection,z]

lemma card_near_sites_le {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (x : Torus L) (A : Finset (DiscreteTorus K))
    (hA : ∀ v∈A, ∀ j, dist (siteCenter L v j) (x j)≤13) : A.card≤29^3 := by
  classical
  let c : Fin 3 → ℝ := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  have hc (j : Fin 3) : ((c j:ℝ):AddCircle L.val)=x j := AddCircle.coe_equivIco
  have hsub : A ⊆ (packingBox c).image (torusProjection K) := by
    intro v hv
    obtain ⟨z,hz,he⟩ := site_packing_witness L hL c v (fun j ↦ by rw [hc]; exact hA v hv j)
    exact Finset.mem_image.mpr ⟨z,hz,he⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (le_of_eq (card_packingBox c)))
end HardSphere.FreeVisits

namespace HardSphere
open MeasureTheory Wiener Set
attribute [local irreducible] torusDistance

def pathVisitsBall {n : ℕ} (L : Length) (R : ℝ) (v : Torus L)
    (i : Fin n) (ω : ConfigurationPath n L) : Prop :=
  ∃ q : Time, torusDistance L (ω q i) v ≤ R

lemma pathVisitsBall_isClosed {n : ℕ} (L : Length) (R : ℝ) (v : Torus L) (i : Fin n) :
    IsClosed {ω : ConfigurationPath n L | pathVisitsBall L R v i ω} := by
  have hc : Continuous (fun p : ConfigurationPath n L × Time ↦ torusDistance L (p.1 p.2 i) v) := by
    have he : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2 i) :=
      (continuous_apply i).comp (continuous_eval : Continuous (fun p : ConfigurationPath n L × Time ↦ p.1 p.2))
    exact (continuous_torusDistance L).comp (he.prodMk continuous_const)
  have hs := isClosedMap_fst_of_compactSpace
    {p : ConfigurationPath n L × Time | torusDistance L (p.1 p.2 i) v ≤ R}
    (isClosed_le hc continuous_const)
  convert hs using 1
  ext ω
  simp only [pathVisitsBall,Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨ω,q,hq,rfl⟩
  · rintro ⟨ω',q,hq,rfl⟩
    exact ⟨q,hq⟩

@[simp] lemma pathVisitsBall_reverse {n : ℕ} (L : Length) (R : ℝ) (v : Torus L)
    (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitsBall L R v i (reverseConfigurationPath n L ω) ↔ pathVisitsBall L R v i ω := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨reverseTime q,hq⟩
  · rintro ⟨q,hq⟩
    refine ⟨reverseTime q,?_⟩
    simpa only [reverseConfigurationPath_apply,reverseTime_reverse] using hq

def pathVisitedSites {S : Type*} {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L) : Finset S := by
  classical
  exact A.filter (fun a ↦ pathVisitsBall L 12 (v a) i ω)

lemma pathVisitedSites_measurable {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) :
    Measurable (fun ω : ConfigurationPath n L ↦ ((pathVisitedSites L v A i ω).card:ℝ)) := by
  classical
  simp only [pathVisitedSites,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (pathVisitsBall_isClosed L 12 (v a) i).measurableSet
    measurable_const measurable_const

@[simp] lemma pathVisitedSites_reverse {S : Type*} {n : ℕ} (L : Length)
    (v : S → Torus L) (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L) :
    pathVisitedSites L v A i (reverseConfigurationPath n L ω)=pathVisitedSites L v A i ω := by
  classical
  simp only [pathVisitedSites,pathVisitsBall_reverse]

end HardSphere

namespace HardSphere.FreeVisits
open HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital HardSphere.Wiener

lemma visited_subset_near {n K : ℕ} [NeZero K] (L : Length) (A : Finset (DiscreteTorus K))
    (i : Fin n) (ω : ConfigurationPath n L) (x : Torus L)
    (hω : ∀ (u : Time) (j : Fin 3), dist (ω u i j) (x j)≤1) :
    ∀ v∈pathVisitedSites L (siteCenter L) A i ω, ∀ j, dist (siteCenter L v j) (x j)≤13 := by
  classical
  intro v hv j
  obtain ⟨_,u,hu⟩ := Finset.mem_filter.mp hv
  have hc := dist_coord_le_torusDistance L (ω u i) (siteCenter L v) j
  calc
    dist (siteCenter L v j) (x j) ≤ dist (siteCenter L v j) (ω u i j)+dist (ω u i j) (x j) := dist_triangle _ _ _
    _ ≤ 12+1 := add_le_add (by rw [dist_comm]; exact hc.trans hu) (hω u j)
    _ = 13 := by norm_num

lemma visited_card_le_of_short {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) (ω : ConfigurationPath n L) (x : Torus L)
    (hω : ∀ (u : Time) (j : Fin 3), dist (ω u i j) (x j)≤1) :
    (pathVisitedSites L (siteCenter L) A i ω).card≤29^3 :=
  card_near_sites_le L hL x _ (visited_subset_near L A i ω x hω)

lemma visited_split {S : Type*} [DecidableEq S] {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L)
    (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    pathVisitedSites L v A i ω = pathVisitedSites L v A i (configurationPrefix n L u ω) ∪
      pathVisitedSites L v A i (configurationSuffix n L u ω) := by
  classical
  ext a
  rw [Finset.mem_union]
  constructor
  · intro hav
    obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
    by_cases hq' : (q:ℝ)≤u
    · let z : Time := ⟨(q:ℝ)/(u:ℝ),div_nonneg q.property.1 hu.le,(div_le_one hu).mpr hq'⟩
      have hz : prefixTime u z=q := by
        apply Subtype.ext
        change (u:ℝ)*((q:ℝ)/(u:ℝ))=(q:ℝ)
        field_simp
      exact Or.inl (Finset.mem_filter.mpr ⟨ha,z,by simpa only [configurationPrefix,ContinuousMap.comp_apply,hz] using hq⟩)
    · let z : Time := ⟨((q:ℝ)-(u:ℝ))/(1-(u:ℝ)),
          div_nonneg (sub_nonneg.mpr (le_of_not_ge hq')) (sub_pos.mpr hu').le,
          (div_le_one (sub_pos.mpr hu')).mpr (by linarith [q.property.2])⟩
      have hz : suffixTime u z=q := by
        apply Subtype.ext
        change (u:ℝ)+(1-(u:ℝ))*(((q:ℝ)-(u:ℝ))/(1-(u:ℝ)))=(q:ℝ)
        field_simp [ne_of_gt (sub_pos.mpr hu')]
        ring
      exact Or.inr (Finset.mem_filter.mpr ⟨ha,z,by simpa only [configurationSuffix,ContinuousMap.comp_apply,hz] using hq⟩)
  · rintro (hav|hav)
    · obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
      exact Finset.mem_filter.mpr ⟨ha,prefixTime u q,hq⟩
    · obtain ⟨ha,q,hq⟩ := Finset.mem_filter.mp hav
      exact Finset.mem_filter.mpr ⟨ha,suffixTime u q,hq⟩

lemma visited_card_split_le {S : Type*} {n : ℕ} (L : Length) (v : S → Torus L)
    (A : Finset S) (i : Fin n) (ω : ConfigurationPath n L)
    (u : Time) (hu : 0<(u:ℝ)) (hu' : (u:ℝ)<1) :
    (pathVisitedSites L v A i ω).card ≤ (pathVisitedSites L v A i (configurationPrefix n L u ω)).card +
      (pathVisitedSites L v A i (configurationSuffix n L u ω)).card := by
  classical
  rw [visited_split L v A i ω u hu hu']
  exact Finset.card_union_le _ _

lemma freeTrajectory_coord_dist_le {n : ℕ} (L : Length) (t : ℝ) (w : CoordinatePaths n)
    (X : Configuration n L) (i : Fin n) (u : Time) (j : Fin 3) :
    dist (freeTrajectory n L t w X u i j) (X i j) ≤ Real.sqrt (2*t)*‖w (i,j)‖ := by
  change dist (X i j+((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)) (X i j) ≤ _
  simp only [dist_eq_norm,add_sub_cancel_left]
  calc
    ‖((Real.sqrt (2*t)*w (i,j) u:ℝ):AddCircle L.val)‖ ≤ ‖Real.sqrt (2*t)*w (i,j) u‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ = Real.sqrt (2*t)*|w (i,j) u| := by rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (w (i,j)) u) (Real.sqrt_nonneg _)

lemma free_visited_card_le_of_norm {n K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (A : Finset (DiscreteTorus K)) (i : Fin n) (t : ℝ) (w : CoordinatePaths n)
    (X : Configuration n L) (hw : ∀ j, Real.sqrt (2*t)*‖w (i,j)‖≤1) :
    (pathVisitedSites L (siteCenter L) A i (freeTrajectory n L t w X)).card≤29^3 := by
  apply visited_card_le_of_short L hL A i _ (X i)
  exact fun u j ↦ (freeTrajectory_coord_dist_le L t w X i u j).trans (hw j)

end HardSphere.FreeVisits

end

end OAI
