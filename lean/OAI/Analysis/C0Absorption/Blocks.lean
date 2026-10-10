import OAI.Analysis.C0Absorption.Angles

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

abbrev Level := ℕ × ℕ
def levelJ (lev : Level) : ℕ := lev.1+lev.2+2
abbrev Block (lev : Level) := (j : Fin (levelJ lev+1)) × BandGrid j.val

structure Label where
  level : Level
  band : Fin (levelJ level+1)
  tag : BandGrid band.val

instance : Countable Label := by
  apply Function.Injective.countable (f := fun γ : Label => (⟨γ.level,⟨γ.band,γ.tag⟩⟩ : (lev : Level) × Block lev))
  intro a b h
  cases a
  cases b
  cases h
  rfl

instance : TopologicalSpace Label := ⊥
instance : DiscreteTopology Label := ⟨rfl⟩

abbrev InputCoordinate := ℕ ⊕ Label

def coordinateEnumeration : InputCoordinate ≃ ℕ := Classical.choice inferInstance

def rowIndex (i : ℕ) : ℕ := coordinateEnumeration (Sum.inl i)
def labelIndex (γ : Label) : ℕ := coordinateEnumeration (Sum.inr γ)
def blockLabel (lev : Level) (b : Block lev) : Label := ⟨lev,b.1,b.2⟩

@[simp] theorem blockLabel_level (lev : Level) (b : Block lev) : (blockLabel lev b).level=lev := rfl

theorem blockLabel_injective (lev : Level) : Function.Injective (blockLabel lev) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

theorem labelIndex_injective : Function.Injective labelIndex := by
  intro a b h
  exact Sum.inr.inj (coordinateEnumeration.injective h)

theorem rowIndex_injective : Function.Injective rowIndex := by
  intro a b h
  exact Sum.inl.inj (coordinateEnumeration.injective h)

theorem rowIndex_ne_labelIndex (i : ℕ) (γ : Label) : rowIndex i≠labelIndex γ := by
  intro h
  cases coordinateEnumeration.injective h

def blockCoordinates (lev : Level) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun b : Block lev => labelIndex (blockLabel lev b))

theorem mem_blockCoordinates {lev : Level} {k : ℕ} : k ∈ blockCoordinates lev ↔
    ∃ γ : Label, γ.level=lev ∧ labelIndex γ=k := by
  classical
  constructor
  · intro hk
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hk
    exact ⟨blockLabel lev b,rfl,hb⟩
  · rintro ⟨⟨μ,j,ξ⟩,h,rfl⟩
    cases h
    exact Finset.mem_image.mpr ⟨⟨j,ξ⟩,Finset.mem_univ _,rfl⟩

theorem blockCoordinates_nonempty (lev : Level) : (blockCoordinates lev).Nonempty := by
  classical
  let j : Fin (levelJ lev+1) := ⟨0,by omega⟩
  let ξ : BandGrid 0 := Fin.elim0
  exact ⟨labelIndex (⟨lev,j,ξ⟩ : Label),mem_blockCoordinates.mpr ⟨⟨lev,j,ξ⟩,rfl,rfl⟩⟩

def predecessorCoordinates (lev : Level) : Finset ℕ :=
  match lev.2 with
  | 0 => {rowIndex lev.1}
  | n+1 => blockCoordinates (lev.1,n)

def radiusCoordinates (lev : Level) : Finset ℕ := predecessorCoordinates lev ∪ blockCoordinates lev

theorem radiusCoordinates_nonempty (lev : Level) : (radiusCoordinates lev).Nonempty :=
  (blockCoordinates_nonempty lev).mono Finset.subset_union_right

def levelSuccessor (lev : Level) : Level := (lev.1,lev.2+1)

def coordinateLevels (k : ℕ) : Finset Level := by
  classical
  exact match coordinateEnumeration.symm k with
  | Sum.inl i => {(i,0)}
  | Sum.inr γ => {γ.level,levelSuccessor γ.level}

theorem radius_incidence (lev : Level) (k : ℕ) :
    k ∈ radiusCoordinates lev ↔ lev ∈ coordinateLevels k := by
  classical
  obtain ⟨c,rfl⟩ := coordinateEnumeration.surjective k
  cases c with
  | inl i =>
    have hk : ∀ μ, coordinateEnumeration (Sum.inl i) ∉ blockCoordinates μ := by
      intro μ h
      obtain ⟨γ,_,he⟩ := mem_blockCoordinates.mp h
      exact rowIndex_ne_labelIndex i γ he.symm
    simp only [radiusCoordinates,Finset.mem_union,coordinateLevels,Equiv.symm_apply_apply,
      Finset.mem_singleton,hk,or_false]
    rcases lev with ⟨l,n⟩
    cases n with
    | zero => simp only [predecessorCoordinates,Finset.mem_singleton,Prod.mk.injEq,and_true]
              change rowIndex i=rowIndex l ↔ l=i
              rw [rowIndex_injective.eq_iff]
              exact eq_comm
    | succ n => simp only [predecessorCoordinates,hk,Prod.mk.injEq,Nat.succ_ne_zero,and_false]
  | inr γ =>
    have hk (μ : Level) : coordinateEnumeration (Sum.inr γ) ∈ blockCoordinates μ ↔ γ.level=μ := by
      rw [mem_blockCoordinates]
      constructor
      · rintro ⟨δ,hδ,he⟩
        exact (labelIndex_injective he) ▸ hδ
      · intro h
        exact ⟨γ,h,rfl⟩
    simp only [radiusCoordinates,Finset.mem_union,coordinateLevels,Equiv.symm_apply_apply,
      Finset.mem_insert,Finset.mem_singleton,hk]
    rcases lev with ⟨i,n⟩
    rcases hγ : γ.level with ⟨l,m⟩
    cases n with
    | zero =>
      simp only [predecessorCoordinates,Finset.mem_singleton]
      have hn : coordinateEnumeration (Sum.inr γ)≠rowIndex i := (rowIndex_ne_labelIndex i γ).symm
      simp only [hn,false_or,levelSuccessor,Prod.mk.injEq,Nat.zero_ne_add_one,and_false,or_false]
      tauto
    | succ n =>
      simp only [predecessorCoordinates,hk,hγ,levelSuccessor,Prod.mk.injEq]
      omega

theorem radius_finite_exceptions (N : ℕ) :
    {lev : Level | ∃ k≤N, k ∈ radiusCoordinates lev}.Finite := by
  classical
  have he : {lev : Level | ∃ k≤N, k ∈ radiusCoordinates lev} ⊆
      ↑((Finset.range (N+1)).biUnion coordinateLevels) := by
    rintro lev ⟨k,hk,hlev⟩
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr (by omega),(radius_incidence lev k).mp hlev⟩
  exact (Finset.finite_toSet _).subset he

def finiteProjection (I : Finset ℕ) : C0 →L[ℝ] C0 :=
  LinearMap.mkContinuous
    ({
      toFun := fun s : C0 => extendFinite I (fun k => s k)
      map_add' := by
        intro s t
        ext k
        simp only [extendFinite_apply,ZeroAtInftyContinuousMap.add_apply]
        split_ifs <;> simp
      map_smul' := by
        intro a s
        ext k
        simp only [extendFinite_apply,ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]
        split_ifs <;> simp } : C0 →ₗ[ℝ] C0) 1 (fun s => by
      change ‖extendFinite I (fun k => s k)‖ ≤ 1 * ‖s‖
      simpa only [one_mul] using extendFinite_norm_le I (fun k => s k) (norm_nonneg s) (fun k => c0_norm_apply_le s k))

@[simp] theorem finiteProjection_apply (I : Finset ℕ) (s : C0) (k : ℕ) :
    finiteProjection I s k = if k∈I then s k else 0 := by
  classical
  rfl

def finiteRadius (I : Finset ℕ) (s : C0) : ℝ := ‖finiteProjection I s‖
def localRadius (lev : Level) : C0 → ℝ := finiteRadius (radiusCoordinates lev)

theorem finiteRadius_nonneg (I : Finset ℕ) (s : C0) : 0 ≤ finiteRadius I s := norm_nonneg _

theorem finiteRadius_le (I : Finset ℕ) (s : C0) : finiteRadius I s≤‖s‖ := by
  apply c0_norm_le _ (norm_nonneg s)
  intro k
  rw [finiteProjection_apply]
  split_ifs
  · exact c0_norm_apply_le s k
  · simp

theorem coordinate_le_finiteRadius {I : Finset ℕ} (s : C0) {k : ℕ} (hk : k∈I) :
    |s k| ≤ finiteRadius I s := by
  simpa only [finiteRadius,finiteProjection_apply,hk,↓reduceIte] using c0_norm_apply_le (finiteProjection I s) k

theorem finiteRadius_lipschitz (I : Finset ℕ) : LipschitzWith 1 (finiteRadius I) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [finiteRadius,NNReal.coe_one,one_mul,dist_eq_norm]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← map_sub]
  exact finiteRadius_le I (s-t)

theorem finiteRadius_le_tau {I : Finset ℕ} (N : ℕ) (hI : ∀ k∈I, N<k) (s : C0) :
    finiteRadius I s ≤ tau N s := by
  apply c0_norm_le _ (tau_nonneg _ _)
  intro k
  rw [finiteProjection_apply]
  split_ifs with hk
  · have hh := c0_norm_apply_le (coordinateTail N s) k
    simpa only [tau,coordinateTail_apply,hI k hk,↓reduceIte] using hh
  · simpa using tau_nonneg N s

theorem finiteRadius_smul (I : Finset ℕ) (a : ℝ) (s : C0) :
    finiteRadius I (a • s)=|a| * finiteRadius I s := by
  simp only [finiteRadius,map_smul,norm_smul,Real.norm_eq_abs]

theorem localRadius_tendsto (s : C0) : Tendsto (fun lev => localRadius lev s) cofinite (nhds 0) := by
  have ht := tau_tendsto_zero s
  rw [Metric.tendsto_atTop] at ht
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N,hN⟩ := ht ε hε
  filter_upwards [(radius_finite_exceptions N).eventually_cofinite_notMem] with lev hlev
  have he : ∀ k∈radiusCoordinates lev, N<k := by
    intro k hk
    by_contra hn
    exact hlev ⟨k,by omega,hk⟩
  have hh := finiteRadius_le_tau N he s
  have hτ := hN N le_rfl
  simpa only [Real.dist_eq,sub_zero,localRadius,abs_of_nonneg (finiteRadius_nonneg _ s)] using
    hh.trans_lt (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (tau_nonneg _ s)] using hτ)

end
end C0Absorption

end OAI
