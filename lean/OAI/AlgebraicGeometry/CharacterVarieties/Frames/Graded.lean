import OAI.AlgebraicGeometry.CharacterVarieties.Frames.GradeMaps
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.ComplementaryPatches

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.TwoFlagBand
open scoped Classical
variable {K : Type*} [Field K] {n m r : ℕ}

def supportedCoordinates (d : RankShape n m r) (s : Set (Fin n × Fin m)) :
    Submodule K (BlockCoordinates K d) where
  carrier := {v | ∀ p, p∉s → v p=0}
  zero_mem' _ _ := rfl
  add_mem' hu hv p hp := by rw [Pi.add_apply,hu p hp,hv p hp,add_zero]
  smul_mem' c v hv p hp := by rw [Pi.smul_apply,hv p hp,smul_zero]

theorem supportedCoordinates_eq (d : RankShape n m r) (s : Set (Fin n × Fin m)) :
    supportedCoordinates (K:=K) d s=⨆ (p : Fin n × Fin m) (_ : p∈s),coordinateBlock d p := by
  apply le_antisymm
  · intro v hv
    have hs : (∑ p,Pi.single p (v p))=v := by
      funext p
      simp
    rw [←hs]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : p∈s
    · exact Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp ⟨v p,rfl⟩)
    · have hz : v p=0 := hv p hp
      simp only [hz,Pi.single_zero]
      exact Submodule.zero_mem _
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp v hv
    rcases hv with ⟨z,rfl⟩
    intro t ht
    have hne : t≠p := by intro he; subst t; exact ht hp
    simp only [LinearMap.single_apply,Pi.single_eq_of_ne hne]

theorem boundedGrid_coordinate_mem (d : RankShape n m r) (i j : ℕ)
    (v : BlockCoordinates K d) :
    v ∈ boundedGrid (fun p => coordinateBlock d p) i j ↔
      ∀ p, ¬(p.1.val < i ∧ p.2.val < j) → v p=0 := by
  have he : boundedGrid (fun p => coordinateBlock (K:=K) d p) i j =
      supportedCoordinates d {p | p.1.val < i ∧ p.2.val < j} :=
    (supportedCoordinates_eq d _).symm
  exact he ▸ Iff.rfl

end IntegralCharacterVarieties.TwoFlagBand
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand

abbrev Atoms {n m r : ℕ} (d : RankShape n m r) :=
  (p : Fin n × Fin m) × Fin (d.val p).val

def rowGrade {n m r : ℕ} (d : RankShape n m r) (i : Atoms d) : ℕ := i.1.1.val

def colGrade {n m r : ℕ} (d : RankShape n m r) (i : Atoms d) : ℕ := i.1.2.val

end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α : Type*} {n m r : ℕ}

def curryCoordinates (d : RankShape n m r) :
    (Atoms d → K) ≃ₗ[K] BlockCoordinates K d :=
  LinearEquiv.piCurry K (fun _ _ => K)

lemma curry_row_prefix (d : RankShape n m r) (k : ℕ) :
    (coordinatePrefix K (rowGrade d) k).map (curryCoordinates d).toLinearMap=
      supportedCoordinates d {p | p.1.val  <  k} := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩ p hp
    ext j
    exact hw ⟨p,j⟩ (by simpa [rowGrade] using Nat.le_of_not_gt hp)
  · intro hv
    refine ⟨(curryCoordinates d).symm v,?_,LinearEquiv.apply_symm_apply _ _⟩
    intro ⟨p,j⟩ hp
    exact congrFun (hv p (by simpa [rowGrade] using Nat.not_lt.mpr hp)) j

lemma curry_col_prefix (d : RankShape n m r) (k : ℕ) :
    (coordinatePrefix K (colGrade d) k).map (curryCoordinates d).toLinearMap=
      supportedCoordinates d {p | p.2.val  <  k} := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩ p hp
    ext j
    exact hw ⟨p,j⟩ (by simpa [colGrade] using Nat.le_of_not_gt hp)
  · intro hv
    refine ⟨(curryCoordinates d).symm v,?_,LinearEquiv.apply_symm_apply _ _⟩
    intro ⟨p,j⟩ hp
    exact congrFun (hv p (by simpa [colGrade] using Nat.not_lt.mpr hp)) j

lemma row_framedPrefix (d : RankShape n m r)
    (e : BlockCoordinates K d ≃ₗ[K] V) (k : ℕ) :
    framedPrefix (rowGrade d) ((curryCoordinates d).trans e) k=
      (supportedCoordinates d {p | p.1.val  <  k}).map e.toLinearMap := by
  change (coordinatePrefix K (rowGrade d) k).map
    (e.toLinearMap.comp (curryCoordinates d).toLinearMap)=_
  rw [Submodule.map_comp,curry_row_prefix]

lemma col_framedPrefix (d : RankShape n m r)
    (e : BlockCoordinates K d ≃ₗ[K] V) (k : ℕ) :
    framedPrefix (colGrade d) ((curryCoordinates d).trans e) k=
      (supportedCoordinates d {p | p.2.val  <  k}).map e.toLinearMap := by
  change (coordinatePrefix K (colGrade d) k).map
    (e.toLinearMap.comp (curryCoordinates d).toLinearMap)=_
  rw [Submodule.map_comp,curry_col_prefix]

lemma boundedGrid_map_support (d : RankShape n m r)
    (e : BlockCoordinates K d ≃ₗ[K] V) (i j : ℕ) :
    boundedGrid (fun p => (coordinateBlock d p).map e.toLinearMap) i j =
      (supportedCoordinates d {p | p.1.val  <  i  ∧  p.2.val  <  j}).map e.toLinearMap := by
  rw [supportedCoordinates_eq]
  simp only [boundedGrid,Submodule.map_iSup]
  rfl

lemma coordinatePrefix_top (a : α → ℕ) (k : ℕ) (ha : ∀ i,a i < k) :
    coordinatePrefix K a k=⊤ := by
  apply top_unique
  intro v _ i hi
  exact False.elim (Nat.not_le.mpr (ha i) hi)

lemma framedPrefix_top (a : α → ℕ) (f : (α → K) ≃ₗ[K] V)
    (k : ℕ) (ha : ∀ i,a i < k) : framedPrefix a f k=⊤ := by
  unfold framedPrefix
  rw [coordinatePrefix_top a k ha]
  simpa only [Submodule.map_top] using (LinearMap.range_eq_top.mpr f.surjective)

lemma framedPrefix_mono (a : α → ℕ) (f : (α → K) ≃ₗ[K] V) :
    Monotone (framedPrefix a f) := fun _ _ hh => Submodule.map_mono (prefix_mono a hh)

lemma framedPrefix_zero (a : α → ℕ) (f : (α → K) ≃ₗ[K] V) :
    framedPrefix a f 0=⊥ := by
  simp only [framedPrefix,prefix_zero_eq_bot,Submodule.map_bot]

end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  {α β : Type*}

lemma frameChange_filters (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] V) (f : (β → R) ≃ₗ[R] V)
    (he : ∀ k,framedPrefix a e k=framedPrefix b f k) :
    ∀ k,(coordinatePrefix R a k).map (e.trans f.symm).toLinearMap=coordinatePrefix R b k := by
  intro k
  change (coordinatePrefix R a k).map (f.symm.toLinearMap.comp e.toLinearMap)=_
  rw [Submodule.map_comp]
  change (framedPrefix a e k).map f.symm.toLinearMap=_
  rw [he k,framedPrefix,←Submodule.map_comp]
  simp

def frameGradeEquiv (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] V) (f : (β → R) ≃ₗ[R] V)
    (he : ∀ k,framedPrefix a e k=framedPrefix b f k) (k : ℕ) :
    ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R) :=
  gradeEquiv a b (e.trans f.symm) (frameChange_filters a b e f he) k

lemma frameGradeEquiv_naturality (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] V) (f : (β → R) ≃ₗ[R] V)
    (he : ∀ k,framedPrefix a e k=framedPrefix b f k)
    (k : ℕ) (v : V) (hv : v∈framedPrefix a e (k+1)) :
    frameGradeEquiv a b e f he k (framedGrade a e k v)=framedGrade b f k v := by
  obtain ⟨w,hw,rfl⟩ := hv
  change gradeMap a b (e.trans f.symm) k (coordinateGrade R a k (e.symm (e w)))=
    coordinateGrade R b k (f.symm (e w))
  rw [LinearEquiv.symm_apply_apply]
  exact gradeMap_naturality a b (e.trans f.symm) (frameChange_filters a b e f he) k w hw

end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
open TwoFlagBand
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {α β : Type*} {n m : ℕ}

/-- A common atomic splitting of two endpoint flags preserves all prefixes. -/
lemma actual_band_common_prefixes
    (a : α → Fin n) (b : β → Fin m)
    (f : (α → K) ≃ₗ[K] V) (h : (β → K) ≃ₗ[K] V) :
    ∃ (d : RankShape n m (Module.finrank K V)) (e : (Atoms d → K) ≃ₗ[K] V),
      (∀ k,framedPrefix (rowGrade d) e k=framedPrefix (fun i => (a i).val) f k)  ∧
      (∀ k,framedPrefix (colGrade d) e k=framedPrefix (fun i => (b i).val) h k) := by
  let F := framedPrefix (fun i => (a i).val) f
  let H := framedPrefix (fun i => (b i).val) h
  have hFn : F n=⊤ := framedPrefix_top _ f n (fun i => (a i).isLt)
  have hHm : H m=⊤ := framedPrefix_top _ h m (fun i => (b i).isLt)
  obtain ⟨d,e,he⟩ := finite_shape_frame_covers F H
    (framedPrefix_mono _ f) (framedPrefix_mono _ h)
    (framedPrefix_zero _ f) (framedPrefix_zero _ h) n m hFn hHm
  refine ⟨d,(curryCoordinates d).trans e,?_,?_⟩
  · intro k
    by_cases hk : k ≤ n
    · have hh := he k m hk le_rfl
      rw [hHm,inf_top_eq,boundedGrid_map_support] at hh
      have hs : {p : Fin n × Fin m | p.1.val  <  k  ∧  p.2.val  <  m} = {p | p.1.val  <  k} := by
        ext p; simp
      rw [hs] at hh
      rw [row_framedPrefix]
      exact hh.symm
    · rw [framedPrefix_top _ _ k (fun i => (i.1.1.isLt.trans_le (by omega))),
        framedPrefix_top _ _ k (fun i => (a i).isLt.trans_le (by omega))]
  · intro k
    by_cases hk : k ≤ m
    · have hh := he n k le_rfl hk
      rw [hFn,top_inf_eq,boundedGrid_map_support] at hh
      have hs : {p : Fin n × Fin m | p.1.val  <  n  ∧  p.2.val  <  k} = {p | p.2.val  <  k} := by
        ext p; simp
      rw [hs] at hh
      rw [col_framedPrefix]
      exact hh.symm
    · rw [framedPrefix_top _ _ k (fun i => (i.1.2.isLt.trans_le (by omega))),
        framedPrefix_top _ _ k (fun i => (b i).isLt.trans_le (by omega))]

/-- Simultaneous splitting of two framed endpoint flags into a finite rank array, with row and
column quotient isomorphisms intertwining the named quotient projections on each prefix. -/
theorem actual_named_band_grades
    (a : α → Fin n) (b : β → Fin m)
    (f : (α → K) ≃ₗ[K] V) (h : (β → K) ≃ₗ[K] V) :
    ∃ (d : RankShape n m (Module.finrank K V)) (e : (Atoms d → K) ≃ₗ[K] V)
      (row : (k : ℕ) → ({i // rowGrade d i=k} → K) ≃ₗ[K] ({i // (a i).val=k} → K))
      (col : (k : ℕ) → ({i // colGrade d i=k} → K) ≃ₗ[K] ({i // (b i).val=k} → K)),
      (∀ k,framedPrefix (rowGrade d) e k=framedPrefix (fun i => (a i).val) f k)  ∧
      (∀ k,framedPrefix (colGrade d) e k=framedPrefix (fun i => (b i).val) h k)  ∧
      (∀ k v,v∈framedPrefix (rowGrade d) e (k+1) →
        row k (framedGrade (rowGrade d) e k v)=framedGrade (fun i => (a i).val) f k v)  ∧
      (∀ k v,v∈framedPrefix (colGrade d) e (k+1) →
        col k (framedGrade (colGrade d) e k v)=framedGrade (fun i => (b i).val) h k v) := by
  obtain ⟨d,e,hr,hc⟩ := actual_band_common_prefixes a b f h
  exact ⟨d,e,frameGradeEquiv _ _ e f hr,frameGradeEquiv _ _ e h hc,hr,hc,
    frameGradeEquiv_naturality _ _ e f hr,frameGradeEquiv_naturality _ _ e h hc⟩

end IntegralCharacterVarieties.NamedBandGrades
end

end OAI
