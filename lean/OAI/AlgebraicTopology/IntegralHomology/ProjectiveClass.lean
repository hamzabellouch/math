import OAI.AlgebraicTopology.IntegralHomology.OpenUnion
import OAI.AlgebraicTopology.IntegralHomology.ProjectiveLocal

namespace OAI

noncomputable section

namespace Kaplansky

/-! Localization, top homology, and the fundamental class of projective products. -/

section
open CategoryTheory Limits
open ComplexGrassmann

instance projectiveSpaceZero_nonempty : Nonempty (Grassmann 1 0) :=
  ⟨graphPoint (standardLineGraphFrame 0) 0⟩

/-- Complex projective space has no positive odd homology and no homology
above its real dimension. The induction uses the proved puncture retraction
and actual local relative homology, with no cell or orientation premise. -/
theorem projectiveSpaceHomology_isZero (k n : ℕ) (hn : n ≠ 0)
    (hdegree : Odd n ∨ 2*k < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (Grassmann 1 k))) := by
  induction k with
  | zero => exact integralSingularHomology_isZero_contractible _ n hn
  | succ k ih =>
    let P := graphPoint (standardLineGraphFrame (k+1)) 0
    have hlower : Odd n ∨ 2*k < n := by
      rcases hdegree with ho | hd
      · exact Or.inl ho
      · exact Or.inr (by omega)
    have hne : n ≠ 2*(k+1) := by
      rcases hdegree with ho | hd
      · obtain ⟨a, ha⟩ := ho
        omega
      · omega
    have hpuncture := (ih hlower).of_iso (projectiveSpacePunctureHomologyIso P n)
    exact (relativeHomology_exact_at_absolute
      (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 (k+1)))) n).isZero_of_both_isZero
      hpuncture (projectiveSpaceLocalHomology_isZero (by omega) P n hne)

/-- Punctured CP^k has no homology in degrees above 2k-2. -/
theorem projectiveSpacePunctureHomology_isZero {k : ℕ} (P : Grassmann 1 (k+1))
    (n : ℕ) (hn : 2*k < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (Grassmann 1 (k+1))))) :=
  (projectiveSpaceHomology_isZero k n (by omega) (Or.inr hn)).of_iso
    (projectiveSpacePunctureHomologyIso P n)

/-- The top-degree local connecting map is zero at every point of CP^k. -/
theorem projectiveSpaceTopBoundary_zero {k : ℕ} (hk : 0 < k) (P : Grassmann 1 k) :
    relativeHomologyBoundary (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))) (2*k-1) = 0 := by
  cases k with
  | zero => omega
  | succ k => exact (projectiveSpacePunctureHomology_isZero P _ (by omega)).eq_of_tgt _ _

/-- Absolute-to-local homology is an isomorphism in the real top dimension
of every positive-dimensional single complex projective space. -/
def projectiveSpaceTopLocalizationIso {k : ℕ} (hk : 0 < k) (P : Grassmann 1 k) :
    (integralSingularHomology (2*k)).obj (TopCat.of (Grassmann 1 k)) ≅
      relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))) (2*k) := by
  let i := subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))
  have hzero (n : ℕ) (hn : 2*k-2 < n) :
      IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (Grassmann 1 k)))) := by
    cases k with
    | zero => omega
    | succ k => exact projectiveSpacePunctureHomology_isZero P n (by omega)
  apply (LinearEquiv.ofBijective (absoluteToRelative i (2*k)).hom ?_).toModuleIso
  constructor
  · apply (absoluteToRelative i (2*k)).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute i (2*k)).moduleCat_range_eq_ker]
    have hz : (integralSingularHomology (2*k)).map i = 0 :=
      (hzero (2*k) (by omega)).eq_of_src _ _
    change LinearMap.range ((integralSingularHomology (2*k)).map i).hom = ⊥
    rw [hz]
    exact LinearMap.range_zero
  · have he : 2*k = (2*k-1)+1 := by omega
    rw [he]
    intro z
    apply (relativeClass_lifts_iff i (2*k-1) z).mp
    rw [projectiveSpaceTopBoundary_zero hk P]
    rfl

theorem projectiveSpaceTopLocalizationIso_hom {k : ℕ} (hk : 0 < k)
    (P : Grassmann 1 k) : (projectiveSpaceTopLocalizationIso hk P).hom =
      absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (Grassmann 1 k))) (2*k) := rfl

open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The dimension of a product with at most one nontrivial factor. -/
theorem projectiveProduct_one_factor_dimension (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) : ∑ j, K j = K i := by
  classical
  exact Finset.sum_eq_single i (fun j _ hji => hrest j hji) (by simp)

/-- Puncturing commutes with the actual one-factor product homeomorphism. -/
def projectiveOneFactorPunctureHomeomorph (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (P : ProjectiveProduct K) :
    ({P}ᶜ : Set (ProjectiveProduct K)) ≃ₜ ({P i}ᶜ : Set (Grassmann 1 (K i))) :=
  (projectiveProductOneFactorHomeomorph K i hrest).subtype
    (fun _ => (not_congr (projectiveProductOneFactorHomeomorph K i hrest).injective.eq_iff).symm)

/-- The top two punctured homology groups vanish for a product supported at
one factor, with no restriction that this factor be a projective line. -/
theorem projectiveOneFactorPunctureHomology_isZero (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j)
    (P : ProjectiveProduct K) (n : ℕ) (hn : 2*(∑ j, K j)-2 < n) :
    IsZero ((integralSingularHomology n).obj
      (TopCat.of ({P}ᶜ : Set (ProjectiveProduct K)))) := by
  have hdim := projectiveProduct_one_factor_dimension K i hrest
  have hsingle : ∀ (k : ℕ), 0 < k → 2*k-2 < n → ∀ Q : Grassmann 1 k,
      IsZero ((integralSingularHomology n).obj (TopCat.of ({Q}ᶜ : Set (Grassmann 1 k)))) := by
    intro k hk hn Q
    cases k with
    | zero => omega
    | succ k => exact projectiveSpacePunctureHomology_isZero Q n (by omega)
  exact (hsingle (K i) (by omega) (by omega) (P i)).of_iso
    (integralHomologyHomotopyIso (projectiveOneFactorPunctureHomeomorph K i hrest P).toHomotopyEquiv n)

/-- The requested top-degree connecting map vanishes for every product with
one positive-dimensional factor, even when its total dimension exceeds one. -/
theorem projectiveOneFactorTopBoundary_zero (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) (P : ProjectiveProduct K) :
    relativeHomologyBoundary (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
      (2*(∑ j, K j)-1) = 0 :=
  (projectiveOneFactorPunctureHomology_isZero K i hrest hp P _ (by omega)).eq_of_tgt _ _

/-- The actual absolute-to-relative map, proved bijective in top degree. -/
def projectiveOneFactorTopLocalizationIso (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) (P : ProjectiveProduct K) :
    (integralSingularHomology (2*(∑ j, K j))).obj (TopCat.of (ProjectiveProduct K)) ≅
      relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ j, K j)) := by
  let j := subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))
  apply (LinearEquiv.ofBijective (absoluteToRelative j (2*(∑ j, K j))).hom ?_).toModuleIso
  constructor
  · apply (absoluteToRelative j (2*(∑ j, K j))).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute j (2*(∑ j, K j))).moduleCat_range_eq_ker]
    have hz : (integralSingularHomology (2*(∑ j, K j))).map j = 0 :=
      (projectiveOneFactorPunctureHomology_isZero K i hrest hp P _ (by omega)).eq_of_src _ _
    change LinearMap.range ((integralSingularHomology (2*(∑ j, K j))).map j).hom = ⊥
    rw [hz]
    exact LinearMap.range_zero
  · have he : 2*(∑ j, K j) = (2*(∑ j, K j)-1)+1 := by omega
    rw [he]
    intro z
    apply (relativeClass_lifts_iff j (2*(∑ j, K j)-1) z).mp
    rw [projectiveOneFactorTopBoundary_zero K i hrest hp P]
    rfl

theorem projectiveOneFactorTopLocalizationIso_hom (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) (P : ProjectiveProduct K) :
    (projectiveOneFactorTopLocalizationIso K i hrest hp P).hom =
      absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ j, K j)) := rfl

/-- Global top homology is ℤ, normalized by the preserved canonical local class. -/
def projectiveOneFactorTopHomologyIso (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) :
    (integralSingularHomology (2*(∑ j, K j))).obj (TopCat.of (ProjectiveProduct K)) ≅
      ModuleCat.of ℤ ℤ :=
  projectiveOneFactorTopLocalizationIso K i hrest hp (firstCoordinateProduct K) ≪≫
    canonicalProductLocalHomologyIso K hp

/-- An actual global lift of the preserved generator for an arbitrary-dimensional
one-factor product. The multi-factor case is not assumed. -/
def projectiveOneFactorFundamentalClass (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) :
    (integralSingularHomology (2*(∑ j, K j))).obj (TopCat.of (ProjectiveProduct K)) :=
  (projectiveOneFactorTopLocalizationIso K i hrest hp (firstCoordinateProduct K)).inv
    (canonicalProductLocalGenerator K hp)

theorem projectiveOneFactorFundamentalClass_localizes (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ j, K j))
      (projectiveOneFactorFundamentalClass K i hrest hp) = canonicalProductLocalGenerator K hp := by
  rw [← projectiveOneFactorTopLocalizationIso_hom K i hrest hp]
  exact ConcreteCategory.congr_hom
    (projectiveOneFactorTopLocalizationIso K i hrest hp (firstCoordinateProduct K)).inv_hom_id _

theorem projectiveOneFactorFundamentalClass_ne_zero (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) :
    projectiveOneFactorFundamentalClass K i hrest hp ≠ 0 := by
  intro hz
  have h := projectiveOneFactorFundamentalClass_localizes K i hrest hp
  rw [hz, map_zero] at h
  exact canonicalProductLocalGenerator_ne_zero K hp h.symm

theorem projectiveOneFactorFundamentalClass_coordinate (i : ι)
    (hrest : ∀ j, j ≠ i → K j = 0) (hp : 0 < ∑ j, K j) :
    (projectiveOneFactorTopHomologyIso K i hrest hp).hom
      (projectiveOneFactorFundamentalClass K i hrest hp) = (1 : ℤ) := by
  change (canonicalProductLocalHomologyIso K hp).hom
    ((projectiveOneFactorTopLocalizationIso K i hrest hp _).hom _) = 1
  rw [projectiveOneFactorTopLocalizationIso_hom, projectiveOneFactorFundamentalClass_localizes]
  exact canonicalProductLocalGenerator_coordinate K hp

end

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {ι : Type} (K : ι → ℕ)

/-- The coordinate puncture is open in the actual compact projective product. -/
def projectiveCoordinatePuncture (P : ProjectiveProduct K) (i : ι) : Set (ProjectiveProduct K) :=
  {Q | Q i ≠ P i}

theorem projectiveCoordinatePuncture_open (P : ProjectiveProduct K) (i : ι) :
    IsOpen (projectiveCoordinatePuncture K P i) :=
  isClosed_singleton.isOpen_compl.preimage (continuous_apply i)

def coordinatePunctureFactor (P : ProjectiveProduct K) (T : Finset ι) (i : ι) :=
  {Q : Grassmann 1 (K i) // i ∈ T → Q ≠ P i}

instance (P : ProjectiveProduct K) (T : Finset ι) (i : ι) :
    TopologicalSpace (coordinatePunctureFactor K P T i) :=
  inferInstanceAs (TopologicalSpace {Q : Grassmann 1 (K i) // i ∈ T → Q ≠ P i})

def coordinatePunctureIntersectionHomeomorph (P : ProjectiveProduct K) (T : Finset ι) :
    (⋂ i ∈ T, projectiveCoordinatePuncture K P i) ≃ₜ
      (∀ i, coordinatePunctureFactor K P T i) where
  toFun Q i := ⟨Q.val i, fun hi => (mem_iInter.mp (mem_iInter.mp Q.property i) hi)⟩
  invFun Q := ⟨fun i => (Q i).val, mem_iInter.mpr (fun i => mem_iInter.mpr (Q i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_pi (fun i => continuous_subtype_val.comp
    (continuous_apply i))).subtype_mk _

def coordinatePunctureDimensions (T : Finset ι) (i : ι) : ℕ := by
  classical
  exact if i ∈ T then K i - 1 else K i

def coordinatePunctureFactorHomotopyEquiv (P : ProjectiveProduct K) (T : Finset ι)
    (hT : ∀ i ∈ T, 0 < K i) (i : ι) :
    coordinatePunctureFactor K P T i ≃ₕ Grassmann 1 (coordinatePunctureDimensions K T i) := by
  classical
  by_cases hi : i ∈ T
  · have he : ({Q : Grassmann 1 (K i) | i ∈ T → Q ≠ P i}) = {P i}ᶜ := by
      ext Q
      simp [hi]
    let e := (Homeomorph.setCongr he).toHomotopyEquiv
    have hk := hT i hi
    have hgen : ∀ k : ℕ, 0 < k → ∀ Q : Grassmann 1 k,
        ({Q}ᶜ : Set (Grassmann 1 k)) ≃ₕ Grassmann 1 (k-1) := by
      intro k hk Q
      cases k with
      | zero => omega
      | succ k => exact projectivePointPunctureLowerHomotopyEquiv Q
    have hd : coordinatePunctureDimensions K T i = K i - 1 := ite_eq_left hi
    rw [hd]
    exact e.trans (hgen (K i) hk (P i))
  · have he : ({Q : Grassmann 1 (K i) | i ∈ T → Q ≠ P i}) = univ := by
      ext Q
      simp [hi]
    have hd : coordinatePunctureDimensions K T i = K i := ite_eq_right hi
    rw [hd]
    exact ((Homeomorph.setCongr he).trans (Homeomorph.Set.univ _)).toHomotopyEquiv

/-- Every nonempty coordinate-puncture intersection retracts to the actual
projective product with one dimension removed in each punctured factor. -/
def coordinatePunctureIntersectionHomotopyEquiv (P : ProjectiveProduct K) (T : Finset ι)
    (hT : ∀ i ∈ T, 0 < K i) :
    (⋂ i ∈ T, projectiveCoordinatePuncture K P i) ≃ₕ
      ProjectiveProduct (coordinatePunctureDimensions K T) :=
  (coordinatePunctureIntersectionHomeomorph K P T).toHomotopyEquiv.trans
    (HomotopyEquiv.piCongrRight (coordinatePunctureFactorHomotopyEquiv K P T hT))

variable [Fintype ι]

theorem coordinatePunctureDimensions_sum (T : Finset ι) (hT : ∀ i ∈ T, 0 < K i) :
    (∑ i, coordinatePunctureDimensions K T i) + T.card = ∑ i, K i := by
  classical
  have he : ∑ i, (coordinatePunctureDimensions K T i + if i ∈ T then 1 else 0) = ∑ i, K i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ T
    · have := hT i hi
      simp only [coordinatePunctureDimensions, ite_eq_left hi]
      omega
    · simp [coordinatePunctureDimensions, hi]
  have hcount : (∑ i, if i ∈ T then 1 else 0 : ℕ) = T.card := by
    rw [Finset.sum_boole]
    have hf : Finset.univ.filter (fun i => i ∈ T) = T := by ext i; simp
    simp only [hf, Nat.cast_id]
  rwa [Finset.sum_add_distrib, hcount] at he

/-- Positive-dimensional coordinate punctures cover the complement of any point. -/
theorem projectiveCoordinatePunctures_cover (P : ProjectiveProduct K) :
    (⋃ i ∈ Finset.univ.filter (fun i => 0 < K i), projectiveCoordinatePuncture K P i) = {P}ᶜ := by
  classical
  ext Q
  simp only [mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    projectiveCoordinatePuncture, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, hne⟩ he
    exact hne (congrFun he i)
  · intro hne
    have hd : ∃ i, Q i ≠ P i := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := hd
    refine ⟨i, ?_, hi⟩
    by_contra hk
    have hz : K i = 0 := by omega
    have hs : Subsingleton (Grassmann 1 (K i)) := by rw [hz]; infer_instance
    exact hi (hs.elim _ _)

end ComplexGrassmann

end

section
open CategoryTheory Limits
open ComplexGrassmann
variable {ι : Type} [Fintype ι]

/-- A zero-dimensional projective product is a single point, including an
empty index type. -/
theorem projectiveProductZero_contractible (K : ι → ℕ) (hK : ∑ i, K i = 0) :
    ContractibleSpace (ProjectiveProduct K) := by
  have hzero (i) : K i = 0 := by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (K j)) (Finset.mem_univ i)
    omega
  let : Subsingleton (ProjectiveProduct K) := ⟨fun P Q => funext (fun i => by
    have hs : Subsingleton (Grassmann 1 (K i)) := by rw [hzero i]; infer_instance
    exact hs.elim _ _)⟩
  let : Nonempty (ProjectiveProduct K) := ⟨firstCoordinateProduct K⟩
  infer_instance

/-- A coordinate-puncture cover converts already-proved lower-dimensional
absolute vanishing into puncture vanishing two degrees below the real dimension. -/
theorem projectiveProductPunctureHomology_from_lower (K : ι → ℕ)
    (hp : 0 < ∑ i, K i)
    (hlower : ∀ L : ι → ℕ, (∑ i, L i) < ∑ i, K i → ∀ q : ℕ, 2*(∑ i, L i) < q →
      IsZero ((integralSingularHomology q).obj (TopCat.of (ProjectiveProduct L))))
    (P : ProjectiveProduct K) (n : ℕ) (hn : 2*(∑ i, K i)-2 < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (ProjectiveProduct K)))) := by
  classical
  let S := Finset.univ.filter (fun i => 0 < K i)
  have hs : S.Nonempty := by
    obtain ⟨i, hi, hKi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by omega : ∑ i, K i ≠ 0)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩⟩
  have hpos : ∀ i ∈ S, 0 < K i := fun i hi => (Finset.mem_filter.mp hi).2
  have hdim := coordinatePunctureDimensions_sum K S hpos
  have hcard : S.card ≤ n+1 := by omega
  have hz := finiteOpenUnionHomology_isZero S (projectiveCoordinatePuncture K P) hs
    (fun i _ => projectiveCoordinatePuncture_open K P i) n hcard (by
      intro T ht hts q hq
      have hT : ∀ i ∈ T, 0 < K i := fun i hi => hpos i (hts hi)
      have hd := coordinatePunctureDimensions_sum K T hT
      have hc := Finset.card_pos.mpr ht
      have hl := hlower (coordinatePunctureDimensions K T) (by omega) q (by omega)
      exact hl.of_iso (integralHomologyHomotopyIso
        (coordinatePunctureIntersectionHomotopyEquiv K P T hT) q))
  rw [projectiveCoordinatePunctures_cover K P] at hz
  exact hz

/-- Genuine integral homology of every finite projective product vanishes
above its real dimension. The strong induction uses the coordinate-puncture
cover, the proved puncture retractions, and the actual relative exact sequence. -/
theorem projectiveProductHomology_above_dimension (K : ι → ℕ)
    (n : ℕ) (hn : 2*(∑ i, K i) < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of (ProjectiveProduct K))) := by
  have hall : ∀ p : ℕ, ∀ L : ι → ℕ, (∑ i, L i) = p → ∀ q : ℕ, 2*p < q →
      IsZero ((integralSingularHomology q).obj (TopCat.of (ProjectiveProduct L))) := by
    intro p
    induction p using Nat.strong_induction_on with
    | h p ih =>
      intro L hL q hq
      by_cases hp : p = 0
      · have hzero : ∑ i, L i = 0 := hL.trans hp
        let := projectiveProductZero_contractible L hzero
        exact integralSingularHomology_isZero_contractible _ q (by omega)
      · let P := firstCoordinateProduct L
        have hpos : 0 < ∑ i, L i := by omega
        have hpuncture := projectiveProductPunctureHomology_from_lower L hpos
          (fun M hM r hr => ih (∑ i, M i) (by omega) M rfl r hr) P q (by omega)
        exact (relativeHomology_exact_at_absolute
          (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct L))) q).isZero_of_both_isZero
          hpuncture (projectivePointLocalHomology_isZero L hpos P q (by omega))
  exact hall (∑ i, K i) K rfl n hn

/-- Removing any point from any positive-dimensional projective product
kills homology above real dimension minus two. -/
theorem projectiveProductPunctureHomology_isZero (K : ι → ℕ) (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) (n : ℕ) (hn : 2*(∑ i, K i)-2 < n) :
    IsZero ((integralSingularHomology n).obj (TopCat.of ({P}ᶜ : Set (ProjectiveProduct K)))) :=
  projectiveProductPunctureHomology_from_lower K hp
    (fun L _ q hq => projectiveProductHomology_above_dimension L q hq) P n hn

theorem projectiveProductTopBoundary_zero (K : ι → ℕ) (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) :
    relativeHomologyBoundary (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
      (2*(∑ i, K i)-1) = 0 :=
  (projectiveProductPunctureHomology_isZero K hp P _ (by omega)).eq_of_tgt _ _

end

open CategoryTheory Limits
section
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- Top-degree localization is the actual absolute-to-relative map and is
invertible at every point of every positive-dimensional projective product. -/
def projectiveProductTopLocalizationIso (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) ≅
      relativeSingularHomology (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ i, K i)) := by
  let j := subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))
  apply (LinearEquiv.ofBijective (absoluteToRelative j (2*(∑ i, K i))).hom ?_).toModuleIso
  constructor
  · apply (absoluteToRelative j (2*(∑ i, K i))).hom.ker_eq_bot.mp
    rw [← (relativeHomology_exact_at_absolute j (2*(∑ i, K i))).moduleCat_range_eq_ker]
    have hz : (integralSingularHomology (2*(∑ i, K i))).map j = 0 :=
      (projectiveProductPunctureHomology_isZero K hp P _ (by omega)).eq_of_src _ _
    change LinearMap.range ((integralSingularHomology (2*(∑ i, K i))).map j).hom = ⊥
    rw [hz]
    exact LinearMap.range_zero
  · have he : 2*(∑ i, K i) = (2*(∑ i, K i)-1)+1 := by omega
    rw [he]
    intro z
    apply (relativeClass_lifts_iff j (2*(∑ i, K i)-1) z).mp
    rw [projectiveProductTopBoundary_zero K hp P]
    rfl

theorem projectiveProductTopLocalizationIso_hom (hp : 0 < ∑ i, K i) (P : ProjectiveProduct K) :
    (projectiveProductTopLocalizationIso K hp P).hom =
      absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K)))
        (2*(∑ i, K i)) := rfl

/-- Global integral top homology is ℤ with the exact preserved local normalization. -/
def projectiveProductTopHomologyIso (hp : 0 < ∑ i, K i) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) ≅
      ModuleCat.of ℤ ℤ :=
  projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K) ≪≫
    canonicalProductLocalHomologyIso K hp

/-- The unique actual global lift of the PRESERVED canonical local generator.
This construction is unconditional apart from positive total dimension. -/
def projectiveProductFundamentalClass (hp : 0 < ∑ i, K i) :
    (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)) :=
  (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv
    (canonicalProductLocalGenerator K hp)

theorem projectiveProductFundamentalClass_localizes (hp : 0 < ∑ i, K i) :
    absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i))
      (projectiveProductFundamentalClass K hp) = canonicalProductLocalGenerator K hp := by
  rw [← projectiveProductTopLocalizationIso_hom K hp]
  exact ConcreteCategory.congr_hom
    (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).inv_hom_id _

theorem projectiveProductFundamentalClass_coordinate (hp : 0 < ∑ i, K i) :
    (projectiveProductTopHomologyIso K hp).hom (projectiveProductFundamentalClass K hp) = (1 : ℤ) := by
  change (canonicalProductLocalHomologyIso K hp).hom
    ((projectiveProductTopLocalizationIso K hp _).hom _) = 1
  rw [projectiveProductTopLocalizationIso_hom, projectiveProductFundamentalClass_localizes]
  exact canonicalProductLocalGenerator_coordinate K hp

theorem projectiveProductFundamentalClass_ne_zero (hp : 0 < ∑ i, K i) :
    projectiveProductFundamentalClass K hp ≠ 0 := by
  intro hz
  have h := projectiveProductFundamentalClass_localizes K hp
  rw [hz, map_zero] at h
  exact canonicalProductLocalGenerator_ne_zero K hp h.symm

theorem projectiveProductFundamentalClass_unique (hp : 0 < ∑ i, K i)
    (z : (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K)))
    (hz : absoluteToRelative (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i)) z =
        canonicalProductLocalGenerator K hp) : z = projectiveProductFundamentalClass K hp := by
  apply (ModuleCat.mono_iff_injective
    (projectiveProductTopLocalizationIso K hp (firstCoordinateProduct K)).hom).mp inferInstance
  rw [projectiveProductTopLocalizationIso_hom, hz, projectiveProductFundamentalClass_localizes]

/-- Every absolute top class is an integral multiple of the specified global class. -/
theorem projectiveProductFundamentalClass_spans (hp : 0 < ∑ i, K i)
    (z : (integralSingularHomology (2*(∑ i, K i))).obj (TopCat.of (ProjectiveProduct K))) :
    ((projectiveProductTopHomologyIso K hp).hom z : ℤ) • projectiveProductFundamentalClass K hp = z := by
  apply (ModuleCat.mono_iff_injective (projectiveProductTopHomologyIso K hp).hom).mp inferInstance
  rw [map_zsmul, projectiveProductFundamentalClass_coordinate]
  exact mul_one _

/-- The same global class localizes nontrivially at EVERY projective point;
these are restrictions of a single class, not independently chosen generators. -/
theorem projectiveProductFundamentalClass_localizes_ne_zero (hp : 0 < ∑ i, K i)
    (P : ProjectiveProduct K) :
    absoluteToRelative (subspaceInclusion ({P}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i))
      (projectiveProductFundamentalClass K hp) ≠ 0 := by
  rw [← projectiveProductTopLocalizationIso_hom K hp P]
  intro hz
  exact projectiveProductFundamentalClass_ne_zero K hp
    ((ModuleCat.mono_iff_injective (projectiveProductTopLocalizationIso K hp P).hom).mp
      inferInstance (hz.trans (map_zero _).symm))

/-- The exact old boundary obligation, with the degree cast made explicit. -/
theorem canonicalProductLocalGenerator_boundary_zero (hp : 0 < ∑ i, K i) :
    relativeHomologyBoundary (subspaceInclusion
      ({firstCoordinateProduct K}ᶜ : Set (ProjectiveProduct K))) (2*(∑ i, K i)-1)
      ((show 2*(∑ i, K i) = (2*(∑ i, K i)-1)+1 by omega) ▸
        canonicalProductLocalGenerator K hp) = 0 := by
  rw [projectiveProductTopBoundary_zero K hp]
  rfl

end

end Kaplansky

end

end OAI
