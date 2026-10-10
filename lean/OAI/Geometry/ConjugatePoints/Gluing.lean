import OAI.Geometry.ConjugatePoints.Quotient

namespace OAI

noncomputable section

/-!
# Two-piece gluing, smooth charts, compactness, and orientation.
-/

open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups

open Set Topology TopologicalSpace CategoryTheory
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]

private def overlap (O : Opens X) : Bool → Bool → Opens X
  | false, false => ⊤
  | true, true => ⊤
  | false, true => O
  | true, false => O

private def transition (O : Opens X) (e : O ≃ₜ O) (i j : Bool) :
    (overlap O i j) → (overlap O j i) :=
  match i, j with
  | false, false => id
  | true, true => id
  | false, true => e
  | true, false => e.symm

private lemma transition_continuous (O : Opens X) (e : O ≃ₜ O) (i j : Bool) :
    Continuous (transition O e i j) := by
  cases i <;> cases j <;> first | exact continuous_id | exact e.continuous | exact e.symm.continuous

private lemma transition_inter (O : Opens X) (e : O ≃ₜ O) (i j k : Bool)
    (x : overlap O i j) (h : x.1 ∈ overlap O i k) :
    (transition O e i j x).1 ∈ overlap O j k := by
  cases i <;> cases j <;> cases k <;> first | exact h | exact (e x).2 | exact (e.symm x).2 | trivial

abbrev datum (O : Opens X) (e : O ≃ₜ O) : TopCat.GlueData :=
  TopCat.GlueData.mk' {
    J := Bool
    U := fun _ => TopCat.of X
    V := overlap O
    t := fun i j => TopCat.ofHom ⟨transition O e i j, transition_continuous O e i j⟩
    V_id := by intro i; cases i <;> rfl
    t_id := by intro i; cases i <;> rfl
    t_inter := by intro i j k x h; exact transition_inter O e i j k x h
    cocycle := by
      intro i j k x h
      change (transition O e j k ⟨(transition O e i j x).1,
        transition_inter O e i j k x h⟩).1 = (transition O e i k ⟨x.1,h⟩).1
      cases i <;> cases j <;> cases k <;> dsimp only [transition] <;> try rfl
      · exact congrArg Subtype.val (e.symm_apply_apply x)
      · exact congrArg Subtype.val (e.apply_symm_apply x)
  }

abbrev Space (O : Opens X) (e : O ≃ₜ O) := (datum O e).toGlueData.glued

def inclusion (O : Opens X) (e : O ≃ₜ O) (i : Bool) : X → Space O e :=
  (datum O e).toGlueData.ι i

lemma inclusion_openEmbedding (O : Opens X) (e : O ≃ₜ O) (i : Bool) :
    IsOpenEmbedding (inclusion O e i) := (datum O e).ι_isOpenEmbedding i

lemma inclusion_surjective (O : Opens X) (e : O ≃ₜ O) (x : Space O e) :
    ∃ i y, inclusion O e i y = x := (datum O e).ι_jointly_surjective x

lemma inclusion_mixed_eq (O : Opens X) (e : O ≃ₜ O) (x y : X) :
    inclusion O e false x = inclusion O e true y ↔
      ∃ hx : x ∈ O, (e ⟨x,hx⟩).1 = y := by
  refine ((datum O e).ι_eq_iff_rel (i := false) (j := true) x y).trans ?_
  change (∃ z : O, z.1 = x ∧ (e z).1 = y) ↔ _
  constructor
  · rintro ⟨⟨z,hz⟩,rfl,he⟩; exact ⟨hz,he⟩
  · rintro ⟨hx,he⟩; exact ⟨⟨x,hx⟩,rfl,he⟩

lemma inclusion_transition (O : Opens X) (e : O ≃ₜ O) (x : O) :
    inclusion O e false x.1 = inclusion O e true (e x).1 :=
  (inclusion_mixed_eq O e _ _).mpr ⟨x.2,rfl⟩

lemma inclusion_symm_transition (O : Opens X) (e : O ≃ₜ O) (x : O) :
    inclusion O e true x.1 = inclusion O e false (e.symm x).1 := by
  simpa only [e.apply_symm_apply] using (inclusion_transition O e (e.symm x)).symm

lemma space_connected (O : Opens X) (e : O ≃ₜ O) [ConnectedSpace X]
    (hO : (O : Set X).Nonempty) : ConnectedSpace (Space O e) := by
  rw [connectedSpace_iff_univ]
  have hf := isConnected_univ.image (inclusion O e false)
    (inclusion_openEmbedding O e false).continuous.continuousOn
  have ht := isConnected_univ.image (inclusion O e true)
    (inclusion_openEmbedding O e true).continuous.continuousOn
  have hcover : (inclusion O e false '' univ) ∪ (inclusion O e true '' univ) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,y,rfl⟩ := inclusion_surjective O e x
    cases i
    · exact Or.inl ⟨y,mem_univ _,rfl⟩
    · exact Or.inr ⟨y,mem_univ _,rfl⟩
  rw [← hcover]
  apply IsConnected.union ?_ hf ht
  obtain ⟨x,hx⟩ := hO
  exact ⟨inclusion O e false x,⟨x,mem_univ _,rfl⟩,
    ⟨(e ⟨x,hx⟩).1,mem_univ _,(inclusion_transition O e ⟨x,hx⟩).symm⟩⟩

def projection (O : Opens X) (e : O ≃ₜ O) : (Σ _ : Bool, X) → Space O e :=
  fun x => inclusion O e x.1 x.2

lemma projection_openQuotient (O : Opens X) (e : O ≃ₜ O) :
    IsOpenQuotientMap (projection O e) := by
  refine ⟨?_, continuous_sigma (fun i => (inclusion_openEmbedding O e i).continuous),
    isOpenMap_sigma.mpr (fun i => (inclusion_openEmbedding O e i).isOpenMap)⟩
  intro x
  obtain ⟨i,y,hy⟩ := inclusion_surjective O e x
  exact ⟨⟨i,y⟩,hy⟩

lemma space_secondCountable (O : Opens X) (e : O ≃ₜ O) [SecondCountableTopology X] :
    SecondCountableTopology (Space O e) :=
  (projection_openQuotient O e).secondCountableTopology

lemma same_piece_separation (O : Opens X) (e : O ≃ₜ O) [T2Space X] (i : Bool)
    {x y : X} (hne : inclusion O e i x ≠ inclusion O e i y) :
    ∃ U V : Set (Space O e), IsOpen U ∧ IsOpen V ∧
      inclusion O e i x ∈ U ∧ inclusion O e i y ∈ V ∧ Disjoint U V := by
  obtain ⟨U,V,hU,hV,hx,hy,hd⟩ := t2_separation (ne_of_apply_ne _ hne)
  refine ⟨inclusion O e i '' U,inclusion O e i '' V,
    (inclusion_openEmbedding O e i).isOpenMap _ hU,
    (inclusion_openEmbedding O e i).isOpenMap _ hV,
    ⟨x,hx,rfl⟩,⟨y,hy,rfl⟩, ?_⟩
  exact (Set.disjoint_image_iff (inclusion_openEmbedding O e i).injective).mpr hd

lemma mixed_separation (O : Opens X) (e : O ≃ₜ O) [T2Space X]
    (L : Set X) (hL : IsOpen L) (hOL : (O : Set X)ᶜ ⊆ L)
    (hsep : ∀ x : O, x.1 ∈ L → (e x).1 ∉ L) {x y : X}
    (hne : inclusion O e false x ≠ inclusion O e true y) :
    ∃ U V : Set (Space O e), IsOpen U ∧ IsOpen V ∧
      inclusion O e false x ∈ U ∧ inclusion O e true y ∈ V ∧ Disjoint U V := by
  by_cases hx : x ∈ O
  · rw [inclusion_transition O e ⟨x,hx⟩] at hne ⊢
    exact same_piece_separation O e true hne
  by_cases hy : y ∈ O
  · rw [inclusion_symm_transition O e ⟨y,hy⟩] at hne ⊢
    exact same_piece_separation O e false hne
  refine ⟨inclusion O e false '' L,inclusion O e true '' L,
    (inclusion_openEmbedding O e false).isOpenMap _ hL,
    (inclusion_openEmbedding O e true).isOpenMap _ hL,
    ⟨x,hOL hx,rfl⟩,⟨y,hOL hy,rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨u,hu,rfl⟩ ⟨v,hv,hv'⟩
  obtain ⟨huO,he⟩ := (inclusion_mixed_eq O e u v).mp hv'.symm
  exact hsep ⟨u,huO⟩ hu (he ▸ hv)

lemma space_t2 (O : Opens X) (e : O ≃ₜ O) [T2Space X]
    (L : Set X) (hL : IsOpen L) (hOL : (O : Set X)ᶜ ⊆ L)
    (hsep : ∀ x : O, x.1 ∈ L → (e x).1 ∉ L) : T2Space (Space O e) := by
  refine ⟨?_⟩
  intro x y hne
  obtain ⟨i,x,rfl⟩ := inclusion_surjective O e x
  obtain ⟨j,y,rfl⟩ := inclusion_surjective O e y
  cases i <;> cases j
  · exact same_piece_separation O e false hne
  · exact mixed_separation O e L hL hOL hsep hne
  · obtain ⟨U,V,hU,hV,hy,hx,hd⟩ := mixed_separation O e L hL hOL hsep hne.symm
    exact ⟨V,U,hV,hU,hx,hy,hd.symm⟩
  · exact same_piece_separation O e true hne

lemma space_compact (O : Opens X) (e : O ≃ₜ O) (K : Set X) (hK : IsCompact K)
    (hcover : ∀ x : X, x ∈ K ∨ ∃ hx : x ∈ O, (e ⟨x,hx⟩).1 ∈ K)
    (hcover' : ∀ x : X, x ∈ K ∨ ∃ hx : x ∈ O, (e.symm ⟨x,hx⟩).1 ∈ K) :
    CompactSpace (Space O e) := by
  refine ⟨?_⟩
  have he : (inclusion O e false '' K) ∪ (inclusion O e true '' K) = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨i,x,rfl⟩ := inclusion_surjective O e p
    cases i
    · rcases hcover x with hx | ⟨hx,hk⟩
      · exact Or.inl ⟨x,hx,rfl⟩
      · exact Or.inr ⟨(e ⟨x,hx⟩).1,hk,(inclusion_transition O e ⟨x,hx⟩).symm⟩
    · rcases hcover' x with hx | ⟨hx,hk⟩
      · exact Or.inr ⟨x,hx,rfl⟩
      · exact Or.inl ⟨(e.symm ⟨x,hx⟩).1,hk,(inclusion_symm_transition O e ⟨x,hx⟩).symm⟩
  rw [← he]
  exact (hK.image (inclusion_openEmbedding O e false).continuous).union
    (hK.image (inclusion_openEmbedding O e true).continuous)

end ThreeManifold.TwoGluing

open Set Topology TopologicalSpace
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

instance : Fact ((0 : ℝ) < 6) := ⟨by norm_num⟩
abbrev Circle := AddCircle (6 : ℝ)
abbrev Piece := OpenCore 8 × Circle
instance : T2Space (OpenCore 8) := inferInstanceAs
  (T2Space {x : Surface // height x < Real.log 8})
instance : SecondCountableTopology (OpenCore 8) :=
  @Subtype.secondCountableTopology Surface _ {x | height x < Real.log 8} surfaceSecondCountable

instance : ConnectedSpace Piece := by
  let : ConnectedSpace (OpenCore 8) := openCore_connected (by norm_num)
  infer_instance

def collar : Opens Piece := ⟨{x | x.1.1 ∈ cusp 2},
  (cusp_open 2).preimage (continuous_subtype_val.comp continuous_fst)⟩

lemma collar_height (x : collar) :
    height x.1.1.1 = Real.log ((cuspCoordinates 2 (by norm_num)
      ⟨x.1.1.1,x.2⟩).1 : ℝ) := by
  exact height_cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩

def collarCoordinates : collar ≃ₜ (Ioo (2 : ℝ) 8 × (Circle × Circle)) where
  toFun x :=
    (⟨((cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩).1 : ℝ),
      (cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩).1.2, by
      have hx := x.1.1.2
      rw [collar_height x] at hx
      exact (Real.log_lt_log_iff
        ((by norm_num : (0:ℝ)<2).trans (cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩).1.2)
        (by norm_num)).mp hx⟩,
      ((cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩).2,x.1.2))
  invFun p :=
    ⟨(⟨((cuspCoordinates 2 (by norm_num)).symm (⟨p.1.1,p.1.2.1⟩,p.2.1)).1, by
        rw [height_cuspCoordinates 2 (by norm_num), Homeomorph.apply_symm_apply]
        exact Real.log_lt_log ((by norm_num : (0:ℝ)<2).trans p.1.2.1) p.1.2.2⟩,p.2.2),
      ((cuspCoordinates 2 (by norm_num)).symm (⟨p.1.1,p.1.2.1⟩,p.2.1)).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change ((cuspCoordinates 2 (by norm_num)).symm
        ((cuspCoordinates 2 (by norm_num)) ⟨x.1.1.1,x.2⟩)).1 = x.1.1.1
      exact congrArg Subtype.val ((cuspCoordinates 2 (by norm_num)).symm_apply_apply ⟨x.1.1.1,x.2⟩)
    · rfl
  right_inv p := by
    have h := (cuspCoordinates 2 (by norm_num)).apply_symm_apply (⟨p.1.1,p.1.2.1⟩,p.2.1)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun q : Ioi (2 : ℝ) × Circle => q.1.1) h
    · exact Prod.ext (congrArg Prod.snd h) rfl
  continuous_toFun := by
    have hc : Continuous (fun x : collar => cuspCoordinates 2 (by norm_num) ⟨x.1.1.1,x.2⟩) :=
      (cuspCoordinates 2 (by norm_num)).continuous.comp (by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val)
    exact ((continuous_subtype_val.comp hc.fst).subtype_mk _).prodMk
      (hc.snd.prodMk (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply continuous_subtype_val.comp
      apply (cuspCoordinates 2 (by norm_num)).symm.continuous.comp
      exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
        (continuous_fst.comp continuous_snd)
    · exact continuous_snd.comp continuous_snd

lemma collarCoordinates_height (x : collar) :
    height x.1.1.1 = Real.log (collarCoordinates x).1.1 := collar_height x

def collarFlip : Ioo (2 : ℝ) 8 ≃ₜ Ioo (2 : ℝ) 8 where
  toFun x := ⟨16 / x.1, by
    constructor
    · exact (lt_div_iff₀ (by linarith [x.2.1])).mpr (by linarith [x.2.2])
    · exact (div_lt_iff₀ (by linarith [x.2.1])).mpr (by linarith [x.2.1])⟩
  invFun x := ⟨16 / x.1, by
    constructor
    · exact (lt_div_iff₀ (by linarith [x.2.1])).mpr (by linarith [x.2.2])
    · exact (div_lt_iff₀ (by linarith [x.2.1])).mpr (by linarith [x.2.1])⟩
  left_inv x := by apply Subtype.ext; dsimp; field_simp
  right_inv x := by apply Subtype.ext; dsimp; field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.div continuous_subtype_val
      (fun x => ne_of_gt (by linarith [x.2.1]))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.div continuous_subtype_val
      (fun x => ne_of_gt (by linarith [x.2.1]))

def torusShear : (Circle × Circle) ≃ₜ (Circle × Circle) where
  toFun z := (z.1 + z.2,z.1)
  invFun z := (z.2,z.1 - z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := (continuous_fst.add continuous_snd).prodMk continuous_fst
  continuous_invFun := continuous_snd.prodMk (continuous_fst.sub continuous_snd)

def gluingMap : collar ≃ₜ collar :=
  collarCoordinates.trans ((collarFlip.prodCongr torusShear.symm).trans collarCoordinates.symm)

lemma gluing_height (x : collar) :
    height (gluingMap x).1.1.1 = Real.log (16 / (collarCoordinates x).1.1) := by
  rw [collarCoordinates_height]
  simp only [gluingMap, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

lemma gluing_symm_height (x : collar) :
    height (gluingMap.symm x).1.1.1 = Real.log (16 / (collarCoordinates x).1.1) := by
  rw [collarCoordinates_height]
  change Real.log (collarCoordinates (collarCoordinates.symm
    ((collarFlip.prodCongr torusShear.symm).symm (collarCoordinates x)))).1.1 = _
  rw [Homeomorph.apply_symm_apply]
  rfl

abbrev Manifold := TwoGluing.Space collar gluingMap

def inclusion (i : Bool) : Piece → Manifold := TwoGluing.inclusion collar gluingMap i

def halfCore : Set Piece := {x | height x.1.1 ≤ Real.log 4}
lemma halfCore_compact : IsCompact halfCore := by
  have he : halfCore = ({x : OpenCore 8 | height x.1 ≤ Real.log 4} ×ˢ (univ : Set Circle)) := by
    ext x
    simp [halfCore]
  rw [he]
  exact (compact_core_slice (by norm_num) (by norm_num)).prod isCompact_univ

lemma collar_nonempty : (collar : Set Piece).Nonempty := by
  let p : Ioo (2 : ℝ) 8 × (Circle × Circle) := (⟨4,by norm_num,by norm_num⟩,(0,0))
  exact ⟨(collarCoordinates.symm p).1,(collarCoordinates.symm p).2⟩

instance : ConnectedSpace Manifold := TwoGluing.space_connected collar gluingMap collar_nonempty
instance : SecondCountableTopology Manifold := TwoGluing.space_secondCountable collar gluingMap

lemma halfCore_covers (x : Piece) :
    x ∈ halfCore ∨ ∃ hx : x ∈ collar, (gluingMap ⟨x,hx⟩).1 ∈ halfCore := by
  by_cases hx : x ∈ halfCore
  · exact Or.inl hx
  have hh : Real.log 4 < height x.1.1 := lt_of_not_ge hx
  have hO : x ∈ collar := (mem_cusp_iff_height (by norm_num : (1:ℝ)<2) _).mpr
    ((Real.log_lt_log (by norm_num) (by norm_num : (2:ℝ)<4)).trans hh)
  refine Or.inr ⟨hO,?_⟩
  change height (gluingMap ⟨x,hO⟩).1.1.1 ≤ Real.log 4
  rw [gluing_height]
  have hy : 4 < (collarCoordinates ⟨x,hO⟩).1.1 := by
    rw [collarCoordinates_height ⟨x,hO⟩] at hh
    exact (Real.log_lt_log_iff (by norm_num)
      (by linarith [(collarCoordinates ⟨x,hO⟩).1.2.1])).mp hh
  exact Real.log_le_log (by positivity) ((div_le_iff₀ (by linarith)).mpr (by linarith))

lemma halfCore_covers_symm (x : Piece) :
    x ∈ halfCore ∨ ∃ hx : x ∈ collar, (gluingMap.symm ⟨x,hx⟩).1 ∈ halfCore := by
  by_cases hx : x ∈ halfCore
  · exact Or.inl hx
  have hh : Real.log 4 < height x.1.1 := lt_of_not_ge hx
  have hO : x ∈ collar := (mem_cusp_iff_height (by norm_num : (1:ℝ)<2) _).mpr
    ((Real.log_lt_log (by norm_num) (by norm_num : (2:ℝ)<4)).trans hh)
  refine Or.inr ⟨hO,?_⟩
  change height (gluingMap.symm ⟨x,hO⟩).1.1.1 ≤ Real.log 4
  rw [gluing_symm_height]
  have hy : 4 < (collarCoordinates ⟨x,hO⟩).1.1 := by
    rw [collarCoordinates_height ⟨x,hO⟩] at hh
    exact (Real.log_lt_log_iff (by norm_num)
      (by linarith [(collarCoordinates ⟨x,hO⟩).1.2.1])).mp hh
  exact Real.log_le_log (by positivity) ((div_le_iff₀ (by linarith)).mpr (by linarith))

instance : CompactSpace Manifold := TwoGluing.space_compact collar gluingMap halfCore
  halfCore_compact halfCore_covers halfCore_covers_symm

instance : T2Space Manifold := by
  let L : Set Piece := {x | height x.1.1 < Real.log 4}
  apply TwoGluing.space_t2 collar gluingMap L
  · exact isOpen_lt (height_continuous.comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  · intro x hx
    have hh : height x.1.1 ≤ Real.log 2 :=
      le_of_not_gt ((mem_cusp_iff_height (by norm_num : (1:ℝ)<2) _).not.mp hx)
    exact hh.trans_lt (Real.log_lt_log (by norm_num) (by norm_num : (2:ℝ)<4))
  · intro x hx he
    change height x.1.1.1 < Real.log 4 at hx
    change height (gluingMap x).1.1.1 < Real.log 4 at he
    rw [collarCoordinates_height x] at hx
    rw [gluing_height] at he
    have hypos : 0 < (collarCoordinates x).1.1 := by linarith [(collarCoordinates x).1.2.1]
    have hy : (collarCoordinates x).1.1 < 4 :=
      (Real.log_lt_log_iff hypos (by norm_num)).mp hx
    have hg : 16 / (collarCoordinates x).1.1 < 4 :=
      (Real.log_lt_log_iff (by positivity) (by norm_num)).mp he
    have hgg := (div_lt_iff₀ hypos).mp hg
    linarith

end ThreeManifold.GluedConstruction
open Set Topology Filter Manifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
open QuotientConstruction
abbrev Deck (b : ℝ) := Multiplicative (AddSubgroup.zmultiples b)
lemma projection_cover (b : ℝ) : IsQuotientCoveringMap ((↑) : ℝ → AddCircle b) (Deck b) :=
  (AddCircle.isAddQuotientCoveringMap_coe b).toMultiplicative _
def sectionMap (b : ℝ) : AddCircle b → ℝ := Function.surjInv (projection_cover b).surjective
lemma section_spec (b : ℝ) : Function.RightInverse (sectionMap b) ((↑) : ℝ → AddCircle b) :=
  Function.rightInverse_surjInv (projection_cover b).surjective
lemma action_smooth (b : ℝ) (k : Deck b) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun x : ℝ => k • x) := by
  change ContMDiff _ _ _ (fun x : ℝ => (Multiplicative.toAdd k).val + x)
  exact contMDiff_const.add contMDiff_id
instance circleCharts (b : ℝ) : ChartedSpace ℝ (AddCircle b) :=
  manifoldCharts (projection_cover b) (section_spec b)
instance circleSmooth (b : ℝ) : IsManifold 𝓘(ℝ,ℝ) ∞ (AddCircle b) :=
  manifold_quotient_isManifold (projection_cover b) (section_spec b) (action_smooth b)
lemma projection_smooth (b : ℝ) : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ ((↑) : ℝ → AddCircle b) :=
  manifold_quotient_projection_smooth (projection_cover b) (section_spec b) (action_smooth b)
def localLift (b : ℝ) (x : AddCircle b) : OpenPartialHomeomorph (AddCircle b) ℝ :=
  (projection_cover b).isCoveringMap.isLocalHomeomorph.localInverseAt (sectionMap b x)
lemma localLift_source (b : ℝ) (x : AddCircle b) : x ∈ (localLift b x).source := by
  change x ∈ ((projection_cover b).isCoveringMap.isLocalHomeomorph.localInverseAt (sectionMap b x)).source
  simpa only [section_spec b x] using
    (projection_cover b).isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := sectionMap b x)
lemma localLift_smooth (b : ℝ) (x : AddCircle b) :
    ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (localLift b x) x :=
  local_lift_smoothAt (projection_cover b) (section_spec b) (action_smooth b)
    (sectionMap b x) (localLift_source b x)
lemma localLift_right (b : ℝ) (x : AddCircle b) {y : AddCircle b}
    (hy : y ∈ (localLift b x).source) : ((localLift b x y : ℝ) : AddCircle b) = y :=
  (projection_cover b).isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy
lemma localLift_eventually (b : ℝ) (x : AddCircle b) :
    (fun y => ((localLift b x y : ℝ) : AddCircle b)) =ᶠ[nhds x] id := by
  filter_upwards [(localLift b x).open_source.mem_nhds (localLift_source b x)] with y hy
  exact localLift_right b x hy

lemma addition_smooth (b : ℝ) : ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
    (fun p : AddCircle b × AddCircle b => p.1 + p.2) := by
  intro p
  have h1 := (localLift_smooth b p.1).comp p (contMDiffAt_fst (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ)))
  have h2 := (localLift_smooth b p.2).comp p (contMDiffAt_snd (I := 𝓘(ℝ,ℝ)) (J := 𝓘(ℝ,ℝ)))
  have h := (projection_smooth b _).comp p (h1.add h2)
  apply h.congr_of_eventuallyEq
  have he1 := (localLift_eventually b p.1).comp_tendsto continuous_fst.continuousAt
  have he2 := (localLift_eventually b p.2).comp_tendsto continuous_snd.continuousAt
  filter_upwards [he1,he2] with q hq1 hq2
  change q.1 + q.2 = (((localLift b p.1 q.1 + localLift b p.2 q.2 : ℝ)) : AddCircle b)
  change ((localLift b p.1 q.1 : ℝ) : AddCircle b) = q.1 at hq1
  change ((localLift b p.2 q.2 : ℝ) : AddCircle b) = q.2 at hq2
  rw [AddCircle.coe_add,hq1,hq2]

lemma negation_smooth (b : ℝ) : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞
    (fun p : AddCircle b => -p) := by
  intro p
  have h := (projection_smooth b _).comp p (localLift_smooth b p).neg
  apply h.congr_of_eventuallyEq
  filter_upwards [localLift_eventually b p] with q hq
  change -q = (((-localLift b p q : ℝ)) : AddCircle b)
  change ((localLift b p q : ℝ) : AddCircle b) = q at hq
  rw [AddCircle.coe_neg,hq]

end ThreeManifold.CircleConstruction
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
open QuotientConstruction

def cuspOpens (a : ℝ) : Opens Surface := ⟨cusp a,cusp_open a⟩
instance cuspCharts (a : ℝ) : ChartedSpace ℂ (cusp a) :=
  inferInstanceAs (ChartedSpace ℂ (cuspOpens a))
instance cuspSmooth (a : ℝ) : IsManifold 𝓘(ℝ,ℂ) ∞ (cusp a) :=
  inferInstanceAs (IsManifold 𝓘(ℝ,ℂ) ∞ (cuspOpens a))
def highOpens (a : ℝ) : Opens ℍ := ⟨{z | a < z.im},isOpen_lt continuous_const UpperHalfPlane.continuous_im⟩
instance highCharts (a : ℝ) : ChartedSpace ℂ {z : ℍ // a < z.im} :=
  inferInstanceAs (ChartedSpace ℂ (highOpens a))
instance highSmooth (a : ℝ) : IsManifold 𝓘(ℝ,ℂ) ∞ {z : ℍ // a < z.im} :=
  inferInstanceAs (IsManifold 𝓘(ℝ,ℂ) ∞ (highOpens a))
def rayOpens (a : ℝ) : Opens ℝ := ⟨Ioi a,isOpen_Ioi⟩
instance rayCharts (a : ℝ) : ChartedSpace ℝ (Ioi a) :=
  inferInstanceAs (ChartedSpace ℝ (rayOpens a))
instance raySmooth (a : ℝ) : IsManifold 𝓘(ℝ,ℝ) ∞ (Ioi a) :=
  inferInstanceAs (IsManifold 𝓘(ℝ,ℝ) ∞ (rayOpens a))
def coreOpens (a : ℝ) : Opens Surface := ⟨{x | height x < Real.log a},openCore_open a⟩
instance coreCharts (a : ℝ) : ChartedSpace ℂ (OpenCore a) :=
  inferInstanceAs (ChartedSpace ℂ (coreOpens a))
instance coreSmooth (a : ℝ) : IsManifold 𝓘(ℝ,ℂ) ∞ (OpenCore a) :=
  inferInstanceAs (IsManifold 𝓘(ℝ,ℂ) ∞ (coreOpens a))

lemma upperHalfPlane_coe_real_smooth :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ ((↑) : ℍ → ℂ) := by
  intro z
  have h := UpperHalfPlane.contMDiff_coe (n := ∞) z
  rw [contMDiffAt_iff] at h ⊢
  exact ⟨h.1,h.2.restrict_scalars ℝ⟩

lemma upperHalfPlane_im_smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ UpperHalfPlane.im :=
  Complex.imCLM.contDiff.contMDiff.comp upperHalfPlane_coe_real_smooth
lemma upperHalfPlane_re_smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ UpperHalfPlane.re :=
  Complex.reCLM.contDiff.contMDiff.comp upperHalfPlane_coe_real_smooth

lemma upperHalfPlane_ofComplex_real_smoothAt {z : ℂ} (hz : 0 < z.im) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ UpperHalfPlane.ofComplex z := by
  have h := UpperHalfPlane.contMDiffAt_ofComplex (n := ∞) hz
  rw [contMDiffAt_iff] at h ⊢
  exact ⟨h.1,h.2.restrict_scalars ℝ⟩

lemma highProjection_smooth (a : ℝ) :
    ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (highProjection a) := by
  apply (ContMDiff.subtypeVal_comp_iff (cuspOpens a) _).mp
  exact projection_smooth.comp (contMDiff_subtype_val (U := highOpens a))

lemma highCylinderProjection_smooth (a : ℝ) :
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞ (highCylinderProjection a) := by
  apply ContMDiff.prodMk
  · apply (ContMDiff.subtypeVal_comp_iff (rayOpens a) _).mp
    exact upperHalfPlane_im_smooth.comp (contMDiff_subtype_val (U := highOpens a))
  · exact (CircleConstruction.projection_smooth 6).comp
      (upperHalfPlane_re_smooth.comp (contMDiff_subtype_val (U := highOpens a)))

lemma cuspCoordinates_smooth (a : ℝ) (ha : 1 < a) :
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞ (cuspCoordinates a ha) := by
  intro x
  obtain ⟨z,hz,hzx⟩ := x.2
  let l := projection_cover.isCoveringMap.isLocalHomeomorph.localInverseAt z
  have hsrc : x.1 ∈ l.source := by
    rw [← hzx]
    exact projection_cover.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hls := local_lift_smoothAt projection_cover sectionMap_rightInverse effective_smooth z hsrc
  have hs := hls.comp x (contMDiff_subtype_val (I := 𝓘(ℝ,ℂ)) (n := ∞) (U := cuspOpens a) x)
  have hlx : l x.1 = z := by
    rw [← hzx]
    exact projection_cover.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have hhigh : ∀ᶠ q : cusp a in nhds x, a < (l q.1).im :=
    ((upperHalfPlane_im_smooth _).continuousAt.comp hs.continuousAt)
      (isOpen_Ioi.mem_nhds (by change a < (l x.1).im; rw [hlx]; exact hz))
  have hright : ∀ᶠ q : cusp a in nhds x, projection (l q.1) = q.1 := by
    filter_upwards [(contMDiff_subtype_val (I := 𝓘(ℝ,ℂ)) (n := ∞) (U := cuspOpens a) x).continuousAt
      (l.open_source.mem_nhds hsrc)] with q hq
    exact projection_cover.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hq
  have he : ∀ᶠ q : cusp a in nhds x,
      ((cuspCoordinates a ha q).1 : ℝ) = (l q.1).im ∧
      (cuspCoordinates a ha q).2 = ((l q.1).re : AddCircle (6 : ℝ)) := by
    filter_upwards [hhigh,hright] with q hq hr
    have hh : (⟨projection (l q.1),⟨l q.1,hq,rfl⟩⟩ : cusp a) = q := Subtype.ext hr
    have hc := cuspCoordinates_apply a ha (l q.1) hq
    rw [hh] at hc
    constructor
    · exact congrArg (fun p : Ioi a × AddCircle (6 : ℝ) => (p.1 : ℝ)) hc
    · exact congrArg Prod.snd hc
  apply ContMDiffAt.prodMk
  · apply (ContMDiffAt.subtypeVal_comp_iff (rayOpens a) _ x).mp
    exact ((upperHalfPlane_im_smooth _).comp x hs).congr_of_eventuallyEq
      (he.mono fun q hq => hq.1)
  · exact (((CircleConstruction.projection_smooth 6) _).comp x
      ((upperHalfPlane_re_smooth _).comp x hs)).congr_of_eventuallyEq
      (he.mono fun q hq => hq.2)

lemma cuspCoordinates_symm_smooth (a : ℝ) (ha : 1 < a) :
    ContMDiff (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℂ) ∞ (cuspCoordinates a ha).symm := by
  intro p
  apply (ContMDiffAt.subtypeVal_comp_iff (cuspOpens a) _ p).mp
  let l := CircleConstruction.localLift 6 p.2
  let c : Ioi a × AddCircle (6 : ℝ) → ℂ := fun q =>
    (l q.2 : ℂ) + (q.1.1 : ℂ) * Complex.I
  have h1 : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (fun q => l q.2) p :=
    (CircleConstruction.localLift_smooth 6 p.2).comp p contMDiffAt_snd
  have h2 : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (fun q : Ioi a × AddCircle (6 : ℝ) => q.1.1) p :=
    (contMDiff_subtype_val (U := rayOpens a) p.1).comp p contMDiffAt_fst
  have hmul : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun z : ℂ => z * Complex.I) :=
    (contDiff_id.mul contDiff_const).contMDiff
  have hc : ContMDiffAt (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℂ) ∞ c p :=
    ((Complex.ofRealCLM.contDiff.contMDiff _).comp p h1).add
      ((hmul _).comp p ((Complex.ofRealCLM.contDiff.contMDiff _).comp p h2))
  have hcim (q : Ioi a × AddCircle (6 : ℝ)) : (c q).im = q.1.1 := by
    simp [c]
  have hcpos (q : Ioi a × AddCircle (6 : ℝ)) : 0 < (c q).im := by
    rw [hcim]; exact (lt_trans (by linarith : 0 < a) q.1.2)
  have hsm := (projection_smooth _).comp p
    ((upperHalfPlane_ofComplex_real_smoothAt (hcpos p)).comp p hc)
  apply hsm.congr_of_eventuallyEq
  have hs := (CircleConstruction.localLift_eventually 6 p.2).comp_tendsto
    continuous_snd.continuousAt
  filter_upwards [hs] with q hq
  change ((cuspCoordinates a ha).symm q).1 = projection (UpperHalfPlane.ofComplex (c q))
  have hy : a < (UpperHalfPlane.ofComplex (c q)).im := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos (hcpos q), UpperHalfPlane.im, hcim, mem_Ioi] using q.1.2
  have hco := cuspCoordinates_apply a ha (UpperHalfPlane.ofComplex (c q)) hy
  have he : (⟨(UpperHalfPlane.ofComplex (c q)).im,hy⟩,
      ((UpperHalfPlane.ofComplex (c q)).re : AddCircle (6 : ℝ))) = q := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [UpperHalfPlane.ofComplex_apply_of_im_pos (hcpos q), UpperHalfPlane.im, hcim]
    · change ((l q.2 : ℝ) : AddCircle (6 : ℝ)) = q.2 at hq
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos (hcpos q), UpperHalfPlane.re, c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hq
  rw [he] at hco
  exact (congrArg Subtype.val ((cuspCoordinates a ha).injective
    ((cuspCoordinates a ha).apply_symm_apply q |>.trans hco.symm)))

end ThreeManifold.HyperbolicCore

open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)

def extendedTransition (x : X) : X := by
  classical
  exact if hx : x ∈ O then (e ⟨x,hx⟩).1 else x

lemma extendedTransition_apply (x : O) : extendedTransition O e x.1 = (e x).1 := by
  simp [extendedTransition, x.2]

omit [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma extendedTransition_smooth (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e) (x : O) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extendedTransition O e) x.1 := by
  apply (contMDiffAt_subtype_iff (U := O) (x := x)).mp
  have h := (contMDiff_subtype_val (I := 𝓘(ℝ,E)) (U := O)).comp he
  convert h x using 1
  exact funext (extendedTransition_apply O e)

def pieceChart (i : Bool) (x : X) : OpenPartialHomeomorph (Space O e) E :=
  (chartAt E x).lift_openEmbedding (inclusion_openEmbedding O e i)

def representative (p : Space O e) : Bool × X :=
  ⟨(inclusion_surjective O e p).choose, (inclusion_surjective O e p).choose_spec.choose⟩

lemma representative_spec (p : Space O e) :
    inclusion O e (representative O e p).1 (representative O e p).2 = p :=
  (inclusion_surjective O e p).choose_spec.choose_spec

@[instance_reducible]
def gluedCharts : ChartedSpace E (Space O e) where
  atlas := {c | ∃ i x, c = pieceChart (E := E) O e i x}
  chartAt p := pieceChart (E := E) O e (representative O e p).1 (representative O e p).2
  mem_chart_source p := by
    exact ⟨(representative O e p).2,mem_chart_source E _,representative_spec O e p⟩
  chart_mem_atlas p := ⟨_,_,rfl⟩

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma pieceChart_apply (i : Bool) (a x : X) :
    pieceChart (E := E) O e i a (inclusion O e i x) = chartAt E a x :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma pieceChart_mixed_germ (a b : X) {x : E}
    (hx : x ∈ (chartAt E a).target) (hO : (chartAt E a).symm x ∈ O) :
    (fun y => pieceChart (E := E) O e true b ((pieceChart (E := E) O e false a).symm y)) =ᶠ[nhds x]
      (fun y => chartAt E b (extendedTransition O e ((chartAt E a).symm y))) := by
  have hn : ∀ᶠ y in nhds x, (chartAt E a).symm y ∈ O :=
    ((chartAt E a).symm.continuousAt hx) (O.isOpen.mem_nhds hO)
  filter_upwards [hn] with y hy
  change pieceChart (E := E) O e true b (inclusion O e false ((chartAt E a).symm y)) = _
  rw [inclusion_transition O e ⟨_,hy⟩,pieceChart_apply]
  congr 1
  exact (extendedTransition_apply O e ⟨_,hy⟩).symm

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma pieceChart_mixed_symm_germ (a b : X) {x : E}
    (hx : x ∈ (chartAt E a).target) (hO : (chartAt E a).symm x ∈ O) :
    (fun y => pieceChart (E := E) O e false b ((pieceChart (E := E) O e true a).symm y)) =ᶠ[nhds x]
      (fun y => chartAt E b (extendedTransition O e.symm ((chartAt E a).symm y))) := by
  have hn : ∀ᶠ y in nhds x, (chartAt E a).symm y ∈ O :=
    ((chartAt E a).symm.continuousAt hx) (O.isOpen.mem_nhds hO)
  filter_upwards [hn] with y hy
  change pieceChart (E := E) O e false b (inclusion O e true ((chartAt E a).symm y)) = _
  rw [inclusion_symm_transition O e ⟨_,hy⟩,pieceChart_apply]
  congr 1
  exact (extendedTransition_apply O e.symm ⟨_,hy⟩).symm

lemma same_chart_smooth (i : Bool) (a b : X) {x : E}
    (hx : x ∈ (chartAt E a).target)
    (hy : (pieceChart (E := E) O e i a).symm x ∈ (pieceChart (E := E) O e i b).source) :
    ContDiffAt ℝ ∞ (fun y => pieceChart (E := E) O e i b ((pieceChart (E := E) O e i a).symm y)) x := by
  obtain ⟨y,hy,he⟩ := hy
  have hey : y = (chartAt E a).symm x := (inclusion_openEmbedding O e i).injective he
  subst y
  have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) a) hx
  have h2 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) b) hy
  convert (h2.comp x h1).contDiffAt using 1
  exact funext (fun z => pieceChart_apply O e i b ((chartAt E a).symm z))

lemma mixed_chart_smooth (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e)
    (a b : X) {x : E} (hx : x ∈ (chartAt E a).target)
    (hy : (pieceChart (E := E) O e false a).symm x ∈ (pieceChart (E := E) O e true b).source) :
    ContDiffAt ℝ ∞ (fun y => pieceChart (E := E) O e true b ((pieceChart (E := E) O e false a).symm y)) x := by
  obtain ⟨y,hy,hey⟩ := hy
  obtain ⟨hO,hye⟩ := (inclusion_mixed_eq O e _ _).mp hey.symm
  have htr := extendedTransition_apply O e ⟨(chartAt E a).symm x,hO⟩
  have hb : extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source :=
    (htr.trans hye) ▸ hy
  have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) a) hx
  have h2 := extendedTransition_smooth O e he ⟨_,hO⟩
  have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) b) hb
  exact ((h3.comp x (h2.comp x h1)).contDiffAt).congr_of_eventuallyEq
    (pieceChart_mixed_germ O e a b hx hO)

lemma mixed_symm_chart_smooth (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm)
    (a b : X) {x : E} (hx : x ∈ (chartAt E a).target)
    (hy : (pieceChart (E := E) O e true a).symm x ∈ (pieceChart (E := E) O e false b).source) :
    ContDiffAt ℝ ∞ (fun y => pieceChart (E := E) O e false b ((pieceChart (E := E) O e true a).symm y)) x := by
  obtain ⟨y,hy,hey⟩ := hy
  obtain ⟨hyO,hye⟩ := (inclusion_mixed_eq O e _ _).mp hey
  have hO : (chartAt E a).symm x ∈ O := by
    change (chartAt E a).invFun x ∈ O
    rw [← hye]
    exact (e ⟨y,hyO⟩).2
  have hye' : (e.symm ⟨(chartAt E a).symm x,hO⟩).1 = y := by
    have hh : (⟨(chartAt E a).symm x,hO⟩ : O) = e ⟨y,hyO⟩ := Subtype.ext hye.symm
    rw [hh,e.symm_apply_apply]
  have htr := extendedTransition_apply O e.symm ⟨(chartAt E a).symm x,hO⟩
  have hb : extendedTransition O e.symm ((chartAt E a).symm x) ∈ (chartAt E b).source :=
    (htr.trans hye') ▸ hy
  have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) a) hx
  have h2 := extendedTransition_smooth O e.symm he ⟨_,hO⟩
  have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) b) hb
  exact ((h3.comp x (h2.comp x h1)).contDiffAt).congr_of_eventuallyEq
    (pieceChart_mixed_symm_germ O e a b hx hO)

lemma glued_isManifold (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e)
    (hei : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm) :
    let := gluedCharts (E := E) O e
    IsManifold 𝓘(ℝ,E) ∞ (Space O e) := by
  let := gluedCharts (E := E) O e
  apply isManifold_of_contDiffOn
  intro c d hc hd
  obtain ⟨i,a,rfl⟩ := hc
  obtain ⟨j,b,rfl⟩ := hd
  intro x hx
  simp only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def,id_eq,preimage_id_eq,range_id,inter_univ] at hx ⊢
  have ha : x ∈ (chartAt E a).target := hx.1
  apply ContDiffAt.contDiffWithinAt
  cases i <;> cases j
  · exact same_chart_smooth O e false a b ha hx.2
  · exact mixed_chart_smooth O e he a b ha hx.2
  · exact mixed_symm_chart_smooth O e hei a b ha hx.2
  · exact same_chart_smooth O e true a b ha hx.2

end ThreeManifold.TwoGluing
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
open HyperbolicCore
abbrev IP := 𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℝ)
abbrev IT := 𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)
abbrev IC := 𝓘(ℝ,ℝ).prod IT

def bandOpens : Opens ℝ := ⟨Ioo (2:ℝ) 8,isOpen_Ioo⟩
instance bandCharts : ChartedSpace ℝ (Ioo (2:ℝ) 8) :=
  inferInstanceAs (ChartedSpace ℝ bandOpens)
instance bandSmooth : IsManifold 𝓘(ℝ,ℝ) ∞ (Ioo (2:ℝ) 8) :=
  inferInstanceAs (IsManifold 𝓘(ℝ,ℝ) ∞ bandOpens)

lemma collarCoordinates_smooth : ContMDiff IP IC ∞ collarCoordinates := by
  have hpiece : ContMDiff IP IP ∞ (fun x : collar => x.1) :=
    contMDiff_subtype_val (U := collar)
  have hcore := contMDiff_fst.comp hpiece
  have hsurf := (contMDiff_subtype_val (U := coreOpens 8)).comp hcore
  have hsub : ContMDiff IP 𝓘(ℝ,ℂ) ∞ (fun x : collar => (⟨x.1.1.1,x.2⟩ : cusp 2)) :=
    (ContMDiff.subtypeVal_comp_iff (cuspOpens 2) _).mp hsurf
  have hc := (cuspCoordinates_smooth 2 (by norm_num)).comp hsub
  apply ContMDiff.prodMk
  · apply (ContMDiff.subtypeVal_comp_iff bandOpens _).mp
    exact (contMDiff_subtype_val (U := rayOpens 2)).comp hc.fst
  · exact hc.snd.prodMk (contMDiff_snd.comp hpiece)

lemma collarCoordinates_symm_smooth : ContMDiff IC IP ∞ collarCoordinates.symm := by
  have hh : ContMDiff IC 𝓘(ℝ,ℝ) ∞ (fun p : Ioo (2:ℝ) 8 × (Circle × Circle) => p.1.1) :=
    (contMDiff_subtype_val (U := bandOpens)).comp contMDiff_fst
  have hlo : ContMDiff IC 𝓘(ℝ,ℝ) ∞ (fun p : Ioo (2:ℝ) 8 × (Circle × Circle) =>
      (⟨p.1.1,p.1.2.1⟩ : Ioi (2:ℝ))) :=
    (ContMDiff.subtypeVal_comp_iff (rayOpens 2) _).mp hh
  have hc := (cuspCoordinates_symm_smooth 2 (by norm_num)).comp
    (hlo.prodMk (contMDiff_fst.comp contMDiff_snd))
  apply (ContMDiff.subtypeVal_comp_iff collar _).mp
  apply ContMDiff.prodMk
  · apply (ContMDiff.subtypeVal_comp_iff (coreOpens 8) _).mp
    exact (contMDiff_subtype_val (U := cuspOpens 2)).comp hc
  · exact contMDiff_snd.comp contMDiff_snd

lemma collarFlip_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ collarFlip := by
  apply (ContMDiff.subtypeVal_comp_iff bandOpens _).mp
  change ContMDiff _ _ _ (fun x : Ioo (2:ℝ) 8 => 16 / x.1)
  exact contMDiff_const.div₀ (contMDiff_subtype_val (U := bandOpens))
    (fun x => ne_of_gt (lt_trans (by norm_num) x.2.1))

lemma collarFlip_symm_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ collarFlip.symm :=
  collarFlip_smooth

lemma torusShear_smooth : ContMDiff IT IT ∞ torusShear :=
  (CircleConstruction.addition_smooth 6).prodMk contMDiff_fst

lemma torusShear_symm_smooth : ContMDiff IT IT ∞ torusShear.symm := by
  have hn : ContMDiff IT 𝓘(ℝ,ℝ) ∞ (fun p : Circle × Circle => -p.2) :=
    (CircleConstruction.negation_smooth 6).comp contMDiff_snd
  have ha := (CircleConstruction.addition_smooth 6).comp (contMDiff_fst.prodMk hn)
  change ContMDiff IT IT ∞ (fun p : Circle × Circle => (p.2,p.1 - p.2))
  simpa only [sub_eq_add_neg, Function.comp_def] using contMDiff_snd.prodMk ha

lemma gluingMap_smooth : ContMDiff IP IP ∞ gluingMap := by
  exact collarCoordinates_symm_smooth.comp
    (((collarFlip_smooth.comp contMDiff_fst).prodMk
      (torusShear_symm_smooth.comp contMDiff_snd)).comp collarCoordinates_smooth)

lemma gluingMap_symm_smooth : ContMDiff IP IP ∞ gluingMap.symm := by
  exact collarCoordinates_symm_smooth.comp
    (((collarFlip_symm_smooth.comp contMDiff_fst).prodMk
      (torusShear_smooth.comp contMDiff_snd)).comp collarCoordinates_smooth)

instance pieceSelfCharts : ChartedSpace (ℂ × ℝ) Piece :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ℝ) Piece)

instance pieceSelfSmooth : IsManifold 𝓘(ℝ,ℂ × ℝ) ∞ Piece := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,ℂ)) (I' := 𝓘(ℝ,ℝ)) (OpenCore 8) Circle

instance manifoldCharts : ChartedSpace (ℂ × ℝ) Manifold :=
  TwoGluing.gluedCharts collar gluingMap

instance manifoldSmooth : IsManifold 𝓘(ℝ,ℂ × ℝ) ∞ Manifold := by
  apply TwoGluing.glued_isManifold (E := ℂ × ℝ) collar gluingMap
  · simpa only [modelWithCornersSelf_prod] using gluingMap_smooth
  · simpa only [modelWithCornersSelf_prod] using gluingMap_symm_smooth

end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.AtlasOrientation

section
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]

def Positive : Prop :=
  ∀ c d : OpenPartialHomeomorph M E, c ∈ atlas E M → d ∈ atlas E M →
    ∀ x ∈ c.target, c.symm x ∈ d.source →
      0 < LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap

lemma transition_contDiffAt [IsManifold 𝓘(ℝ,E) ∞ M]
    {c d : OpenPartialHomeomorph M E} (hc : c ∈ atlas E M) (hd : d ∈ atlas E M)
    {x : E} (hx : x ∈ c.target) (hy : c.symm x ∈ d.source) :
    ContDiffAt ℝ ∞ (d ∘ c.symm) x :=
  ((contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E)) (subset_maximalAtlas (n := ∞) hd) hy).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E)) (subset_maximalAtlas (n := ∞) hc) hx)).contDiffAt

lemma product [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N]
    (hM : Positive (E := E) (M := M)) (hN : Positive (E := F) (M := N)) :
    @Positive (E × F) (M × N) _ _ _ (prodChartedSpace E M F N) := by
  intro a b ha hb x hx hy
  obtain ⟨c,hc,d,hd,rfl⟩ := ha
  obtain ⟨c',hc',d',hd',rfl⟩ := hb
  have h1 := (transition_contDiffAt hc hc' hx.1 hy.1).differentiableAt (by simp)
  have h2 := (transition_contDiffAt hd hd' hx.2 hy.2).differentiableAt (by simp)
  change 0 < LinearMap.det (fderiv ℝ (Prod.map (c' ∘ c.symm) (d' ∘ d.symm)) x).toLinearMap
  rw [(HasFDerivAt.prodMap x h1.hasFDerivAt h2.hasFDerivAt).fderiv]
  change (0 : ℝ) < LinearMap.det ((fderiv ℝ (c' ∘ c.symm) x.1).toLinearMap.prodMap
    (fderiv ℝ (d' ∘ d.symm) x.2).toLinearMap)
  rw [LinearMap.det_prodMap]
  exact mul_pos (hM c c' hc hc' x.1 hx.1 hy.1) (hN d d' hd hd' x.2 hx.2 hy.2)

lemma open_subset (U : TopologicalSpace.Opens M) (hM : Positive (E := E) (M := M)) :
    Positive (E := E) (M := U) := by
  classical
  by_cases hU : Nonempty U
  swap
  · intro c d hc hd x hx hy
    exact (hU ⟨c.symm x⟩).elim
  intro c d hc hd x hx hy
  obtain ⟨a,rfl⟩ := TopologicalSpace.Opens.chart_eq hU hc
  obtain ⟨b,rfl⟩ := TopologicalSpace.Opens.chart_eq hU hd
  have hy' : (chartAt E a.1).symm x ∈ (chartAt E b.1).source := by
    rw [← (chartAt E a.1).subtypeRestr_symm_apply hU hx]
    exact hy.2
  have hg : ((chartAt E b.1).subtypeRestr hU ∘ ((chartAt E a.1).subtypeRestr hU).symm)
      =ᶠ[nhds x] (chartAt E b.1 ∘ (chartAt E a.1).symm) := by
    filter_upwards [((chartAt E a.1).subtypeRestr hU).open_target.mem_nhds hx] with y hy
    change chartAt E b.1 ((((chartAt E a.1).subtypeRestr hU).symm y).1) = _
    rw [← Function.comp_apply (f := Subtype.val),
      (chartAt E a.1).subtypeRestr_symm_apply hU hy]
    rfl
  rw [hg.fderiv_eq]
  exact hM _ _ (chart_mem_atlas E a.1) (chart_mem_atlas E b.1) x hx.1 hy'

end

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma transition_det_mul {c d : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hd : d ∈ atlas E M) {x : E}
    (hx : x ∈ c.target) (hy : c.symm x ∈ d.source) :
    LinearMap.det (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).toLinearMap *
      LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap = 1 := by
  have h1 := (transition_contDiffAt hc hd hx hy).differentiableAt (by simp)
  have hyt : d (c.symm x) ∈ d.target := d.map_source hy
  have hys : d.symm (d (c.symm x)) ∈ c.source := by
    rw [d.left_inv hy]
    exact c.map_target hx
  have h2 := (transition_contDiffAt hd hc hyt hys).differentiableAt (by simp)
  have he : ((c ∘ d.symm) ∘ (d ∘ c.symm)) =ᶠ[nhds x] id := by
    filter_upwards [c.open_target.mem_nhds hx,
      c.symm.continuousAt hx (d.open_source.mem_nhds hy)] with y hy1 hy2
    simp only [Function.comp_apply,id_eq,d.left_inv hy2,c.right_inv hy1]
  have hh := h2.hasFDerivAt.comp x h1.hasFDerivAt
  have hid : (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).comp
      (fderiv ℝ (d ∘ c.symm) x) = ContinuousLinearMap.id ℝ E := by
    exact (hh.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_id x)
  rw [← LinearMap.det_comp]
  change LinearMap.det ((fderiv ℝ (c ∘ d.symm) (d (c.symm x))).comp
    (fderiv ℝ (d ∘ c.symm) x)).toLinearMap = 1
  rw [hid]
  exact LinearMap.det_id

lemma reverse_positive {c d : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hd : d ∈ atlas E M) {x : E}
    (hx : x ∈ c.target) (hy : c.symm x ∈ d.source)
    (h : 0 < LinearMap.det (fderiv ℝ (d ∘ c.symm) x).toLinearMap) :
    0 < LinearMap.det (fderiv ℝ (c ∘ d.symm) (d (c.symm x))).toLinearMap := by
  have hm := transition_det_mul hc hd hx hy
  exact pos_of_mul_pos_left (by rw [hm]; norm_num) h.le
end ThreeManifold.AtlasOrientation

open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.QuotientConstruction
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
  [Group G] [MulAction G M] {p : M → Q} (hp : IsQuotientCoveringMap p G)

lemma manifold_quotient_positive {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, Continuous (fun x : M => k • x))
    (hpos : ∀ (k : G) (a b : M) (x : E), x ∈ (chartAt E a).target →
      k • (chartAt E a).symm x ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (k • (chartAt E a).symm y)) x).toLinearMap) :
    let := manifoldCharts (E := E) hp hσ
    AtlasOrientation.Positive (E := E) (M := Q) := by
  let := manifoldCharts (E := E) hp hσ
  change AtlasOrientation.Positive (E := E) (M := Q)
  intro c d hc hd x hx hy
  obtain ⟨a,rfl⟩ := hc
  obtain ⟨b,rfl⟩ := hd
  let ca := chartAt E (σ a)
  let cb := chartAt E (σ b)
  let la := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ a)
  let lb := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ b)
  have ha : x ∈ ca.target := hx.1
  have hb : p (ca.symm x) ∈ lb.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def] using hy.1
  have hb' : lb (p (ca.symm x)) ∈ cb.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def, mem_preimage] using hy.2
  obtain ⟨k,hk⟩ := cover_lift_eventuallyEq_action hp hact (σ b) hb
  have hks : k • ca.symm x ∈ cb.source := hk.eq_of_nhds ▸ hb'
  have he : ((lb.trans cb) ∘ (la.trans ca).symm) =ᶠ[nhds x]
      (fun y => cb (k • ca.symm y)) := by
    have hh := hk.comp_tendsto (ca.symm.continuousAt ha)
    filter_upwards [hh] with y hy
    simp only [la, lb, OpenPartialHomeomorph.coe_trans,OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm,Function.comp_def]
    exact congrArg cb hy
  rw [he.fderiv_eq]
  exact hpos k (σ a) (σ b) x ha hks

lemma manifold_projection_positive {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, Continuous (fun x : M => k • x))
    (hpos : ∀ (k : G) (a b : M) (x : E), x ∈ (chartAt E a).target →
      k • (chartAt E a).symm x ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (k • (chartAt E a).symm y)) x).toLinearMap) :
    let := manifoldCharts (E := E) hp hσ
    ∀ (a : M) (b : Q) (x : E), x ∈ (chartAt E a).target →
      p ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (p ((chartAt E a).symm y))) x).toLinearMap := by
  let := manifoldCharts (E := E) hp hσ
  change ∀ (a : M) (b : Q) (x : E), _ → _ → _
  intro a b x hx hy
  let ca := chartAt E a
  let cb := chartAt E (σ b)
  let lb := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ b)
  have hb : p (ca.symm x) ∈ lb.source := hy.1
  have hb' : lb (p (ca.symm x)) ∈ cb.source := hy.2
  obtain ⟨k,hk⟩ := cover_lift_eventuallyEq_action hp hact (σ b) hb
  have hks : k • ca.symm x ∈ cb.source := hk.eq_of_nhds ▸ hb'
  have he : (fun y => chartAt E b (p (ca.symm y))) =ᶠ[nhds x]
      (fun y => cb (k • ca.symm y)) := by
    filter_upwards [hk.comp_tendsto (ca.symm.continuousAt hx)] with y hy
    exact congrArg cb hy
  rw [he.fderiv_eq]
  exact hpos k a (σ b) x hx hks
end ThreeManifold.QuotientConstruction
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
lemma action_orientation (g : SL(2,ℤ)) (a b : ℍ) (x : ℂ)
    (hx : x ∈ (chartAt ℂ a).target) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt ℂ b (g • (chartAt ℂ a).symm y)) x).toLinearMap := by
  let z := (chartAt ℂ a).symm x
  have hz : (z : ℂ) = x := (chartAt ℂ a).right_inv hx
  have he : (fun y => chartAt ℂ b (g • (chartAt ℂ a).symm y)) =ᶠ[nhds x]
      (fun y => ((SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.ofComplex y : ℍ) : ℂ)) := by
    filter_upwards [(chartAt ℂ a).open_target.mem_nhds hx] with y hy
    have hy' : ((chartAt ℂ a).symm y : ℂ) = y := (chartAt ℂ a).right_inv hy
    have ho : UpperHalfPlane.ofComplex y = (chartAt ℂ a).symm y := by
      exact (congrArg UpperHalfPlane.ofComplex hy'.symm).trans
        (UpperHalfPlane.ofComplex_apply _)
    rw [ho]
    rfl
  rw [he.fderiv_eq]
  have hd := (UpperHalfPlane.hasStrictFDerivAt_smul (SpecialLinearGroup.mapGL ℝ g) z).hasFDerivAt
  rw [hz] at hd
  rw [hd.fderiv]
  change 0 < (UpperHalfPlane.smulFDeriv _ x).det
  rw [UpperHalfPlane.det_smulFDeriv]
  have hdet : (SpecialLinearGroup.mapGL ℝ g).det.val = 1 := by
    exact mapGL_det g
  have hn : 0 < ‖UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) x‖ := by
    rw [← hz]
    exact norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero _ z)
  simp only [hdet, one_pow, mul_one, sign_one]
  change (0 : ℝ) < 1 / ‖UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) x‖ ^ 4
  positivity

lemma surface_positive : AtlasOrientation.Positive (E := ℂ) (M := Surface) := by
  apply QuotientConstruction.manifold_quotient_positive projection_cover sectionMap_rightInverse
    (fun k => (effective_smooth k).continuous)
  intro k a b x hx hy
  obtain ⟨g,rfl⟩ := effect_surjective k
  exact action_orientation g.val a b x hx
end ThreeManifold.HyperbolicCore
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
lemma positive (b : ℝ) : AtlasOrientation.Positive (E := ℝ) (M := AddCircle b) := by
  apply QuotientConstruction.manifold_quotient_positive (projection_cover b) (section_spec b)
    (fun k => (action_smooth b k).continuous)
  intro k a c x hx hy
  change 0 < LinearMap.det (fderiv ℝ ((fun _ : ℝ => (Multiplicative.toAdd k).val) + id) x).toLinearMap
  rw [(hasFDerivAt_const (𝕜 := ℝ) (Multiplicative.toAdd k).val x |>.add (hasFDerivAt_id x)).fderiv]
  simp
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
lemma piece_positive : AtlasOrientation.Positive (E := ℂ × ℝ) (M := Piece) := by
  exact AtlasOrientation.product (AtlasOrientation.open_subset (HyperbolicCore.coreOpens 8)
    HyperbolicCore.surface_positive) (CircleConstruction.positive 6)
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.HyperbolicCore
lemma projection_chart_positive (b : Surface) (z : ℍ)
    (hy : projection z ∈ (chartAt ℂ b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y : ℂ => chartAt ℂ b (projection (UpperHalfPlane.ofComplex y))) (z : ℂ)).toLinearMap := by
  have hpos := QuotientConstruction.manifold_projection_positive projection_cover
    sectionMap_rightInverse (fun k => (effective_smooth k).continuous)
    (fun k a b x hx hy => by
      obtain ⟨g,rfl⟩ := effect_surjective k
      exact action_orientation g.val a b x hx)
  have hx : (z : ℂ) ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source (mem_chart_source ℂ z)
  have hz : (chartAt ℂ z).symm (z : ℂ) = z := (chartAt ℂ z).left_inv (mem_chart_source ℂ z)
  have he : (fun y : ℂ => chartAt ℂ b (projection (UpperHalfPlane.ofComplex y))) =ᶠ[nhds (z : ℂ)]
      (fun y => chartAt ℂ b (projection ((chartAt ℂ z).symm y))) := by
    filter_upwards [(chartAt ℂ z).open_target.mem_nhds hx] with y hy
    have hy' : ((chartAt ℂ z).symm y : ℂ) = y := (chartAt ℂ z).right_inv hy
    have ho : UpperHalfPlane.ofComplex y = (chartAt ℂ z).symm y :=
      (congrArg UpperHalfPlane.ofComplex hy'.symm).trans (UpperHalfPlane.ofComplex_apply _)
    rw [ho]
  rw [he.fderiv_eq]
  exact hpos z b (z : ℂ) hx (by rw [hz]; exact hy)
end ThreeManifold.HyperbolicCore
namespace ThreeManifold.CircleConstruction
lemma projection_chart_positive (b : ℝ) (a : AddCircle b) (r : ℝ)
    (hr : (r : AddCircle b) ∈ (chartAt ℝ a).source) :
    0 < LinearMap.det (fderiv ℝ (fun t : ℝ => chartAt ℝ a (t : AddCircle b)) r).toLinearMap := by
  have hpos := QuotientConstruction.manifold_projection_positive (projection_cover b) (section_spec b)
    (fun k => (action_smooth b k).continuous) (fun k a c x hx hy => by
      change 0 < LinearMap.det (fderiv ℝ ((fun _ : ℝ => (Multiplicative.toAdd k).val) + id) x).toLinearMap
      rw [(hasFDerivAt_const (𝕜 := ℝ) (Multiplicative.toAdd k).val x |>.add (hasFDerivAt_id x)).fderiv]
      simp)
  exact hpos r a r (mem_univ _) hr
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

def coverChart (b : Piece) : ℂ × ℝ → ℂ × ℝ :=
  Prod.map (fun z => chartAt ℂ b.1.1 (projection (UpperHalfPlane.ofComplex z)))
    (fun t => chartAt ℝ b.2 (t : Circle))

lemma coverChart_component_smooth (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    ContDiffAt ℝ ∞ (fun y : ℂ => chartAt ℂ b.1.1 (projection (UpperHalfPlane.ofComplex y))) (z : ℂ) ∧
    ContDiffAt ℝ ∞ (fun t : ℝ => chartAt ℝ b.2 (t : Circle)) r := by
  constructor
  · have h1 := upperHalfPlane_ofComplex_real_smoothAt z.im_pos
    have h2 := projection_smooth z
    have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℂ)) (n := ∞) b.1.1) hz
    have hh : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (chartAt ℂ b.1.1 ∘ projection)
        (UpperHalfPlane.ofComplex (z : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using h3.comp z h2
    exact (hh.comp (z : ℂ) h1).contDiffAt
  · have h2 := CircleConstruction.projection_smooth 6 r
    have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,ℝ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℝ)) (n := ∞) b.2) hr
    exact (h3.comp r h2).contDiffAt

lemma coverChart_positive (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    0 < LinearMap.det (fderiv ℝ (coverChart b) ((z : ℂ),r)).toLinearMap := by
  obtain ⟨h1,h2⟩ := coverChart_component_smooth b z r hz hr
  have hd := HasFDerivAt.prodMap ((z : ℂ),r)
    (h1.differentiableAt (by simp)).hasFDerivAt (h2.differentiableAt (by simp)).hasFDerivAt
  change 0 < LinearMap.det (fderiv ℝ (Prod.map _ _) ((z : ℂ),r)).toLinearMap
  rw [hd.fderiv]
  change (0 : ℝ) < LinearMap.det ((fderiv ℝ _ (z : ℂ)).toLinearMap.prodMap
    (fderiv ℝ _ r).toLinearMap)
  rw [LinearMap.det_prodMap]
  exact mul_pos (HyperbolicCore.projection_chart_positive _ z hz)
    (CircleConstruction.projection_chart_positive 6 _ r hr)

lemma coverChart_smooth (b : Piece) (z : ℍ) (r : ℝ)
    (hz : projection z ∈ (chartAt ℂ b.1.1).source)
    (hr : (r : Circle) ∈ (chartAt ℝ b.2).source) :
    ContDiffAt ℝ ∞ (coverChart b) ((z : ℂ),r) := by
  obtain ⟨h1,h2⟩ := coverChart_component_smooth b z r hz hr
  exact h1.prodMap h2

lemma coverChart_apply (b : Piece) (z : ℍ) (r : ℝ)
    (hz : height (projection z) < Real.log 8) :
    coverChart b ((z : ℂ),r) = chartAt (ℂ × ℝ) b ((⟨projection z,hz⟩ : OpenCore 8),(r : Circle)) := by
  simp only [coverChart,Prod.map_apply,UpperHalfPlane.ofComplex_apply]
  rfl
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

def neckLift (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) : collar :=
  ⟨(⟨projection z,by
      rw [height_projection_high (by linarith [hz.1])]
      exact Real.log_lt_log z.im_pos hz.2⟩,(r : Circle)),⟨z,hz.1,rfl⟩⟩

lemma neckLift_coordinates (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    collarCoordinates (neckLift z hz r) = (⟨z.im,hz⟩,((z.re : Circle),(r : Circle))) := by
  have hh := cuspCoordinates_apply 2 (by norm_num) z hz.1
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p : Ioi (2 : ℝ) × Circle => p.1.1) hh
  · exact Prod.ext (congrArg Prod.snd hh) rfl

lemma neckLift_surjective (x : collar) :
    ∃ (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ), neckLift z hz r = x := by
  obtain ⟨z,hz,hzx⟩ := x.2
  change (2 : ℝ) < z.im at hz
  obtain ⟨r,hr⟩ := (CircleConstruction.projection_cover 6).surjective x.1.2
  have hlt : z.im < 8 := by
    have h := x.1.1.2
    rw [← hzx,height_projection_high (by linarith)] at h
    exact (Real.log_lt_log_iff z.im_pos (by norm_num)).mp h
  refine ⟨z,⟨hz,hlt⟩,r,?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hzx) hr

def flipUpper (z : ℍ) (r : ℝ) : ℍ :=
  ⟨(r : ℂ) + (16 / z.im : ℝ) * Complex.I,by simp; positivity⟩
@[simp] lemma flipUpper_im (z : ℍ) (r : ℝ) : (flipUpper z r).im = 16 / z.im := by
  change ((r : ℂ) + (16 / z.im : ℝ) * Complex.I).im = _
  simp
@[simp] lemma flipUpper_re (z : ℍ) (r : ℝ) : (flipUpper z r).re = r := by
  change ((r : ℂ) + (16 / z.im : ℝ) * Complex.I).re = _
  simp
lemma flipUpper_band (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    (2 : ℝ) < (flipUpper z r).im ∧ (flipUpper z r).im < 8 := by
  rw [flipUpper_im]
  exact (collarFlip ⟨z.im,hz⟩).2

lemma neckLift_gluing (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    gluingMap (neckLift z hz r) =
      neckLift (flipUpper z r) (flipUpper_band z hz r) (z.re-r) := by
  apply collarCoordinates.injective
  change collarCoordinates (collarCoordinates.symm
    ((collarFlip.prodCongr torusShear.symm) (collarCoordinates (neckLift z hz r)))) = _
  rw [Homeomorph.apply_symm_apply,neckLift_coordinates,neckLift_coordinates]
  apply Prod.ext
  · apply Subtype.ext
    exact (flipUpper_im z r).symm
  · change ((r : Circle),(z.re : Circle)-(r : Circle)) =
      (((flipUpper z r).re : Circle),((z.re-r : ℝ) : Circle))
    simp

lemma neckLift_chart (b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    chartAt (ℂ × ℝ) b (neckLift z hz r).1 = coverChart b ((z : ℂ),r) :=
  (coverChart_apply b z r _).symm

lemma neckLift_chart_source (b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ) :
    (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) b).source ↔
      projection z ∈ (chartAt ℂ b.1.1).source ∧ (r : Circle) ∈ (chartAt ℝ b.2).source := by
  change ((neckLift z hz r).1.1 ∈ (chartAt ℂ b.1).source ∧ _) ↔ _
  change ((⟨projection z, (neckLift z hz r).1.1.2⟩ : coreOpens 8) ∈
    ((chartAt ℂ b.1.1).subtypeRestr (⟨b.1⟩ : Nonempty (coreOpens 8))).source ∧ _) ↔ _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  rfl
end ThreeManifold.GluedConstruction

open Set Filter Topology
namespace ThreeManifold.Coordinates3

def coordinates : (ℂ × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  { toFun := fun p => ![p.1.re,p.1.im,p.2]
    invFun := fun v => ((v 0 : ℂ) + (v 1 : ℂ) * Complex.I,v 2)
    left_inv := by intro p; ext <;> simp
    right_inv := by intro v; funext i; fin_cases i <;> simp
    map_add' := by intro p q; funext i; fin_cases i <;> simp
    map_smul' := by intro r p; funext i; fin_cases i <;> simp }

def shearD (d : ℝ) : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
  { toFun := fun p => ((p.2 : ℂ) + (d * p.1.im : ℝ) * Complex.I, p.1.re - p.2)
    map_add' := by intro p q; ext <;> simp <;> ring
    map_smul' := by intro r p; ext <;> simp <;> ring }

lemma det_shearD (d : ℝ) : LinearMap.det (shearD d).toLinearMap = -d := by
  let L := coordinates.toLinearEquiv.toLinearMap ∘ₗ (shearD d).toLinearMap ∘ₗ
    coordinates.symm.toLinearEquiv.toLinearMap
  have hL : LinearMap.toMatrix (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) L =
      !![0,0,1;0,d,0;1,0,-1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L,coordinates,shearD]
  rw [← LinearMap.det_conj (shearD d).toLinearMap coordinates.toLinearEquiv]
  change LinearMap.det L = -d
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)),hL,Matrix.det_fin_three]
  simp

def liftedGluing (p : ℂ × ℝ) : ℂ × ℝ :=
  ((p.2 : ℂ) + (16 / p.1.im : ℝ) * Complex.I, p.1.re - p.2)

lemma liftedGluing_derivative {p : ℂ × ℝ} (hp : p.1.im ≠ 0) :
    HasFDerivAt liftedGluing (shearD (-(16 / p.1.im ^ 2))) p := by
  have hi := Complex.imCLM.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  have hr := Complex.reCLM.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  have hs := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt (x := p)
  have hd := (hasDerivAt_inv hp).comp_hasFDerivAt p hi |>.const_mul (16 : ℝ)
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp p hs).add
    ((Complex.ofRealCLM.hasFDerivAt.comp p hd).mul_const Complex.I)
  have h2 := hr.sub hs
  have h := h1.prodMk h2
  convert! h using 1
  ext x <;> simp [shearD,ContinuousLinearMap.comp_apply,div_eq_mul_inv]
  ring
end ThreeManifold.Coordinates3

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore Coordinates3 TwoGluing

lemma cover_transition_germ (a b : Piece) (z : ℍ) (hz : (2 : ℝ) < z.im ∧ z.im < 8) (r : ℝ)
    (ha : (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) a).source) :
    ((fun x => chartAt (ℂ × ℝ) b (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm x))) ∘
      coverChart a) =ᶠ[nhds ((z : ℂ),r)] (coverChart b ∘ liftedGluing) := by
  obtain ⟨ha1,ha2⟩ := (neckLift_chart_source a z hz r).mp ha
  have him : ContinuousAt (fun p : ℂ × ℝ => p.1.im) ((z : ℂ),r) :=
    (Complex.continuous_im.comp continuous_fst).continuousAt
  have hband : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r), (2 : ℝ) < p.1.im ∧ p.1.im < 8 :=
    him (isOpen_Ioo.mem_nhds hz)
  have hof : ContinuousAt UpperHalfPlane.ofComplex (z : ℂ) :=
    (upperHalfPlane_ofComplex_real_smoothAt (z := (z : ℂ)) z.im_pos).continuousAt
  have hofst : ContinuousAt (fun p : ℂ × ℝ => UpperHalfPlane.ofComplex p.1) ((z : ℂ),r) :=
    hof.comp (f := fun p : ℂ × ℝ => p.1) (continuousAt_fst (p := ((z : ℂ),r)))
  have hproj : ContinuousAt projection (UpperHalfPlane.ofComplex (z : ℂ)) :=
    projection_cover.continuous.continuousAt
  have h1 : ContinuousAt (fun p : ℂ × ℝ => projection (UpperHalfPlane.ofComplex p.1)) ((z : ℂ),r) :=
    hproj.comp (f := fun p : ℂ × ℝ => UpperHalfPlane.ofComplex p.1) hofst
  have h2 : ContinuousAt (fun p : ℂ × ℝ => (p.2 : Circle)) ((z : ℂ),r) :=
    (CircleConstruction.projection_cover 6).continuous.continuousAt.comp continuousAt_snd
  have hsource1 : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r),
      projection (UpperHalfPlane.ofComplex p.1) ∈ (chartAt ℂ a.1.1).source :=
    h1 ((chartAt ℂ a.1.1).open_source.mem_nhds (by simpa only [UpperHalfPlane.ofComplex_apply] using ha1))
  have hsource2 : ∀ᶠ p : ℂ × ℝ in nhds ((z : ℂ),r), (p.2 : Circle) ∈ (chartAt ℝ a.2).source :=
    h2 ((chartAt ℝ a.2).open_source.mem_nhds ha2)
  filter_upwards [hband,hsource1,hsource2] with p hp hpa hpb
  let w : ℍ := ⟨p.1,by linarith [hp.1]⟩
  have hw : UpperHalfPlane.ofComplex p.1 = w := UpperHalfPlane.ofComplex_apply_of_im_pos _
  have hws : (neckLift w hp p.2).1 ∈ (chartAt (ℂ × ℝ) a).source :=
    (neckLift_chart_source a w hp p.2).mpr ⟨hw ▸ hpa,hpb⟩
  change chartAt (ℂ × ℝ) b (extendedTransition collar gluingMap
    ((chartAt (ℂ × ℝ) a).symm (coverChart a ((w : ℂ),p.2)))) = _
  rw [← neckLift_chart a w hp p.2,(chartAt (ℂ × ℝ) a).left_inv hws,
    extendedTransition_apply collar gluingMap]
  calc
    _ = chartAt (ℂ × ℝ) b (neckLift (flipUpper w p.2) (flipUpper_band w hp p.2)
      (w.re-p.2)).1 := congrArg (fun t : collar => chartAt (ℂ × ℝ) b t.1)
        (neckLift_gluing w hp p.2)
    _ = _ := neckLift_chart b (flipUpper w p.2) (flipUpper_band w hp p.2) (w.re-p.2)

lemma gluing_transition_positive (a b : Piece) (x : ℂ × ℝ)
    (hx : x ∈ (chartAt (ℂ × ℝ) a).target)
    (hO : (chartAt (ℂ × ℝ) a).symm x ∈ collar)
    (hb : extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm x) ∈
      (chartAt (ℂ × ℝ) b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt (ℂ × ℝ) b
        (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm y))) x).toLinearMap := by
  obtain ⟨z,hz,r,he⟩ := neckLift_surjective ⟨(chartAt (ℂ × ℝ) a).symm x,hO⟩
  have hey : (neckLift z hz r).1 = (chartAt (ℂ × ℝ) a).symm x := congrArg Subtype.val he
  have ha : (neckLift z hz r).1 ∈ (chartAt (ℂ × ℝ) a).source := hey ▸ (chartAt (ℂ × ℝ) a).map_target hx
  have hax : coverChart a ((z : ℂ),r) = x := by
    rw [← neckLift_chart a z hz r,hey,(chartAt (ℂ × ℝ) a).right_inv hx]
  have hb' : (neckLift (flipUpper z r) (flipUpper_band z hz r) (z.re-r)).1 ∈
      (chartAt (ℂ × ℝ) b).source := by
    rw [← neckLift_gluing]
    rw [← hey,extendedTransition_apply collar gluingMap] at hb
    exact hb
  obtain ⟨ha1,ha2⟩ := (neckLift_chart_source a z hz r).mp ha
  obtain ⟨hb1,hb2⟩ := (neckLift_chart_source b (flipUpper z r) (flipUpper_band z hz r) (z.re-r)).mp hb'
  let T := fun y => chartAt (ℂ × ℝ) b
    (extendedTransition collar gluingMap ((chartAt (ℂ × ℝ) a).symm y))
  have hT : ContDiffAt ℝ ∞ T x := by
    have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ)) (n := ∞) a) hx
    have he' : ContMDiff 𝓘(ℝ,ℂ × ℝ) 𝓘(ℝ,ℂ × ℝ) ∞ gluingMap := by
      simpa only [modelWithCornersSelf_prod] using gluingMap_smooth
    have h2 := extendedTransition_smooth collar gluingMap he' ⟨_,hO⟩
    have h3 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ))
      (chart_mem_maximalAtlas (I := 𝓘(ℝ,ℂ × ℝ)) (n := ∞) b) hb
    exact ((h3.comp x (h2.comp x h1)).contDiffAt)
  have hca := (coverChart_smooth a z r ha1 ha2).differentiableAt (by simp)
  have hcb := (coverChart_smooth b (flipUpper z r) (z.re-r) hb1 hb2).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ T (coverChart a ((z : ℂ),r)) := by
    rw [hax]
    exact hT.differentiableAt (by simp)
  have hl := ht.hasFDerivAt.comp ((z : ℂ),r) hca.hasFDerivAt
  have hf := liftedGluing_derivative (p := ((z : ℂ),r)) (ne_of_gt z.im_pos)
  have hr := hcb.hasFDerivAt.comp ((z : ℂ),r) hf
  have hid := hl.unique (hr.congr_of_eventuallyEq (cover_transition_germ a b z hz r ha))
  rw [hax] at hid
  have hd := congrArg (fun L : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) => LinearMap.det L.toLinearMap) hid
  change LinearMap.det ((fderiv ℝ T x).toLinearMap ∘ₗ (fderiv ℝ (coverChart a) ((z : ℂ),r)).toLinearMap) =
      LinearMap.det ((fderiv ℝ (coverChart b) ((flipUpper z r : ℂ),z.re-r)).toLinearMap ∘ₗ
        (shearD (-(16 / z.im ^ 2))).toLinearMap) at hd
  rw [LinearMap.det_comp,LinearMap.det_comp,det_shearD,neg_neg] at hd
  have hp : 0 < 16 / z.im ^ 2 := by positivity
  exact pos_of_mul_pos_left (show 0 < LinearMap.det (fderiv ℝ T x).toLinearMap *
    LinearMap.det (fderiv ℝ (coverChart a) ((z : ℂ),r)).toLinearMap by
      rw [hd]
      exact mul_pos (coverChart_positive b (flipUpper z r) (z.re-r) hb1 hb2) hp)
    (coverChart_positive a z r ha1 ha2).le
end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart

section
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M]
variable (e : E ≃L[ℝ] F)

def chart (c : OpenPartialHomeomorph M E) : OpenPartialHomeomorph M F :=
  c.trans e.toHomeomorph.toOpenPartialHomeomorph

omit [ChartedSpace E M] in
lemma chart_source (c : OpenPartialHomeomorph M E) : (chart e c).source = c.source := by
  simp [chart]
omit [ChartedSpace E M] in
lemma chart_target (c : OpenPartialHomeomorph M E) : (chart e c).target = e '' c.target := by
  ext x
  change (x ∈ (univ : Set F) ∧ e.symm x ∈ c.target) ↔ x ∈ e '' c.target
  simp only [mem_univ, true_and]
  exact ⟨fun h => ⟨e.symm x,h,e.apply_symm_apply x⟩,
    fun ⟨y,hy,he⟩ => by rw [← he,e.symm_apply_apply]; exact hy⟩

@[instance_reducible]
def charts : ChartedSpace F M where
  atlas := chart e '' atlas E M
  chartAt x := chart e (chartAt E x)
  mem_chart_source x := by rw [chart_source]; exact mem_chart_source E x
  chart_mem_atlas x := ⟨chartAt E x,chart_mem_atlas E x,rfl⟩

variable [IsManifold 𝓘(ℝ,E) ∞ M]

lemma isManifold : let := charts (M := M) e; IsManifold 𝓘(ℝ,F) ∞ M := by
  let := charts (M := M) e
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c,hc,rfl⟩ ⟨d,hd,rfl⟩ x hx
  simp only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def,id_eq,preimage_id_eq,range_id,inter_univ] at hx ⊢
  have hcx : e.symm x ∈ c.target := by
    exact hx.1.2
  have hdx : c.symm (e.symm x) ∈ d.source := by
    exact hx.2.1
  have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (subset_maximalAtlas (n := ∞) hc) hcx
  have h2 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (subset_maximalAtlas (n := ∞) hd) hdx
  have ht := ((h2.comp _ h1).contDiffAt.comp x e.symm.contDiff.contDiffAt)
  change ContDiffWithinAt ℝ ∞ (fun x => e (d (c.symm (e.symm x)))) _ x
  exact (e.contDiff.contDiffAt.comp x ht).contDiffWithinAt

end

def realThree : (ℂ × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  (LinearEquiv.ofFinrankEq (R := ℝ) (ℂ × ℝ) (Fin 3 → ℝ) (by simp)).toContinuousLinearEquiv

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma positive (e : E ≃L[ℝ] F) (h : AtlasOrientation.Positive (E := E) (M := M)) :
    let := charts (M := M) e
    AtlasOrientation.Positive (E := F) (M := M) := by
  let := charts (M := M) e
  change AtlasOrientation.Positive (E := F) (M := M)
  rintro _ _ ⟨c,hc,rfl⟩ ⟨d,hd,rfl⟩ x hx hy
  have hcx : e.symm x ∈ c.target := hx.2
  have hdx : c.symm (e.symm x) ∈ d.source := hy.1
  have ht := (AtlasOrientation.transition_contDiffAt hc hd hcx hdx).differentiableAt (by simp)
  have hg := e.hasFDerivAt.comp x (ht.hasFDerivAt.comp x e.symm.hasFDerivAt)
  change 0 < LinearMap.det (fderiv ℝ (e ∘ (d ∘ c.symm) ∘ e.symm) x).toLinearMap
  rw [hg.fderiv]
  change 0 < LinearMap.det ((e.toLinearEquiv : E →ₗ[ℝ] F) ∘ₗ
    (fderiv ℝ (d ∘ c.symm) (e.symm x)).toLinearMap ∘ₗ (e.toLinearEquiv.symm : F →ₗ[ℝ] E))
  rw [LinearMap.det_conj]
  exact h c d hc hd (e.symm x) hcx hdx
end ThreeManifold.Rechart

open Set Filter Topology TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)
omit [IsManifold 𝓘(ℝ,E) ∞ X] in
lemma mixed_chart_positive
    (hpos : ∀ (a b : X) (x : E), x ∈ (chartAt E a).target →
      (chartAt E a).symm x ∈ O →
      extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (extendedTransition O e ((chartAt E a).symm y))) x).toLinearMap)
    (a b : X) {x : E} (hx : x ∈ (chartAt E a).target)
    (hy : (pieceChart (E := E) O e false a).symm x ∈ (pieceChart (E := E) O e true b).source) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => pieceChart (E := E) O e true b ((pieceChart (E := E) O e false a).symm y)) x).toLinearMap := by
  obtain ⟨y,hy,hey⟩ := hy
  obtain ⟨hxO,hxe⟩ := (inclusion_mixed_eq O e _ _).mp hey.symm
  have hb : extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source := by
    change extendedTransition O e ((chartAt E a).invFun x) ∈ (chartAt E b).source
    rw [extendedTransition_apply O e ⟨_,hxO⟩,hxe]
    exact hy
  rw [(pieceChart_mixed_germ O e a b hx hxO).fderiv_eq]
  exact hpos a b x hx hxO hb

lemma glued_positive (he : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e)
    (hei : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ e.symm)
    (hX : AtlasOrientation.Positive (E := E) (M := X))
    (hpos : ∀ (a b : X) (x : E), x ∈ (chartAt E a).target →
      (chartAt E a).symm x ∈ O →
      extendedTransition O e ((chartAt E a).symm x) ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (extendedTransition O e ((chartAt E a).symm y))) x).toLinearMap) :
    let := gluedCharts (E := E) O e
    AtlasOrientation.Positive (E := E) (M := Space O e) := by
  let := gluedCharts (E := E) O e
  let := glued_isManifold O e he hei
  change AtlasOrientation.Positive (E := E) (M := Space O e)
  rintro c d ⟨i,a,rfl⟩ ⟨j,b,rfl⟩ x hx hy
  have ha : x ∈ (chartAt E a).target := hx
  have same (k : Bool)
      (hk : (pieceChart (E := E) O e k a).symm x ∈ (pieceChart (E := E) O e k b).source) :
      0 < LinearMap.det (fderiv ℝ
        (pieceChart (E := E) O e k b ∘ (pieceChart (E := E) O e k a).symm) x).toLinearMap := by
    obtain ⟨y,hys,hye⟩ := hk
    have hey : y = (chartAt E a).symm x := (inclusion_openEmbedding O e k).injective hye
    have hb : (chartAt E a).symm x ∈ (chartAt E b).source := hey ▸ hys
    have hg : (pieceChart (E := E) O e k b ∘ (pieceChart (E := E) O e k a).symm) =
        (chartAt E b ∘ (chartAt E a).symm) := by
      funext y
      exact pieceChart_apply O e k b _
    rw [hg]
    exact hX _ _ (chart_mem_atlas E a) (chart_mem_atlas E b) x ha hb
  cases i <;> cases j
  · exact same false hy
  · exact mixed_chart_positive O e hpos a b ha hy
  · let c := pieceChart (E := E) O e true a
    let d := pieceChart (E := E) O e false b
    have hc : c ∈ atlas E (Space O e) := ⟨true,a,rfl⟩
    have hd : d ∈ atlas E (Space O e) := ⟨false,b,rfl⟩
    have hyt : d (c.symm x) ∈ d.target := d.map_source hy
    have hys : d.symm (d (c.symm x)) ∈ c.source := by
      rw [d.left_inv hy]
      exact c.map_target hx
    have hp := mixed_chart_positive O e hpos b a hyt hys
    have hh := AtlasOrientation.reverse_positive hd hc hyt hys hp
    rw [d.left_inv hy,c.right_inv hx] at hh
    exact hh
  · exact same true hy
end ThreeManifold.TwoGluing
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
lemma manifold_positive : AtlasOrientation.Positive (E := ℂ × ℝ) (M := Manifold) := by
  exact TwoGluing.glued_positive (E := ℂ × ℝ) collar gluingMap
    (by simpa only [modelWithCornersSelf_prod] using gluingMap_smooth)
    (by simpa only [modelWithCornersSelf_prod] using gluingMap_symm_smooth)
    piece_positive gluing_transition_positive

instance realCharts : ChartedSpace E3 Manifold := Rechart.charts Coordinates3.coordinates
instance realSmooth : IsManifold I3 ∞ Manifold :=
  Rechart.isManifold Coordinates3.coordinates

lemma manifold_oriented : OrientedAtlas (M := Manifold) :=
  Rechart.positive Coordinates3.coordinates manifold_positive

theorem closed_oriented_candidate :
    ∃ (M : Type) (top : TopologicalSpace M),
      letI := top
      ∃ (_ : T2Space M) (_ : SecondCountableTopology M) (_ : CompactSpace M)
        (_ : ConnectedSpace M) (charts : ChartedSpace E3 M),
        letI := charts
        ∃ (smooth : IsManifold I3 ∞ M),
          letI := smooth
          OrientedAtlas (M := M) := by
  exact ⟨Manifold,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    realCharts,realSmooth,manifold_oriented⟩
end ThreeManifold.GluedConstruction

end

end OAI
