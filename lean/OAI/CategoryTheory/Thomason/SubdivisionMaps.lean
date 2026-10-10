import Mathlib
import OAI.CategoryTheory.Thomason.HornRealization

namespace OAI

/-! Subdivision Maps. -/

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

lemma minimum_le_one {n : ℕ} (i : Fin (n+2)) (x : Simplex (n+1)) : minimum i x ≤ 1 := by
  obtain ⟨j, hj, he⟩ := minimum_attained i x
  rw [he]
  exact (Finset.single_le_sum (fun k _ => Convexity.StdSimplex.weights_nonneg k)
    (Finset.mem_univ j)).trans_eq (Convexity.StdSimplex.total_of_fintype x)

noncomputable def prismDenominator {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) : ℝ :=
  max (1 - minimum i q.2 / 2) |2 * (q.1 : ℝ) - 1|

lemma prismDenominator_pos {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    0 < prismDenominator i q := by
  have : (1:ℝ)/2 ≤ 1 - minimum i q.2 / 2 := by linarith [minimum_le_one i q.2]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (this.trans (le_max_left _ _))

lemma prismDenominator_le_one {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    prismDenominator i q ≤ 1 := by
  apply max_le
  · linarith [minimum_nonneg i q.2]
  · exact abs_le.mpr ⟨by linarith [q.1.property.1], by linarith [q.1.property.2]⟩

lemma continuous_prismDenominator {n : ℕ} (i : Fin (n+2)) : Continuous (prismDenominator i) :=
  (continuous_const.sub ((continuous_minimum i).comp continuous_snd |>.div_const 2)).max
    (((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const).abs

noncomputable def prismTime {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) : I :=
  ⟨1/2 + ((q.1 : ℝ)-1/2) / prismDenominator i q, by
    have hd := prismDenominator_pos i q
    have ha := abs_le.mp (le_max_right (1 - minimum i q.2 / 2) |2 * (q.1:ℝ) - 1|)
    change -prismDenominator i q ≤ _ ∧ _ ≤ prismDenominator i q at ha
    constructor
    · have : (-1/2 : ℝ) ≤ ((q.1:ℝ)-1/2) / prismDenominator i q :=
        (le_div_iff₀ hd).mpr (by linarith [ha.1])
      linarith
    · have : ((q.1:ℝ)-1/2) / prismDenominator i q ≤ (1/2 : ℝ) :=
        (div_le_iff₀ hd).mpr (by linarith [ha.2])
      linarith⟩

noncomputable def prismSpace {n : ℕ} (i : Fin (n+2)) :
    C(I × Simplex (n+1), Simplex (n+1)) := by
  classical
  let r (q : I × Simplex (n+1)) (j : Fin (n+2)) :=
    (if j = i then q.2.weights i + (2*(n+1:ℝ)-1)*(1-prismDenominator i q)
      else q.2.weights j - 2*(1-prismDenominator i q)) / prismDenominator i q
  refine ⟨fun q => ⟨Finsupp.equivFunOnFinite.symm (r q), ?_, ?_⟩, ?_⟩
  · intro j
    dsimp [r]
    apply div_nonneg _ (prismDenominator_pos i q).le
    split_ifs with he
    · exact add_nonneg (Convexity.StdSimplex.weights_nonneg _) (mul_nonneg (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
        (sub_nonneg.mpr (prismDenominator_le_one i q)))
    · have hmin := minimum_le i q.2 j he
      have hd : 1 - minimum i q.2/2 ≤ prismDenominator i q := le_max_left _ _
      linarith
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ j, r q j = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [r, Fin.succAbove_ne, ite_false, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← add_div]
    apply (div_eq_one_iff_eq (ne_of_gt (prismDenominator_pos i q))).mpr
    have hx := Convexity.StdSimplex.total_of_fintype q.2
    rw [Fin.sum_univ_succAbove _ i] at hx
    push_cast
    nlinarith
  · apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
    apply continuous_pi
    intro j
    dsimp [r]
    apply Continuous.div _ (continuous_prismDenominator i) (fun q => ne_of_gt (prismDenominator_pos i q))
    split_ifs
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd).add
        ((continuous_const.sub (continuous_prismDenominator i)).const_mul _)
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd).sub
        ((continuous_const.sub (continuous_prismDenominator i)).const_mul _)

lemma continuous_prismTime {n : ℕ} (i : Fin (n+2)) : Continuous (prismTime i) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp continuous_fst).sub continuous_const).div
    (continuous_prismDenominator i) (fun q => ne_of_gt (prismDenominator_pos i q)))

def prismRoof {n : ℕ} (i : Fin (n+2)) : Set (I × Simplex (n+1)) :=
  {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ horn i}

lemma prism_mem_roof {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    (prismTime i q, prismSpace i q) ∈ prismRoof i := by
  have hd := prismDenominator_pos i q
  rcases le_total |2*(q.1:ℝ)-1| (1-minimum i q.2/2) with h | h
  · right; right
    have he : prismDenominator i q = 1-minimum i q.2/2 := max_eq_left h
    obtain ⟨j, hj, hjx⟩ := minimum_attained i q.2
    refine ⟨j,hj,?_⟩
    change (if j = i then q.2.weights i + (2*(n+1:ℝ)-1)*(1-prismDenominator i q)
      else q.2.weights j - 2*(1-prismDenominator i q)) / prismDenominator i q = 0
    simp only [hj, ite_false, he]
    rw [← hjx]
    ring
  · have he : prismDenominator i q = |2*(q.1:ℝ)-1| := max_eq_right h
    rcases (abs_eq hd.le).mp he.symm with hq | hq
    · right; left
      apply Subtype.ext
      change 1/2 + ((q.1:ℝ)-1/2)/prismDenominator i q = 1
      have : ((q.1:ℝ)-1/2)/prismDenominator i q = (1/2 : ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]; norm_num
    · left
      apply Subtype.ext
      change 1/2 + ((q.1:ℝ)-1/2)/prismDenominator i q = 0
      have : ((q.1:ℝ)-1/2)/prismDenominator i q = (-1/2 : ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]; norm_num

noncomputable def prismRetract {n : ℕ} (i : Fin (n+2)) : C(I × Simplex (n+1), prismRoof i) :=
  ⟨fun q => ⟨(prismTime i q, prismSpace i q), prism_mem_roof i q⟩,
    ((continuous_prismTime i).prodMk (prismSpace i).continuous).subtype_mk _⟩

lemma prismRetract_fixed {n : ℕ} (i : Fin (n+2)) (q : prismRoof i) :
    (prismRetract i q).val = q.val := by
  have he : prismDenominator i q = 1 := by
    apply le_antisymm (prismDenominator_le_one i q)
    rcases q.property with h | h | h
    · have : |2 * (q.val.1 : ℝ) - 1| = 1 := by rw [h]; norm_num
      exact this ▸ le_max_right _ _
    · have : |2 * (q.val.1 : ℝ) - 1| = 1 := by rw [h]; norm_num
      exact this ▸ le_max_right _ _
    · have : 1 - minimum i q.val.2 / 2 = 1 := by rw [minimum_eq_zero i _ h]; norm_num
      exact this ▸ le_max_left _ _
  apply Prod.ext
  · apply Subtype.ext
    change 1/2 + ((q.val.1:ℝ)-1/2)/prismDenominator i q = (q.val.1:ℝ)
    rw [he, div_one]; ring
  · ext j
    change (if j = i then _ else _) / prismDenominator i q = q.val.2.weights j
    rw [he]
    split_ifs with hj
    · rw [hj]; ring
    · ring

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

lemma isClosed_horn {n : ℕ} (i : Fin (n+2)) : IsClosed (horn i) := by
  have he : horn i = {x | minimum i x = 0} := by
    ext x
    constructor
    · exact minimum_eq_zero i x
    · intro hx
      obtain ⟨j,hj,hmin⟩ := minimum_attained i x
      exact ⟨j,hj,hmin.symm.trans hx⟩
  rw [he]
  exact isClosed_eq (continuous_minimum i) continuous_const

def roofPiece {n : ℕ} (i : Fin (n+2)) : Option Bool → Set (prismRoof i)
  | none => {q | q.val.2 ∈ horn i}
  | some b => {q | q.val.1 = if b then 1 else 0}

lemma isClosed_roofPiece {n : ℕ} (i : Fin (n+2)) (b : Option Bool) :
    IsClosed (roofPiece i b) := by
  cases b with
  | none => exact (isClosed_horn i).preimage (continuous_snd.comp continuous_subtype_val)
  | some b => exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const

lemma roofPiece_cover {n : ℕ} (i : Fin (n+2)) (q : prismRoof i) : ∃ b, q ∈ roofPiece i b := by
  rcases q.property with h | h | h
  · exact ⟨some false,h⟩
  · exact ⟨some true,h⟩
  · exact ⟨none,h⟩

variable {X : Type u} [TopologicalSpace X] {n : ℕ} {i : Fin (n+2)}

noncomputable def roofPieceValue (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X)) :
    ∀ k, C(roofPiece i k,X)
  | none => H.comp ⟨fun q => (q.val.val.1,⟨q.val.val.2,q.property⟩),
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)⟩
  | some k => (if k then b else a).comp
      ⟨fun q => q.val.val.2, continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

lemma roofPieceValue_agree (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x)
    (j k : Option Bool) (q : prismRoof i) (hj : q ∈ roofPiece i j) (hk : q ∈ roofPiece i k) :
    roofPieceValue a b H j ⟨q,hj⟩ = roofPieceValue a b H k ⟨q,hk⟩ := by
  cases j with
  | none =>
    cases k with
    | none => rfl
    | some k =>
      cases k
      · change H (q.val.1,⟨q.val.2,hj⟩) = a q.val.2
        rw [show q.val.1 = 0 from hk]
        exact ha _
      · change H (q.val.1,⟨q.val.2,hj⟩) = b q.val.2
        rw [show q.val.1 = 1 from hk]
        exact hb _
  | some j =>
    cases k with
    | none =>
      cases j
      · change a q.val.2 = H (q.val.1,⟨q.val.2,hk⟩)
        rw [show q.val.1 = 0 from hj]
        exact (ha ⟨q.val.2,hk⟩).symm
      · change b q.val.2 = H (q.val.1,⟨q.val.2,hk⟩)
        rw [show q.val.1 = 1 from hj]
        exact (hb ⟨q.val.2,hk⟩).symm
    | some k =>
      cases j <;> cases k
      · rfl
      · exact (zero_ne_one (hj.symm.trans hk)).elim
      · exact (zero_ne_one (hk.symm.trans hj)).elim
      · rfl

noncomputable def roofValue (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) : C(prismRoof i,X) :=
  closedCoverPaste (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb)

noncomputable def prismExtend (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) : C(I × Simplex (n+1),X) :=
  (roofValue a b H ha hb).comp (prismRetract i)

lemma prismExtend_onRoof (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (q : prismRoof i) :
    prismExtend a b H ha hb q = roofValue a b H ha hb q :=
  congrArg (roofValue a b H ha hb) (Subtype.ext (prismRetract_fixed i q))

lemma prismExtend_zero (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (x : Simplex (n+1)) :
    prismExtend a b H ha hb (0,x) = a x := by
  rw [prismExtend_onRoof a b H ha hb ⟨(0,x),Or.inl rfl⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) (some false) _ rfl

lemma prismExtend_one (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (x : Simplex (n+1)) :
    prismExtend a b H ha hb (1,x) = b x := by
  rw [prismExtend_onRoof a b H ha hb ⟨(1,x),Or.inr (Or.inl rfl)⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) (some true) _ rfl

lemma prismExtend_side (a b : C(Simplex (n+1),X)) (H : C(I × horn i,X))
    (ha : ∀ x : horn i, H (0,x) = a x) (hb : ∀ x : horn i, H (1,x) = b x) (t : I) (x : horn i) :
    prismExtend a b H ha hb (t,x) = H (t,x) := by
  rw [prismExtend_onRoof a b H ha hb ⟨(t,x),Or.inr (Or.inr x.property)⟩]
  exact closedCoverPaste_apply (roofPiece i) (isClosed_roofPiece i) (roofPiece_cover i)
    (roofPieceValue a b H) (roofPieceValue_agree a b H ha hb) none _ x.property

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial
open scoped Topology unitInterval

lemma singularValue_post {X Y : TopCat.{u}} {n : ℕ}
    (f : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj X) (p : X ⟶ Y)
    (x : Simplex n) : singularValue (f ≫ TopCat.toSSet.map p) x = p (singularValue f x) := rfl

lemma hornValue_square {X Y : TopCat.{u}} {n : ℕ} {i : Fin (n+2)}
    (g : (SSet.horn (n+1) i : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (f : (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj Y) (p : X ⟶ Y)
    (h : g ≫ TopCat.toSSet.map p = (SSet.horn (n+1) i).ι ≫ f) (x : horn i) :
    p (hornValue (fun j hj => SSet.horn.ι i j hj ≫ g) (SSet.horn.IsCompatible.of_hom g) x) =
      singularValue f x := by
  obtain ⟨j,hj,hx⟩ := x.property
  let y := drop j ⟨x.val,hx⟩
  have he : (⟨Convexity.StdSimplex.map j.succAbove y,j,hj,map_succAbove_pivot j y⟩ : horn i) = x :=
    Subtype.ext (map_drop j x hx)
  rw [← he, hornValue_face]
  have hh : (SSet.horn.ι i j hj ≫ g) ≫ TopCat.toSSet.map p = SSet.stdSimplex.δ j ≫ f := by
    rw [Category.assoc, h, SSet.horn.ι_ι_assoc]
  simpa only [singularValue_post, singularValue_delta] using congrArg (fun φ => singularValue φ y) hh

abbrev PathSpace (X : TopCat.{u}) : TopCat.{u} := TopCat.of C(I,X)
abbrev EndpointSpace (X : TopCat.{u}) : TopCat.{u} := TopCat.of (X × X)

noncomputable def pathEndpoints (X : TopCat.{u}) : PathSpace X ⟶ EndpointSpace X :=
  TopCat.ofHom ⟨fun γ => (γ 0,γ 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

theorem singular_path_fibration (T : TopCat.{u}) :
    SSet.modelCategoryQuillen.J.rlp (TopCat.toSSet.map (pathEndpoints T)) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n,⟨k⟩⟩ := hi
  constructor
  intro g f sq
  let F := fun j hj => SSet.horn.ι k j hj ≫ g
  have hF : SSet.horn.IsCompatible F := SSet.horn.IsCompatible.of_hom g
  let H : C(I × horn k,T) := (hornValue F hF).uncurry.comp ⟨Prod.swap,continuous_swap⟩
  let a : C(Simplex (n+1),T) := ContinuousMap.fst.comp (singularValue f)
  let b : C(Simplex (n+1),T) := ContinuousMap.snd.comp (singularValue f)
  have ha (x : horn k) : H (0,x) = a x :=
    congrArg Prod.fst (hornValue_square g f (pathEndpoints T) sq.w x)
  have hb (x : horn k) : H (1,x) = b x :=
    congrArg Prod.snd (hornValue_square g f (pathEndpoints T) sq.w x)
  let h : C(Simplex (n+1),C(I,T)) :=
    ((prismExtend a b H ha hb).comp ⟨Prod.swap,continuous_swap⟩).curry
  let φ := SSet.yonedaEquiv.symm (((PathSpace T).toSSetObjEquiv _).symm h)
  have hφ : singularValue φ = h := by simp only [singularValue, φ, Equiv.apply_symm_apply]
  refine ⟨⟨{ l := φ, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply SSet.horn.hom_ext'
    intro j hj
    rw [SSet.horn.ι_ι_assoc]
    apply SSet.yonedaEquiv.injective
    apply ((PathSpace T).toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    change singularValue (SSet.stdSimplex.δ j ≫ φ) x t = singularValue (F j hj) x t
    rw [singularValue_delta, hφ]
    change prismExtend a b H ha hb (t,Convexity.StdSimplex.map j.succAbove x) = _
    rw [prismExtend_side a b H ha hb t
      ⟨Convexity.StdSimplex.map j.succAbove x,j,hj,map_succAbove_pivot j x⟩]
    change hornValue F hF ⟨Convexity.StdSimplex.map j.succAbove x,j,hj,map_succAbove_pivot j x⟩ t = _
    rw [hornValue_face]
  · apply SSet.yonedaEquiv.injective
    apply ((EndpointSpace T).toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro x
    change singularValue (φ ≫ TopCat.toSSet.map (pathEndpoints T)) x = singularValue f x
    rw [singularValue_post,hφ]
    apply Prod.ext
    · exact prismExtend_zero a b H ha hb x
    · exact prismExtend_one a b H ha hb x

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Topology unitInterval

lemma anodyne_top_extension {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
    (Z : TopCat.{u}) (f : SSet.toTop.obj A ⟶ Z) :
    ∃ g : SSet.toTop.obj B ⟶ Z, SSet.toTop.map i ≫ g = f := by
  let : SSet.KanComplex (TopCat.toSSet.obj Z) := singular_kan Z
  have hp : SSet.modelCategoryQuillen.J.rlp (terminal.from (TopCat.toSSet.obj Z)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  let : HasLiftingProperty i (terminal.from (TopCat.toSSet.obj Z)) := hi _ hp
  have sq : CommSq ((sSetTopAdj.homEquiv _ _) f) i
      (terminal.from (TopCat.toSSet.obj Z)) (terminal.from B) := ⟨Subsingleton.elim _ _⟩
  refine ⟨(sSetTopAdj.homEquiv _ _).symm sq.lift, ?_⟩
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact sq.fac_left

theorem anodyne_weak_equivalence {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    simplicialWeakEquivalences i := by
  let j := SSet.toTop.map i
  obtain ⟨r,hr⟩ := anodyne_top_extension i hi (SSet.toTop.obj A) (𝟙 _)
  have hre (a : SSet.toTop.obj A) : r (j a) = a := ConcreteCategory.congr_hom hr a
  let f : SSet.toTop.obj A ⟶ PathSpace (SSet.toTop.obj B) :=
    TopCat.ofHom (ContinuousMap.const'.comp j.hom)
  let g : SSet.toTop.obj B ⟶ EndpointSpace (SSet.toTop.obj B) :=
    TopCat.ofHom ⟨fun b => (j (r b),b), (j.hom.continuous.comp r.hom.continuous).prodMk continuous_id⟩
  have sq : CommSq f j (pathEndpoints (SSet.toTop.obj B)) g := by
    constructor
    apply ConcreteCategory.hom_ext
    intro a
    change (j a,j a) = (j (r (j a)),j a)
    rw [hre]
  let : HasLiftingProperty j (pathEndpoints (SSet.toTop.obj B)) :=
    (sSetTopAdj.hasLiftingProperty_iff i _).mpr (hi _ (singular_path_fibration _))
  have hzero (b : SSet.toTop.obj B) : sq.lift b 0 = j (r b) :=
    congrArg Prod.fst (ConcreteCategory.congr_hom sq.fac_right b)
  have hone (b : SSet.toTop.obj B) : sq.lift b 1 = b :=
    congrArg Prod.snd (ConcreteCategory.congr_hom sq.fac_right b)
  have hfixed (a : SSet.toTop.obj A) (t : I) : sq.lift (j a) t = j a :=
    congrArg (fun γ : C(I,SSet.toTop.obj B) => γ t) (ConcreteCategory.congr_hom sq.fac_left a)
  apply WeakHomotopy.equivalence_of_strong_retract j.hom r.hom
    (congrArg TopCat.Hom.hom hr)
  refine ⟨{ toHomotopy :=
    { toFun := fun q => sq.lift q.2 q.1
      continuous_toFun := ?_
      map_zero_left := hzero
      map_one_left := hone }
            prop' := ?_ }⟩
  · exact continuous_eval.comp ((sq.lift.hom.continuous.comp continuous_snd).prodMk continuous_fst)
  · rintro t b ⟨a,rfl⟩
    change sq.lift (j a) t = j (r (j a))
    rw [hre]
    exact hfixed a t

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

noncomputable def hornOneIso (i j : Fin 2) (h : j ≠ i) :
    (Δ[0] : SSet.{u}) ≅ SSet.horn 1 i where
  hom := SSet.horn.ι i j h
  inv := SSet.stdSimplex.isTerminalObj₀.from _
  hom_inv_id := SSet.stdSimplex.ext₀
  inv_hom_id := by
    apply SSet.horn.hom_ext'
    intro k hk
    have he : k = j := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    subst k
    rw [← Category.assoc, SSet.stdSimplex.ext₀ (f := SSet.horn.ι i j h ≫
      SSet.stdSimplex.isTerminalObj₀.from _) (g := 𝟙 _)]
    simp

lemma delta_one_anodyne (j : Fin 2) :
    SSet.anodyneExtensions.{u} (SSet.stdSimplex.δ (n := 0) j) := by
  let i : Fin 2 := j.rev
  have h : j ≠ i := by fin_cases j <;> decide
  have hh := SSet.anodyneExtensions.comp_mem (hornOneIso i j h).hom (SSet.horn 1 i).ι
    (SSet.anodyneExtensions.of_isIso _) (SSet.anodyneExtensions.horn_ι i)
  simpa only [hornOneIso, SSet.horn.ι_ι] using hh

noncomputable def zeroFactorIso (X : SSet.{u}) : X ≅ X ⊗ Δ[0] where
  hom := lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _)
  inv := fst _ _
  hom_inv_id := by simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact SSet.stdSimplex.ext₀

lemma endpoint_anodyne (X : SSet.{u}) :
    SSet.anodyneExtensions (SSet.ι₀ (X := X)) ∧
    SSet.anodyneExtensions (SSet.ι₁ (X := X)) := by
  have h (j : Fin 2) := SSet.anodyneExtensions.comp_mem (zeroFactorIso X).hom
    (X ◁ SSet.stdSimplex.δ (n := 0) j) (SSet.anodyneExtensions.of_isIso _)
    ((delta_one_anodyne j).whiskerLeft X)
  have h0 : (zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 1 = SSet.ι₀ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro z
      rfl
  have h1 : (zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 0 = SSet.ι₁ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro z
      rfl
  exact ⟨h0 ▸ h 1,h1 ▸ h 0⟩

lemma endpoint_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (SSet.ι₀ (X := X)) ∧
    simplicialWeakEquivalences (SSet.ι₁ (X := X)) :=
  ⟨TopologicalHorn.anodyne_weak_equivalence _ (endpoint_anodyne X).1,
   TopologicalHorn.anodyne_weak_equivalence _ (endpoint_anodyne X).2⟩

end Thomason.SimplicialCylinder

end

noncomputable section
universe u v w z


namespace Thomason.SimplicialCylinder

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

def Ends (X : SSet.{u}) : SSet.{u} where
  obj k := X.obj k ⊕ X.obj k
  map f := ↾(Sum.map (X.map f) (X.map f))
  map_id k := by ext x; cases x <;> simp
  map_comp f g := by ext x; cases x <;> simp

def endsMap {X Y : SSet.{u}} (f g : X ⟶ Y) : Ends X ⟶ Y where
  app k := ↾(Sum.elim (f.app k) (g.app k))
  naturality k l a := by
    ext x
    cases x with
    | inl x => exact NatTrans.naturality_apply f a x
    | inr x => exact NatTrans.naturality_apply g a x

noncomputable def endsInclusion (X : SSet.{u}) : Ends X ⟶ X ⊗ Δ[1] :=
  endsMap SSet.ι₀ SSet.ι₁

instance endsInclusion_mono (X : SSet.{u}) : Mono (endsInclusion X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (congrArg Prod.fst hab)
    | inr b =>
      have h := congrArg (fun z : (X ⊗ Δ[1]).obj k => SSet.stdSimplex.asOrderHom z.2 0) hab
      exact (zero_ne_one h).elim
  | inr a =>
    cases b with
    | inl b =>
      have h := congrArg (fun z : (X ⊗ Δ[1]).obj k => SSet.stdSimplex.asOrderHom z.2 0) hab
      exact (one_ne_zero h).elim
    | inr b => exact congrArg Sum.inr (congrArg Prod.fst hab)

theorem boundary_rlp_weak {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.I.rlp p) : simplicialWeakEquivalences p := by
  have hall : (MorphismProperty.monomorphisms SSet).rlp p := by
    rwa [SSet.rlp_monomorphisms]
  let : HasLiftingProperty (initial.to B) p := hall _ inferInstance
  have sqs : CommSq (initial.to E) (initial.to B) p (𝟙 B) := ⟨Subsingleton.elim _ _⟩
  let s := sqs.lift
  have hs : s ≫ p = 𝟙 B := sqs.fac_right
  let : HasLiftingProperty (endsInclusion E) p := hall _ inferInstance
  have sq : CommSq (endsMap (p ≫ s) (𝟙 E)) (endsInclusion E) p (fst _ _ ≫ p) := by
    constructor
    ext k x
    cases x with
    | inl x =>
      change p.app k (s.app k (p.app k x)) = p.app k x
      exact congrArg (fun f : B ⟶ B => f.app k (p.app k x)) hs
    | inr x => rfl
  have h0 : SSet.ι₀ ≫ sq.lift = p ≫ s := by
    ext k x
    exact congrArg (fun f : Ends E ⟶ E => f.app k (Sum.inl x)) sq.fac_left
  have h1 : SSet.ι₁ ≫ sq.lift = 𝟙 E := by
    ext k x
    exact congrArg (fun f : Ends E ⟶ E => f.app k (Sum.inr x)) sq.fac_left
  have hl : simplicialWeakEquivalences sq.lift :=
    simplicialWeakEquivalences.of_precomp SSet.ι₁ sq.lift (endpoint_weak E).2
      (h1.symm ▸ simplicialWeakEquivalences.id_mem E)
  have hps : simplicialWeakEquivalences (p ≫ s) := h0 ▸
    simplicialWeakEquivalences.comp_mem _ _ (endpoint_weak E).1 hl
  have hr : RetractArrow p (p ≫ s) :=
    { i := Arrow.homMk (𝟙 E) s (by change 𝟙 E ≫ (p ≫ s) = p ≫ s; simp)
      r := Arrow.homMk (𝟙 E) p (by change 𝟙 E ≫ p = (p ≫ s) ≫ p; simp [Category.assoc,hs])
      retract := by ext <;> simp [hs] }
  exact simplicialWeakEquivalences.of_retract hr hps

end Thomason.SimplicialCylinder

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open SSet.modelCategoryQuillen

instance boundary_small : IsSmall.{u} I.{u} := by
  change IsSmall (ofHoms fun n => (SSet.boundary n).ι)
  exact isSmall_ofHoms _

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance boundary_smallCardinal : IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance boundary_smallObject : HasSmallObjectArgument.{u} I.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma boundary_left_class : I.{u}.rlp.llp = monomorphisms SSet := by
  apply le_antisymm
  · rw [llp_rlp_of_hasSmallObjectArgument]
    rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · rw [← SSet.rlp_monomorphisms]
    exact le_llp_rlp _

lemma anodyne_monomorphism : SSet.anodyneExtensions.{u} ≤ monomorphisms SSet := by
  rw [SSet.anodyneExtensions_eq_retracts_transfiniteCompositions]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  exact J_le_monomorphisms

lemma boundary_right_fibrations : I.{u}.rlp ≤ simplicialFibrations := by
  rw [← SSet.rlp_monomorphisms]
  exact antitone_rlp J_le_monomorphisms

lemma boundary_right_weak : I.{u}.rlp ≤ simplicialWeakEquivalences :=
  fun _ _ p hp => SimplicialCylinder.boundary_rlp_weak p hp

lemma anodyne_weak : SSet.anodyneExtensions.{u} ≤ simplicialWeakEquivalences :=
  fun _ _ i hi => TopologicalHorn.anodyne_weak_equivalence i hi

theorem boundary_weakFactorization :
    IsWeakFactorizationSystem (monomorphisms SSet.{u}) I.rlp := by
  rw [← boundary_left_class]
  exact { rlp := rlp_llp_rlp I.{u}, llp := rfl }

theorem horn_weakFactorization :
    IsWeakFactorizationSystem SSet.anodyneExtensions.{u} simplicialFibrations := by
  change IsWeakFactorizationSystem J.{u}.rlp.llp J.{u}.rlp
  exact { rlp := rlp_llp_rlp J.{u}, llp := rfl }

noncomputable def factorization_cof_weakFib {X Y : SSet.{u}} (f : X ⟶ Y) :
    MapFactorizationData (monomorphisms SSet) (simplicialFibrations ⊓ simplicialWeakEquivalences) f := by
  let d := factorizationData I.{u}.rlp.llp I.{u}.rlp f
  exact {
    Z := d.Z
    i := d.i
    p := d.p
    fac := d.fac
    hi := boundary_left_class ▸ d.hi
    hp := ⟨boundary_right_fibrations _ d.hp, boundary_right_weak _ d.hp⟩ }

noncomputable def factorization_weakCof_fib {X Y : SSet.{u}} (f : X ⟶ Y) :
    MapFactorizationData ((monomorphisms SSet) ⊓ simplicialWeakEquivalences) simplicialFibrations f := by
  let d := factorizationData J.{u}.rlp.llp J.{u}.rlp f
  exact {
    Z := d.Z
    i := d.i
    p := d.p
    fac := d.fac
    hi := ⟨anodyne_monomorphism _ d.hi, anodyne_weak _ d.hi⟩
    hp := d.hp }

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory PartialOrder

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

lemma chain_has_greatest (s : NonemptyFiniteChains X) :
    ∃ x, x ∈ s.finset ∧ ∀ y ∈ s.finset, y ≤ x := by
  obtain ⟨x, hx, hm⟩ := s.finset.exists_maximal s.nonempty
  refine ⟨x, hx, fun y hy => ?_⟩
  rcases s.comparable ⟨x, hx⟩ ⟨y, hy⟩ with h | h
  · exact hm hy h
  · exact h

noncomputable def chainGreatest (s : NonemptyFiniteChains X) : X :=
  (chain_has_greatest s).choose

lemma chainGreatest_mem (s : NonemptyFiniteChains X) : chainGreatest s ∈ s.finset :=
  (chain_has_greatest s).choose_spec.1

lemma le_chainGreatest (s : NonemptyFiniteChains X) {x : X} (hx : x ∈ s.finset) :
    x ≤ chainGreatest s := (chain_has_greatest s).choose_spec.2 x hx

noncomputable def chainLast : NonemptyFiniteChains X →o X where
  toFun := chainGreatest
  monotone' s t h := le_chainGreatest t (h (chainGreatest_mem s))

lemma chainGreatest_map (s : NonemptyFiniteChains X) (f : X →o Y) :
    chainGreatest (s.map f) = f (chainGreatest s) := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := (NonemptyFiniteChains.mem_map_iff s f _).mp
      (chainGreatest_mem (s.map f))
    rw [← he]
    exact f.monotone (le_chainGreatest s hx)
  · exact le_chainGreatest (s.map f)
      ((NonemptyFiniteChains.mem_map_iff s f _).mpr ⟨_, chainGreatest_mem s, rfl⟩)

noncomputable def chainLastNat : PartOrd.nonemptyFiniteChainsFunctor.{u} ⟶ 𝟭 PartOrd where
  app X := PartOrd.ofHom chainLast
  naturality X Y f := by
    apply PartOrd.hom_ext
    apply OrderHom.ext
    funext s
    exact chainGreatest_map s f.hom

def OldChains (A : Set X) : Type u := {s : NonemptyFiniteChains X // ∀ x ∈ s.finset, x ∈ A}

def MeetingChains (A : Set X) : Type u := {s : NonemptyFiniteChains X // ∃ x ∈ s.finset, x ∈ A}

instance (A : Set X) : PartialOrder (OldChains A) := inferInstanceAs (PartialOrder (Subtype _))
instance (A : Set X) : PartialOrder (MeetingChains A) := inferInstanceAs (PartialOrder (Subtype _))

def chainInclusion (A : Set X) : OldChains A →o MeetingChains A where
  toFun s := ⟨s.val, by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩⟩
  monotone' _ _ h := h

noncomputable def chainIntersection (A : Set X) : MeetingChains A →o OldChains A := by
  classical
  let raw (s : MeetingChains A) : NonemptyFiniteChains X := {
    finset := s.val.finset.filter (· ∈ A)
    nonempty := by
      obtain ⟨x, hx, ha⟩ := s.property
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, ha⟩⟩
    comparable := fun a b => s.val.comparable
      ⟨a.val, (Finset.mem_filter.mp a.property).1⟩
      ⟨b.val, (Finset.mem_filter.mp b.property).1⟩ }
  refine {
    toFun := fun s => ⟨raw s, ?_⟩
    monotone' := ?_ }
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro s t h x hx
    obtain ⟨hx, ha⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h hx, ha⟩

lemma chainIntersection_adjunction (A : Set X) :
    GaloisConnection (chainInclusion A) (chainIntersection A) := by
  classical
  intro s t
  constructor
  · intro h x hx
    exact Finset.mem_filter.mpr ⟨h hx, s.property x hx⟩
  · intro h x hx
    exact (Finset.mem_filter.mp (h hx)).1

lemma chainIntersection_retraction (A : Set X) (s : OldChains A) :
    chainIntersection A (chainInclusion A s) = s := by
  classical
  apply Subtype.ext
  apply NonemptyFiniteChains.ext
  exact Finset.filter_eq_self.mpr s.property

lemma oldChains_sieve (A : Set X) {s t : NonemptyFiniteChains X}
    (h : s ≤ t) (ht : ∀ x ∈ t.finset, x ∈ A) : ∀ x ∈ s.finset, x ∈ A :=
  fun x hx => ht x (h hx)

lemma meetingChains_cosieve (A : Set X) {s t : NonemptyFiniteChains X}
    (h : s ≤ t) (hs : ∃ x ∈ s.finset, x ∈ A) : ∃ x ∈ t.finset, x ∈ A := by
  obtain ⟨x, hx, ha⟩ := hs
  exact ⟨x, h hx, ha⟩

lemma meetingChains_upward (A : Set X) (s : NonemptyFiniteChains X) :
    (∃ x ∈ s.finset, x ∈ A) ↔ ∃ t : OldChains A, t.val ≤ s := by
  classical
  constructor
  · rintro ⟨x, hx, ha⟩
    refine ⟨⟨{ finset := {x}, comparable := ?_ }, ?_⟩, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Finset.mem_singleton] at ha hb
      subst a; subst b
      exact Or.inl le_rfl
    · intro y hy
      have hy' : y = x := Finset.mem_singleton.mp hy
      exact hy' ▸ ha
    · exact Finset.singleton_subset_iff.mpr hx
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := t.val.nonempty
    exact ⟨x, ht hx, t.property x hx⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

noncomputable def simplexNerveIso : SSet.stdSimplex.{u} ≅
    SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n => SSet.stdSimplex.isoNerve n.len) (by
    intro n m f
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    apply ComposableArrows.ext (fun _ => rfl)
    intros
    apply Subsingleton.elim)

noncomputable def simplexLastVertex : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex :=
  Functor.whiskerLeft SimplexCategory.toPartOrd (Functor.whiskerRight chainLastNat PartOrd.nerveFunctor) ≫
    simplexNerveIso.inv

noncomputable def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 SSet) simplexLastVertex

lemma lastVertex_stdSimplex (n : SimplexCategory) :
    lastVertex.app (SSet.stdSimplex.obj n) =
      (SSet.stdSimplex.sdIso.app n).hom ≫ simplexLastVertex.app n := by
  apply (cancel_epi (SSet.stdSimplex.sdIso.app n).inv).mp
  simpa only [lastVertex, Iso.app_inv, Iso.app_hom, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using
    SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv
      (𝟭 SSet) simplexLastVertex n

noncomputable def exComparison : 𝟭 SSet.{u} ⟶ SSet.ex where
  app X := SSet.sdExAdjunction.homEquiv X X (lastVertex.app X)
  naturality X Y f := by
    change f ≫ SSet.sdExAdjunction.homEquiv Y Y (lastVertex.app Y) =
      SSet.sdExAdjunction.homEquiv X X (lastVertex.app X) ≫ SSet.ex.map f
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← SSet.sdExAdjunction.homEquiv_naturality_right]
    exact congrArg (SSet.sdExAdjunction.homEquiv X Y) (lastVertex.naturality f)

lemma exComparison_mate (X : SSet.{u}) :
    (SSet.sdExAdjunction.homEquiv X X).symm (exComparison.app X) = lastVertex.app X :=
  (SSet.sdExAdjunction.homEquiv X X).symm_apply_apply _

end Thomason.Subdivision

end

end OAI
