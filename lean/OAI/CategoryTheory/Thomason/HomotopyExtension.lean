import Mathlib
import OAI.CategoryTheory.Thomason.SieveAttachments

namespace OAI

/-! Homotopy Extension. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.TopologicalCylinder
open scoped Topology unitInterval
open CategoryTheory
open Thomason.TopologicalHorn

noncomputable def minimum (n : ℕ) (x : Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n+1) => x.weights k)

lemma minimum_nonneg (n : ℕ) (x : Simplex n) : 0 ≤ minimum n x :=
  Finset.le_inf' _ _ (fun _ _ => Convexity.StdSimplex.weights_nonneg _)

lemma minimum_le (n : ℕ) (x : Simplex n) (j : Fin (n+1)) : minimum n x ≤ x.weights j :=
  Finset.inf'_le _ (Finset.mem_univ j)

lemma minimum_attained (n : ℕ) (x : Simplex n) : ∃ j, minimum n x = x.weights j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun k : Fin (n+1) => x.weights k)
  exact ⟨j,hj⟩

lemma continuous_minimum (n : ℕ) : Continuous (minimum n) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun k _ => Convexity.StdSimplex.continuous_weights_apply ℝ k)

noncomputable def denominator {n : ℕ} (q : I × Simplex n) : ℝ :=
  max (1 - (q.1 : ℝ)/2) (1 - (n+1 : ℝ) * minimum n q.2)

lemma denominator_pos {n : ℕ} (q : I × Simplex n) : 0 < denominator q := by
  have : (1:ℝ)/2 ≤ 1 - (q.1:ℝ)/2 := by linarith [q.1.property.2]
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (this.trans (le_max_left _ _))

lemma denominator_le_one {n : ℕ} (q : I × Simplex n) : denominator q ≤ 1 := by
  apply max_le
  · linarith [q.1.property.1]
  · have := mul_nonneg (show 0 ≤ (n+1:ℝ) by positivity) (minimum_nonneg n q.2)
    linarith

lemma continuous_denominator (n : ℕ) : Continuous (@denominator n) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_const.sub (((continuous_minimum n).comp continuous_snd).const_mul _))

noncomputable def time {n : ℕ} (q : I × Simplex n) : I :=
  ⟨2 - (2 - (q.1:ℝ))/denominator q, by
    have hd := denominator_pos q
    have ha : 1 - (q.1:ℝ)/2 ≤ denominator q := le_max_left _ _
    constructor
    · have : (2 - (q.1:ℝ))/denominator q ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
      linarith
    · have : 1 ≤ (2 - (q.1:ℝ))/denominator q := (le_div_iff₀ hd).mpr (by
        linarith [denominator_le_one q, q.1.property.2])
      linarith⟩

lemma continuous_time (n : ℕ) : Continuous (@time n) := by
  apply Continuous.subtype_mk
  exact continuous_const.sub ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
    (continuous_denominator n) (fun q => ne_of_gt (denominator_pos q)))

noncomputable def space (n : ℕ) : C(I × Simplex n, Simplex n) := by
  refine ⟨fun q => ⟨Finsupp.equivFunOnFinite.symm
    (fun j => (q.2.weights j - (1-denominator q)/(n+1:ℝ))/denominator q), ?_, ?_⟩, ?_⟩
  · intro j
    apply div_nonneg _ (denominator_pos q).le
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (show (0:ℝ) < n+1 by positivity)).mpr
    have h := minimum_le n q.2 j
    have hd : 1 - (n+1:ℝ)*minimum n q.2 ≤ denominator q := le_max_right _ _
    nlinarith
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change ∑ j, (q.2.weights j - (1-denominator q)/(n+1:ℝ))/denominator q = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Convexity.StdSimplex.total_of_fintype,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply (div_eq_one_iff_eq (ne_of_gt (denominator_pos q))).mpr
    push_cast
    field_simp
    ring
  · apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro j
    exact (((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd).sub
      ((continuous_const.sub (continuous_denominator n)).div_const _)).div
        (continuous_denominator n) (fun q => ne_of_gt (denominator_pos q))

def bottomSides (n : ℕ) : Set (I × Simplex n) :=
  {q | q.1 = 0 ∨ ∃ j, q.2.weights j = 0}

lemma retract_mem (n : ℕ) (q : I × Simplex n) : (time q, space n q) ∈ bottomSides n := by
  have hd := denominator_pos q
  rcases le_total (1 - (n+1:ℝ)*minimum n q.2) (1 - (q.1:ℝ)/2) with h | h
  · left
    apply Subtype.ext
    have he : denominator q = 1 - (q.1:ℝ)/2 := max_eq_left h
    change 2 - (2 - (q.1:ℝ))/denominator q = 0
    have : (2 - (q.1:ℝ))/denominator q = 2 := (div_eq_iff (ne_of_gt hd)).mpr (by rw [he]; ring)
    rw [this]; ring
  · right
    have he : denominator q = 1 - (n+1:ℝ)*minimum n q.2 := max_eq_right h
    obtain ⟨j,hj⟩ := minimum_attained n q.2
    refine ⟨j, ?_⟩
    change (q.2.weights j - (1-denominator q)/(n+1:ℝ))/denominator q = 0
    rw [he, ← hj]
    have hn : (n+1:ℝ) ≠ 0 := by positivity
    field_simp
    ring

noncomputable def retract (n : ℕ) : C(I × Simplex n, bottomSides n) :=
  ⟨fun q => ⟨(time q,space n q),retract_mem n q⟩,
    ((continuous_time n).prodMk (space n).continuous).subtype_mk _⟩

lemma retract_fixed (n : ℕ) (q : bottomSides n) : (retract n q).val = q.val := by
  have hd : denominator q.val = 1 := by
    apply le_antisymm (denominator_le_one q.val)
    rcases q.property with h | ⟨j,hj⟩
    · have : 1 - (q.val.1:ℝ)/2 = 1 := by rw [h]; norm_num
      exact this ▸ le_max_left _ _
    · have hm : minimum n q.val.2 = 0 :=
        le_antisymm (hj ▸ minimum_le n q.val.2 j) (minimum_nonneg n q.val.2)
      have : 1 - (n+1:ℝ)*minimum n q.val.2 = 1 := by rw [hm]; ring
      exact this ▸ le_max_right _ _
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (q.val.1:ℝ))/denominator q.val = _
    rw [hd]; simp
  · ext j
    change (q.val.2.weights j - (1-denominator q.val)/(n+1:ℝ))/denominator q.val = _
    rw [hd]; simp

def boundarySet (n : ℕ) : Set (Simplex n) := {x | ∃ j, x.weights j = 0}

lemma minimum_eq_zero {n : ℕ} (x : boundarySet n) : minimum n x = 0 := by
  obtain ⟨j,hj⟩ := x.property
  exact le_antisymm (hj ▸ minimum_le n x j) (minimum_nonneg n x)

lemma isClosed_boundarySet (n : ℕ) : IsClosed (boundarySet n) := by
  have he : boundarySet n = {x | minimum n x = 0} := by
    ext x
    constructor
    · intro hx; exact minimum_eq_zero ⟨x,hx⟩
    · intro hx
      obtain ⟨j,hj⟩ := minimum_attained n x
      exact ⟨j,hj.symm.trans hx⟩
  rw [he]
  exact isClosed_eq (continuous_minimum n) continuous_const

def bottomPiece (n : ℕ) : Bool → Set (bottomSides n) := by
  intro b
  cases b
  · exact {q | q.val.1 = 0}
  · exact {q | q.val.2 ∈ boundarySet n}

lemma isClosed_bottomPiece (n : ℕ) (b : Bool) : IsClosed (bottomPiece n b) := by
  cases b
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  · exact (isClosed_boundarySet n).preimage (continuous_snd.comp continuous_subtype_val)

lemma bottomPiece_cover (n : ℕ) (q : bottomSides n) : ∃ b, q ∈ bottomPiece n b := by
  rcases q.property with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

noncomputable def bottomPieceValue (a : C(Simplex n,X)) (H : C(I × boundarySet n,X)) :
    ∀ k, C(bottomPiece n k,X) := by
  intro b
  cases b
  · exact a.comp
      ⟨fun q => q.val.val.2, continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩
  · exact H.comp ⟨fun q => (q.val.val.1,⟨q.val.val.2,q.property⟩),
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)⟩

lemma bottomPieceValue_agree (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x)
    (j k : Bool) (q : bottomSides n) (hj : q ∈ bottomPiece n j) (hk : q ∈ bottomPiece n k) :
    bottomPieceValue a H j ⟨q,hj⟩ = bottomPieceValue a H k ⟨q,hk⟩ := by
  cases j <;> cases k
  · rfl
  · change a q.val.2 = H (q.val.1,⟨q.val.2,hk⟩)
    rw [show q.val.1 = 0 from hj]
    exact (ha ⟨q.val.2,hk⟩).symm
  · change H (q.val.1,⟨q.val.2,hj⟩) = a q.val.2
    rw [show q.val.1 = 0 from hk]
    exact ha _
  · rfl

noncomputable def bottomValue (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x) : C(bottomSides n,X) :=
  closedCoverPaste (bottomPiece n) (isClosed_bottomPiece n) (bottomPiece_cover n)
    (bottomPieceValue a H) (bottomPieceValue_agree a H ha)

noncomputable def extend (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x) : C(I × Simplex n,X) :=
  (bottomValue a H ha).comp (retract n)

lemma extend_onRoof (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x) (q : bottomSides n) :
    extend a H ha q = bottomValue a H ha q :=
  congrArg (bottomValue a H ha) (Subtype.ext (retract_fixed n q))

lemma extend_zero (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x) (x : Simplex n) :
    extend a H ha (0,x) = a x := by
  rw [extend_onRoof a H ha ⟨(0,x),Or.inl rfl⟩]
  exact closedCoverPaste_apply (bottomPiece n) (isClosed_bottomPiece n) (bottomPiece_cover n)
    (bottomPieceValue a H) (bottomPieceValue_agree a H ha) false _ rfl

lemma extend_side (a : C(Simplex n,X)) (H : C(I × boundarySet n,X))
    (ha : ∀ x : boundarySet n, H (0,x) = a x) (t : I) (x : boundarySet n) :
    extend a H ha (t,x) = H (t,x) := by
  rw [extend_onRoof a H ha ⟨(t,x),Or.inr x.property⟩]
  exact closedCoverPaste_apply (bottomPiece n) (isClosed_bottomPiece n) (bottomPiece_cover n)
    (bottomPieceValue a H) (bottomPieceValue_agree a H ha) true _ x.property

lemma boundary_faces_agree {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.boundary (n+1) : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (j k : Fin (n+2)) (x : Simplex (n+1)) (hxj : x.weights j = 0) (hxk : x.weights k = 0) :
    singularValue (SSet.boundary.ι j ≫ f) (drop j ⟨x,hxj⟩) =
      singularValue (SSet.boundary.ι k ≫ f) (drop k ⟨x,hxk⟩) := by
  by_cases he : j = k
  · subst k
    rfl
  suffices h : ∀ (j k : Fin (n+2)) (hjk : j < k) (hxj : x.weights j = 0) (hxk : x.weights k = 0),
      singularValue (SSet.boundary.ι j ≫ f) (drop j ⟨x,hxj⟩) =
        singularValue (SSet.boundary.ι k ≫ f) (drop k ⟨x,hxk⟩) by
    rcases lt_or_gt_of_ne he with hlt | hlt
    · exact h j k hlt hxj hxk
    · exact (h k j hlt hxk hxj).symm
  clear j k hxj hxk he
  intro j k hjk hxj hxk
  cases n with
  | zero =>
    have hs := Convexity.StdSimplex.total_of_fintype x
    rw [Fin.sum_univ_two] at hs
    fin_cases j <;> fin_cases k <;> norm_num at hjk
    change x.weights 0 = 0 at hxj
    change x.weights 1 = 0 at hxk
    linarith
  | succ n =>
    let b := k.pred (Fin.ne_zero_of_lt hjk)
    let a := j.castPred (Fin.ne_last_of_lt hjk)
    let y := drop j ⟨x,hxj⟩
    have hy : y.weights b = 0 := by
      change x.weights (j.succAbove b) = 0
      simpa only [b, Fin.succAbove_pred_of_lt j k hjk] using hxk
    let z := drop b ⟨y,hy⟩
    have hyz : Convexity.StdSimplex.map b.succAbove z = y := map_drop b y hy
    have hkz : Convexity.StdSimplex.map a.succAbove z = drop k ⟨x,hxk⟩ := by
      apply map_succAbove_injective k
      rw [map_drop, ← double_map j k hjk z, hyz]
      exact map_drop j x hxj
    have hc : SSet.stdSimplex.δ b ≫ (SSet.boundary.ι j ≫ f) =
        SSet.stdSimplex.δ a ≫ (SSet.boundary.ι k ≫ f) := by
      simp only [← Category.assoc]
      congr 1
      dsimp [a,b]
      obtain ⟨j,rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
      obtain ⟨k,rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
      rw [← cancel_mono (SSet.boundary (n+2)).ι, Category.assoc, Category.assoc,
        SSet.boundary.ι_ι, SSet.boundary.ι_ι, Fin.pred_succ, Fin.castPred_castSucc,
        SSet.stdSimplex.δ_comp_δ (by simpa using hjk)]
    have heq := congrArg (fun g => singularValue g z) hc
    rw [singularValue_delta, singularValue_delta] at heq
    change singularValue (SSet.boundary.ι j ≫ f) (Convexity.StdSimplex.map b.succAbove z) =
      singularValue (SSet.boundary.ι k ≫ f) (Convexity.StdSimplex.map a.succAbove z) at heq
    rwa [hyz,hkz] at heq

noncomputable def boundaryValue {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.boundary (n+1) : SSet.{u}) ⟶ TopCat.toSSet.obj X) : C(boundarySet (n+1), X) :=
  closedCoverPaste (fun j : Fin (n+2) => {x | x.val.weights j = 0})
    (fun j => isClosed_eq ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp
      continuous_subtype_val) continuous_const)
    (fun x => by obtain ⟨j,hj⟩ := x.property; exact ⟨j,hj⟩)
    (fun j => (singularValue (SSet.boundary.ι j ≫ f)).comp
      ((drop j).comp ⟨fun x => ⟨x.val.val,x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩))
    (fun j k x hj hk => boundary_faces_agree f j k x.val hj hk)

lemma boundaryValue_face {X : TopCat.{u}} {n : ℕ}
    (f : (SSet.boundary (n+1) : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (j : Fin (n+2)) (x : Simplex n) :
    boundaryValue f ⟨Convexity.StdSimplex.map j.succAbove x,j,map_succAbove_pivot j x⟩ =
      singularValue (SSet.boundary.ι j ≫ f) x := by
  rw [boundaryValue, closedCoverPaste_apply (j := j) (ha := map_succAbove_pivot j x)]
  change singularValue (SSet.boundary.ι j ≫ f)
    (drop j ⟨Convexity.StdSimplex.map j.succAbove x, map_succAbove_pivot j x⟩) = _
  rw [drop_map]

open Simplicial
lemma boundaryValue_square {X Y : TopCat.{u}} {n : ℕ}
    (g : (SSet.boundary (n+1) : SSet.{u}) ⟶ TopCat.toSSet.obj X)
    (f : (SSet.stdSimplex.obj ⦋n+1⦌ : SSet.{u}) ⟶ TopCat.toSSet.obj Y) (p : X ⟶ Y)
    (h : g ≫ TopCat.toSSet.map p = (SSet.boundary (n+1)).ι ≫ f) (x : boundarySet (n+1)) :
    p (boundaryValue g x) = singularValue f x := by
  obtain ⟨j,hx⟩ := x.property
  let y := drop j ⟨x.val,hx⟩
  have he : (⟨Convexity.StdSimplex.map j.succAbove y,j,map_succAbove_pivot j y⟩ : boundarySet (n+1)) = x :=
    Subtype.ext (map_drop j x hx)
  rw [← he,boundaryValue_face]
  have hh : (SSet.boundary.ι j ≫ g) ≫ TopCat.toSSet.map p = SSet.stdSimplex.δ j ≫ f := by
    rw [Category.assoc,h,SSet.boundary.ι_ι_assoc]
  simpa only [singularValue_post,singularValue_delta] using congrArg (fun φ => singularValue φ y) hh

noncomputable def pathStart (T : TopCat.{u}) : TopCat.of C(I,T) ⟶ T :=
  TopCat.ofHom ⟨fun γ => γ 0, continuous_eval_const 0⟩

theorem singular_pathStart_boundary_rlp (T : TopCat.{u}) :
    SSet.modelCategoryQuillen.I.rlp (TopCat.toSSet.map (pathStart T)) := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro g f sq
  cases n with
  | zero =>
    let h : C(Simplex 0,C(I,T)) := ContinuousMap.const'.comp (singularValue f)
    let φ := SSet.yonedaEquiv.symm (((PathSpace T).toSSetObjEquiv _).symm h)
    have hφ : singularValue φ = h := by simp only [singularValue,φ,Equiv.apply_symm_apply]
    refine ⟨⟨{ l := φ, fac_left := SSet.boundary.hom_ext₀, fac_right := ?_ }⟩⟩
    apply SSet.yonedaEquiv.injective
    apply (T.toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro x
    change singularValue (φ ≫ TopCat.toSSet.map (pathStart T)) x = singularValue f x
    rw [singularValue_post,hφ]
    rfl
  | succ n =>
    let H : C(I × boundarySet (n+1),T) := (boundaryValue g).uncurry.comp ⟨Prod.swap,continuous_swap⟩
    let a : C(Simplex (n+1),T) := singularValue f
    have ha (x : boundarySet (n+1)) : H (0,x) = a x :=
      boundaryValue_square g f (pathStart T) sq.w x
    let h : C(Simplex (n+1),C(I,T)) :=
      ((extend a H ha).comp ⟨Prod.swap,continuous_swap⟩).curry
    let φ := SSet.yonedaEquiv.symm (((PathSpace T).toSSetObjEquiv _).symm h)
    have hφ : singularValue φ = h := by simp only [singularValue,φ,Equiv.apply_symm_apply]
    refine ⟨⟨{ l := φ, fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply SSet.boundary.hom_ext
      intro j
      rw [SSet.boundary.ι_ι_assoc]
      apply SSet.yonedaEquiv.injective
      apply ((PathSpace T).toSSetObjEquiv _).injective
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro t
      change singularValue (SSet.stdSimplex.δ j ≫ φ) x t =
        singularValue (SSet.boundary.ι j ≫ g) x t
      rw [singularValue_delta,hφ]
      change extend a H ha (t,Convexity.StdSimplex.map j.succAbove x) = _
      rw [extend_side a H ha t ⟨Convexity.StdSimplex.map j.succAbove x,j,map_succAbove_pivot j x⟩]
      change boundaryValue g ⟨Convexity.StdSimplex.map j.succAbove x,j,map_succAbove_pivot j x⟩ t = _
      rw [boundaryValue_face]
    · apply SSet.yonedaEquiv.injective
      apply (T.toSSetObjEquiv _).injective
      apply ContinuousMap.ext
      intro x
      change singularValue (φ ≫ TopCat.toSSet.map (pathStart T)) x = singularValue f x
      rw [singularValue_post,hφ]
      exact extend_zero a H ha x

theorem realization_mono_homotopy_extension {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (T : TopCat.{u}) : HasLiftingProperty (SSet.toTop.map i) (pathStart T) := by
  rw [sSetTopAdj.hasLiftingProperty_iff]
  have hp : (MorphismProperty.monomorphisms SSet).rlp (TopCat.toSSet.map (pathStart T)) := by
    rw [SSet.rlp_monomorphisms]
    exact singular_pathStart_boundary_rlp T
  exact hp i inferInstance
end Thomason.TopologicalCylinder

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy
open scoped Topology Topology.Homotopy
variable {X : Type u} {Y : Type v} {Z : Type w} {T : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

lemma Equivalence.middle {f : C(X,Y)} {g : C(Y,Z)} {h : C(Z,T)}
    (hfg : Equivalence (g.comp f)) (hgh : Equivalence (h.comp g)) : Equivalence g := by
  have hfg₀ : Function.Bijective (componentsMap g ∘ componentsMap f) := by
    rw [show componentsMap g ∘ componentsMap f = componentsMap (g.comp f) from
      funext (componentsMap_comp f g)]
    exact hfg.1
  have hgh₀ : Function.Bijective (componentsMap h ∘ componentsMap g) := by
    rw [show componentsMap h ∘ componentsMap g = componentsMap (h.comp g) from
      funext (componentsMap_comp g h)]
    exact hgh.1
  have hg₀ : Function.Bijective (componentsMap g) :=
    ⟨hgh₀.injective.of_comp, hfg₀.surjective.of_comp⟩
  have hf₀ : Function.Bijective (componentsMap f) :=
    (Function.Bijective.of_comp_iff' hg₀ _).mp hfg₀
  refine ⟨hg₀, ?_⟩
  intro n y
  obtain ⟨c, hc⟩ := hf₀.surjective (ZerothHomotopy.mk y)
  induction c using ZerothHomotopy.rec with
  | mk x =>
    have he : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk y := hc
    obtain ⟨γ⟩ : Nonempty (Path (f x) y) := Quotient.exact he
    apply groupMap_bijective_along_path g γ
    have hfgn := hfg.2 n x
    have hghn := hgh.2 n (f x)
    rw [groupMap_comp] at hfgn hghn
    exact ⟨hghn.injective.of_comp, hfgn.surjective.of_comp⟩
end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory
lemma simplicialWeakEquivalences_middle {W X Y Z : SSet.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : simplicialWeakEquivalences (f ≫ g))
    (hgh : simplicialWeakEquivalences (g ≫ h)) : simplicialWeakEquivalences g := by
  apply WeakHomotopy.Equivalence.middle (f := (SSet.toTop.map f).hom)
    (h := (SSet.toTop.map h).hom)
  · simpa only [simplicialWeakEquivalences, topologicalWeakEquivalences,
      MorphismProperty.inverseImage, Functor.map_comp, TopCat.hom_comp] using hfg
  · simpa only [simplicialWeakEquivalences, topologicalWeakEquivalences,
      MorphismProperty.inverseImage, Functor.map_comp, TopCat.hom_comp] using hgh
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

lemma zeroFactor_one (X : SSet.{u}) :
    (SimplicialCylinder.zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) 0 = SSet.ι₁ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl

lemma extend_one {A B T : SSet.{u}} (i : A ⟶ B) [Mono i] [SSet.KanComplex T]
    (g : B ⟶ T) (H : A ⊗ Δ[1] ⟶ T) (h₁ : SSet.ι₁ ≫ H = i ≫ g) :
    ∃ Q : B ⊗ Δ[1] ⟶ T, (i ▷ Δ[1]) ≫ Q = H ∧ SSet.ι₁ ≫ Q = g := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hc : i ▷ Δ[0] ≫ (fst B Δ[0] ≫ g) = A ◁ SSet.stdSimplex.δ (n := 0) 0 ≫ H := by
    apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
    rw [← Category.assoc _ _ H, zeroFactor_one, h₁]
    rfl
  let a : sq.pt ⟶ T := sq.isPushout.desc (fst B Δ[0] ≫ g) H hc
  have : HasLiftingProperty sq.ι (terminal.from T) :=
    SSet.anodyneExtensions_pushoutObjObjι sq (SimplicialCylinder.delta_one_anodyne 0)
      (terminal.from T) (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let lsq : CommSq a sq.ι (terminal.from T) (terminal.from (B ⊗ Δ[1])) := ⟨by simp⟩
  have hi : sq.inr ≫ sq.ι = i ▷ Δ[1] := sq.inr_ι
  have hj : sq.inl ≫ sq.ι = B ◁ SSet.stdSimplex.δ (n := 0) 0 := sq.inl_ι
  refine ⟨lsq.lift, ?_, ?_⟩
  · rw [← hi, Category.assoc, lsq.fac_left]
    exact sq.isPushout.inr_desc _ _ _
  · rw [← zeroFactor_one B, Category.assoc, ← hj, Category.assoc, lsq.fac_left]
    rw [sq.isPushout.inl_desc]
    rfl
end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def toHomotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : A ⊗ Δ[1] ⟶ B)
    (h₀ : SSet.ι₀ ≫ H = f) (h₁ : SSet.ι₁ ≫ H = g) : SSet.Homotopy f g where
  h := H
  h₀ := h₀
  h₁ := h₁
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma pushout_weak {K A B C P Q : SSet.{u}} (k : K ⟶ A) (c : K ⟶ C) [Mono c]
    (f : A ⟶ B) (g : B ⟶ A)
    (HA : SSet.Homotopy (f ≫ g) (𝟙 A)) (HB : SSet.Homotopy (g ≫ f) (𝟙 B))
    (coh : HA.h ≫ f = (f ▷ Δ[1]) ≫ HB.h)
    {lA : A ⟶ P} {lC : C ⟶ P} (sp : IsPushout k c lA lC)
    {lB : B ⟶ Q} {lC' : C ⟶ Q} (sq : IsPushout (k ≫ f) c lB lC')
    (F : P ⟶ Q) (hFA : lA ≫ F = f ≫ lB) (hFC : lC ≫ F = lC') :
    simplicialWeakEquivalences F := by
  dsimp only [SSet.Homotopy] at HA HB
  let R := Subdivision.exInfinityFunctor
  let eP : P ⟶ R.obj P := Subdivision.exInfinityComparison P
  let eQ : Q ⟶ R.obj Q := Subdivision.exInfinityComparison Q
  have hnat : eP ≫ R.map F = F ≫ eQ := (Subdivision.exInfinityUnit.naturality F).symm
  have : SSet.KanComplex (R.obj P) := Subdivision.exInfinity_kan P
  obtain ⟨HC,hCK,hC₁⟩ := extend_one c (lC ≫ eP) ((k ▷ Δ[1]) ≫ HA.h ≫ lA ≫ eP) (by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁_assoc HA,
      Category.id_comp, ← Category.assoc k lA, sp.w]
    simp only [Category.assoc])
  let gC := SSet.ι₀ ≫ HC
  have hgK : (k ≫ f) ≫ (g ≫ lA ≫ eP) = c ≫ gC := by
    dsimp only [gC]
    rw [← SSet.ι₀_comp_assoc, hCK]
    simp only [SSet.ι₀_comp_assoc, SSet.Homotopy.h₀_assoc HA, Category.assoc]
  let G : Q ⟶ R.obj P := sq.desc (g ≫ lA ≫ eP) gC hgK
  have hGB : lB ≫ G = g ≫ lA ≫ eP := sq.inl_desc _ _ _
  have hGC : lC' ≫ G = gC := sq.inr_desc _ _ _
  have spI := sp.map (tensorRight (Δ[1] : SSet.{u}))
  let HP : P ⊗ Δ[1] ⟶ R.obj P := spI.desc (HA.h ≫ lA ≫ eP) HC hCK.symm
  have hPA : lA ▷ Δ[1] ≫ HP = HA.h ≫ lA ≫ eP := spI.inl_desc _ _ _
  have hPC : lC ▷ Δ[1] ≫ HP = HC := spI.inr_desc _ _ _
  have hP₀ : SSet.ι₀ ≫ HP = F ≫ G := by
    apply sp.hom_ext
    · erw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hPA,
        SSet.Homotopy.h₀_assoc HA, ← Category.assoc lA F G, hFA]
      simp only [Category.assoc, hGB]
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hPC,
        ← Category.assoc lC F G, hFC, hGC]
  have hP₁ : SSet.ι₁ ≫ HP = eP := by
    apply sp.hom_ext
    · erw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hPA,
        SSet.Homotopy.h₁_assoc HA, Category.id_comp]
    · erw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hPC,hC₁]
  have hqK : ((k ≫ f) ▷ Δ[1]) ≫ (HB.h ≫ lB ≫ eQ) =
      (c ▷ Δ[1]) ≫ (HC ≫ R.map F) := by
    erw [← Category.assoc _ HC, hCK]
    simp only [Category.assoc]
    rw [hnat, ← Category.assoc lA F, hFA]
    simp only [Category.assoc]
    rw [← Category.assoc HA.h f, coh]
    simp only [comp_whiskerRight, Category.assoc]
  have sqI := sq.map (tensorRight (Δ[1] : SSet.{u}))
  let HQ : Q ⊗ Δ[1] ⟶ R.obj Q := sqI.desc (HB.h ≫ lB ≫ eQ) (HC ≫ R.map F) hqK
  have hQB : lB ▷ Δ[1] ≫ HQ = HB.h ≫ lB ≫ eQ := sqI.inl_desc _ _ _
  have hQC : lC' ▷ Δ[1] ≫ HQ = HC ≫ R.map F := sqI.inr_desc _ _ _
  have hQ₀ : SSet.ι₀ ≫ HQ = G ≫ R.map F := by
    apply sq.hom_ext
    · erw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hQB, SSet.Homotopy.h₀_assoc HB,
        ← Category.assoc lB G, hGB]
      simp only [Category.assoc]
      rw [hnat, ← Category.assoc lA F, hFA]
      simp only [Category.assoc]
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hQC,
        ← Category.assoc lC' G, hGC]
      rfl
  have hQ₁ : SSet.ι₁ ≫ HQ = eQ := by
    apply sq.hom_ext
    · erw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hQB,
        SSet.Homotopy.h₁_assoc HB, Category.id_comp]
    · erw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hQC,
        ← Category.assoc SSet.ι₁ HC, hC₁, Category.assoc, hnat,
        ← Category.assoc, hFC]
  have hFG : simplicialWeakEquivalences (F ≫ G) :=
    (simplicialWeakEquivalences_homotopy (toHomotopy HP hP₀ hP₁)).mpr
      (Subdivision.exInfinityComparison_weak P)
  have hGR : simplicialWeakEquivalences (G ≫ R.map F) :=
    (simplicialWeakEquivalences_homotopy (toHomotopy HQ hQ₀ hQ₁)).mpr
      (Subdivision.exInfinityComparison_weak Q)
  exact simplicialWeakEquivalences.of_postcomp F G
    (simplicialWeakEquivalences_middle F G (R.map F) hFG hGR) hFG
end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def endpoint (X : SSet.{u}) (j : Fin 2) : X ⟶ X ⊗ Δ[1] :=
  (SimplicialCylinder.zeroFactorIso X).hom ≫ X ◁ SSet.stdSimplex.δ (n := 0) j

@[reassoc] lemma endpoint_natural {A B : SSet.{u}} (f : A ⟶ B) (j : Fin 2) :
    f ≫ endpoint B j = endpoint A j ≫ f ▷ Δ[1] := by
  rfl

lemma endpoint_zero (X : SSet.{u}) : endpoint X 1 = SSet.ι₀ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl
lemma endpoint_one (X : SSet.{u}) : endpoint X 0 = SSet.ι₁ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro z
    rfl

lemma cylinder_lift {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (p : X ⟶ Y) (hp : simplicialFibrations p) (j : Fin 2)
    (l : B ⟶ X) (H : A ⊗ Δ[1] ⟶ X) (K : B ⊗ Δ[1] ⟶ Y)
    (hA : endpoint A j ≫ H = i ≫ l)
    (hB : endpoint B j ≫ K = l ≫ p)
    (hC : H ≫ p = i ▷ Δ[1] ≫ K) :
    ∃ Q : B ⊗ Δ[1] ⟶ X,
      i ▷ Δ[1] ≫ Q = H ∧ endpoint B j ≫ Q = l ∧ Q ≫ p = K := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) j)
  have hc : i ▷ Δ[0] ≫ (fst B Δ[0] ≫ l) = A ◁ SSet.stdSimplex.δ (n := 0) j ≫ H := by
    apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
    exact hA.symm
  let a : s.pt ⟶ X := s.isPushout.desc (fst B Δ[0] ≫ l) H hc
  have hs : a ≫ p = s.ι ≫ K := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc, s.isPushout.inl_desc, ← Category.assoc, s.inl_ι]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso B).hom).mp
      exact hB.symm
    · rw [← Category.assoc, s.isPushout.inr_desc, ← Category.assoc, s.inr_ι]
      exact hC
  have : HasLiftingProperty s.ι p :=
    SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne j) p hp
  let sq : CommSq a s.ι p K := ⟨hs⟩
  have hi : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  have hj : s.inl ≫ s.ι = B ◁ SSet.stdSimplex.δ (n := 0) j := s.inl_ι
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← hi, Category.assoc, sq.fac_left]
    exact s.isPushout.inr_desc _ _ _
  · dsimp only [endpoint]
    rw [Category.assoc, ← hj, Category.assoc, sq.fac_left, s.isPushout.inl_desc]
    rfl

lemma anodyne_of_coherent_span {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (g : B ⟶ A) (cA : A ⟶ A) (cB : B ⟶ B)
    (H₀ : SSet.Homotopy (i ≫ g) cA) (K₀ : SSet.Homotopy (g ≫ i) cB)
    (H₁ : SSet.Homotopy (𝟙 A) cA) (K₁ : SSet.Homotopy (𝟙 B) cB)
    (coh₀ : H₀.h ≫ i = i ▷ Δ[1] ≫ K₀.h)
    (coh₁ : H₁.h ≫ i = i ▷ Δ[1] ≫ K₁.h) : SSet.anodyneExtensions i := by
  intro X Y p hp
  constructor
  intro a b s
  obtain ⟨Q,hQA,hQ₀,hQp⟩ := cylinder_lift i p hp 1 (g ≫ a)
    (H₀.h ≫ a) (K₀.h ≫ b)
    (by rw [endpoint_zero, H₀.h₀_assoc]; simp only [Category.assoc])
    (by rw [endpoint_zero, K₀.h₀_assoc]; simpa only [Category.assoc] using congrArg (g ≫ ·) s.w.symm)
    (by rw [Category.assoc, s.w, ← Category.assoc H₀.h i, coh₀]; simp)
  let l := SSet.ι₁ ≫ Q
  have hlA : i ≫ l = cA ≫ a := by
    dsimp only [l]
    rw [← SSet.ι₁_comp_assoc, hQA, H₀.h₁_assoc]
  have hlB : l ≫ p = cB ≫ b := by
    dsimp only [l]
    rw [Category.assoc, hQp, K₀.h₁_assoc]
  obtain ⟨R,hRA,hR₁,hRp⟩ := cylinder_lift i p hp 0 l
    (H₁.h ≫ a) (K₁.h ≫ b)
    (by rw [endpoint_one, H₁.h₁_assoc, hlA])
    (by rw [endpoint_one, K₁.h₁_assoc, hlB])
    (by rw [Category.assoc, s.w, ← Category.assoc H₁.h i, coh₁]; simp)
  refine ⟨⟨{ l := SSet.ι₀ ≫ R, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← SSet.ι₀_comp_assoc, hRA, H₁.h₀_assoc, Category.id_comp]
  · rw [Category.assoc, hRp, K₁.h₀_assoc, Category.id_comp]
end Thomason.HornSubdivision

end

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory PartialOrder

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def orderCylinder (f g : P →o Q) (h : ∀ x, f x ≤ g x) : OneCat.Interval.{u} × P →o Q where
  toFun x := if x.1.down = 0 then f x.2 else g x.2
  monotone' := by
    rintro ⟨⟨b⟩,x⟩ ⟨⟨c⟩,y⟩ ⟨hbc,hxy⟩
    fin_cases b <;> fin_cases c
    · exact f.monotone hxy
    · exact (h x).trans (g.monotone hxy)
    · exact False.elim (by simp at hbc)
    · exact g.monotone hxy

def orderCylinderCat (f g : P →o Q) (h : ∀ x, f x ≤ g x) :
    OneCat.cylinder.obj (Cat.of P) ⟶ Cat.of Q :=
  ({ obj := orderCylinder f g h
     map := fun a => homOfLE ((orderCylinder f g h).monotone ⟨leOfHom a.1,leOfHom a.2⟩) } :
    OneCat.Interval.{u} × P ⥤ Q).toCatHom

def orderHomotopy (f g : P →o Q) (h : ∀ x, f x ≤ g x) :
    SSet.Homotopy (nerveMap f.toFunctor) (nerveMap g.toFunctor) where
  h := OneCat.cylinderMap (C := Cat.of P) (D := Cat.of Q) (orderCylinderCat f g h)
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma orderHomotopy_coherent {A B : Type u} [PartialOrder A] [PartialOrder B]
    (i : A →o B) (fA gA : A →o A) (fB gB : B →o B)
    (hA : ∀ x, fA x ≤ gA x) (hB : ∀ x, fB x ≤ gB x)
    (hf : ∀ x, i (fA x) = fB (i x)) (hg : ∀ x, i (gA x) = gB (i x)) :
    (orderHomotopy fA gA hA).h ≫ nerveMap i.toFunctor =
      (nerveMap i.toFunctor ▷ Δ[1]) ≫ (orderHomotopy fB gB hB).h := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.Functor.ext (fun j => by
    change i (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
        then fA (x.1.obj j) else gA (x.1.obj j)) =
      (if (SSet.stdSimplex.objEquiv x.2).toOrderHom j = 0
        then fB (i (x.1.obj j)) else gB (i (x.1.obj j)))
    split_ifs <;> [exact hf _; exact hg _])

lemma hornFaceInclusion_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions (nerveMap (OrderHom.Subtype.val
      (fun chain : NonemptyFiniteChains (ULift.{u} (Fin (n+1))) =>
        chain ∈ Subdivision.HornFaces.{u} n k)).toFunctor) := by
  classical
  let B := NonemptyFiniteChains (ULift.{u} (Fin (n+1)))
  let A := Subdivision.HornFaces.{u} n k
  let i : A →o B := OrderHom.Subtype.val _
  let a₀ : A := Subdivision.hornFacePoint hn k
  let g : B →o A := OrderHom.const _ a₀
  let cA := Subdivision.hornFaceCone k
  let cB : B →o B := {
    toFun := fun s => ⟨insert (ULift.up k) s.finset, by simp, by
      intro a b
      exact le_total a.val b.val⟩
    monotone' := by
      intro s t h a ha
      rcases Finset.mem_insert.mp ha with ha | ha
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert.mpr (Or.inr (h ha)) }
  have hcB (s : B) : s ≤ cB s := fun _ => Finset.mem_insert_of_mem
  have hkB (s : B) : i a₀ ≤ cB s := by
    intro a ha
    have he : a = ULift.up k := by
      change a ∈ ({ULift.up k} : Finset _) at ha
      exact Finset.mem_singleton.mp ha
    subst a
    exact Finset.mem_insert_self _ _
  have : Mono (nerveMap i.toFunctor) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [CategoryTheory.mono_iff_injective]
    intro x y h
    exact CategoryTheory.Functor.ext (fun j => Subtype.ext (congrArg (fun z => z.obj j) h))
  let H₀ := orderHomotopy (g.comp i) cA (fun s => Subdivision.hornFacePoint_le_cone hn k s)
  let K₀ := orderHomotopy (i.comp g) cB hkB
  let H₁ := orderHomotopy (OrderHom.id) cA (fun s => Subdivision.le_hornFaceCone k s)
  let K₁ := orderHomotopy (OrderHom.id) cB hcB
  apply anodyne_of_coherent_span (nerveMap i.toFunctor) (nerveMap g.toFunctor)
    (nerveMap cA.toFunctor) (nerveMap cB.toFunctor) H₀ K₀ H₁ K₁
  · exact orderHomotopy_coherent i (g.comp i) cA (i.comp g) cB _ _ (fun _ => rfl) (fun _ => rfl)
  · exact orderHomotopy_coherent i OrderHom.id cA OrderHom.id cB _ _ (fun _ => rfl) (fun _ => rfl)
end Thomason.HornSubdivision

end

end OAI
