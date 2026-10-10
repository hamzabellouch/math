import Mathlib
import OAI.CategoryTheory.Thomason.CoreCouniversality

namespace OAI

/-! Atom Fibers. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits AbstractTransfer
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem finitePosetComparisonOfCore (T : RightIntervalCore.{u}) (n : ℕ)
    (hS : T.SimplexDescent n) (hn : 1 ≤ n) :
    PosetComparison (categorificationFinite.{u} n) (streetNerveFinite n)
      (categorificationFiniteAdjunction n) := by
  let := T.rightAdjoint
  exact {
    unit_weak := posetCategorificationFiniteUnit_weakEquivalence n hn
    attachment_mono := AttachmentComparison.finite_nerve_attachment_mono n hn
    comparison := AttachmentComparison.core_gray_comparison_local T
      T.tensor.rightAdjoint (Adjunction.ofIsLeftAdjoint T.tensor) n hS hn }

def finiteEndpointOfCore (T : RightIntervalCore.{u}) (n : ℕ)
    (hS : T.SimplexDescent n) (hn : 1 ≤ n) :
    ExactModelEndpoint (thomasonLeftFinite.{u} n) (thomasonRightFinite n)
      (thomasonFiniteAdjunction n) := by
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (hornImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} :=
    thomasonHornFinite_smallCardinal n
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (boundaryImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} :=
    thomasonBoundaryFinite_smallCardinal n
  exact AbstractTransfer.exactEndpoint (finitePosetComparisonOfCore T n hS hn)

def exactEndpointTwo :
    ExactModelEndpoint (thomasonLeftFinite.{u} 2) (thomasonRightFinite 2)
      (thomasonFiniteAdjunction 2) :=
  finiteEndpointOfCore GrayRecursive.IntervalHom.intervalCore 2
    RightIntervalCore.intervalCore_simplexDescent_two (by omega)

theorem endpointTwo : Nonempty
    (ExactModelEndpoint (thomasonLeftFinite.{u} 2) (thomasonRightFinite 2)
      (thomasonFiniteAdjunction 2)) := ⟨exactEndpointTwo⟩
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.Functor
open CategoryTheory

variable {C D : OmegaCategory.{u}} (F : C ⟶ D)

lemma onCells_injective_mono {n k : ℕ} (hkn : k ≤ n)
    (h : Function.Injective (F.onCells n)) : Function.Injective (F.onCells k) := by
  intro x y he
  have heq : F.map x.val = F.map y.val := congrArg Subtype.val he
  apply Subtype.ext
  exact congrArg (fun z : C.Cells n => z.val) (h
    (a₁ := ⟨x.val,C.source_fixed_upwards hkn x.property⟩)
    (a₂ := ⟨y.val,C.source_fixed_upwards hkn y.property⟩)
    (Subtype.ext heq))

lemma onCells_injective_of_map_injective (h : Function.Injective F.map) (n : ℕ) :
    Function.Injective (F.onCells n) := by
  intro x y he
  exact Subtype.ext (h (congrArg Subtype.val he))

lemma map_surjective_of_onCells_surjective
    (h : ∀ n, Function.Surjective (F.onCells n)) : Function.Surjective F.map := by
  intro y
  obtain ⟨n,hn⟩ := D.finite_dimension y
  obtain ⟨x,hx⟩ := h n ⟨y,hn⟩
  exact ⟨x.val,congrArg Subtype.val hx⟩

lemma map_injective_of_onCells_injective {n : ℕ} (hn : C.IsTruncated n)
    (h : Function.Injective (F.onCells n)) : Function.Injective F.map := by
  intro x y he
  exact congrArg Subtype.val
    (h (a₁ := ⟨x,hn x⟩) (a₂ := ⟨y,hn y⟩) (Subtype.ext he))

lemma onCells_injective_of_isIso [IsIso F] (n : ℕ) :
    Function.Injective (F.onCells n) := by
  apply F.onCells_injective_of_map_injective
  intro x y he
  have hx := congrArg (fun G : C ⟶ C => G.map x) (IsIso.hom_inv_id F)
  have hy := congrArg (fun G : C ⟶ C => G.map y) (IsIso.hom_inv_id F)
  change (inv F).map (F.map x) = x at hx
  change (inv F).map (F.map y) = y at hy
  exact hx.symm.trans ((congrArg (inv F).map he).trans hy)

end Thomason.OmegaCategory.Functor

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table OmegaCategory NormalizedChains

lemma chainComparison_finiteSimplex_surjective_of_lower_injective
    (P : Type u) [LinearOrder P] [Finite P] (n : ℕ)
    (h : ∀ k, k < n → Function.Injective
      ((chainComparison (NormalizedChains.complex P)).onCells k)) :
    Function.Surjective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofFinite P
  by_cases he : Fintype.card P = 0
  · let : IsEmpty P := Fintype.card_eq_zero_iff.mp he
    intro t
    exact isEmptyElim (PosetTables.tableStart
      ((NormalizedChains.complex P).cylinderProjection.table t.val))
  · have hp : Fintype.card P = (Fintype.card P - 1) + 1 := by omega
    let e := Fintype.orderIsoFinOfCardEq P hp
    apply (Prism.Basis.ofOrderIso e).surjective_onCells_of_lower_injective
      (chainComparison (NormalizedChains.complex P)) n h
    intro b hb
    obtain ⟨x,hx⟩ := chainComparison_atom_lift e b
    exact ⟨⟨x.val, (tensorFunctor.obj (NormalizedChains.complex P).nu).source_fixed_upwards hb x.property⟩,hx⟩

lemma chainComparison_finiteSimplex_isIso_of_injective
    (P : Type u) [LinearOrder P] [Finite P]
    (h : Function.Injective (chainComparison (NormalizedChains.complex P)).map) :
    IsIso (chainComparison (NormalizedChains.complex P)) := by
  exact (OmegaCategory.isoOfBijective (chainComparison (NormalizedChains.complex P))
    ⟨h,(chainComparison (NormalizedChains.complex P)).map_surjective_of_onCells_surjective
      (fun n => chainComparison_finiteSimplex_surjective_of_lower_injective P n
        (fun k _ => (chainComparison (NormalizedChains.complex P)).onCells_injective_of_map_injective h k))⟩).isIso_hom

lemma chainComparison_injective_of_higher_crossing {M : DirectedComplex.{u}}
    (h : ∀ n : ℕ, 3 ≤ n → ∀ x y : (tensorFunctor.obj M.nu).Cells n,
      tensorLabel x.val false = 0 → tensorLabel x.val true = 1 →
      tensorLabel y.val false = 0 → tensorLabel y.val true = 1 →
      (chainComparison M).map x.val = (chainComparison M).map y.val → x = y) :
    Function.Injective (chainComparison M).map := by
  apply chainComparison_injective_of_crossing
  intro x y hxs hxt hys hyt he
  obtain ⟨i,hi⟩ := (tensorFunctor.obj M.nu).finite_dimension x
  obtain ⟨j,hj⟩ := (tensorFunctor.obj M.nu).finite_dimension y
  by_cases hb : max i j ≤ 2
  · exact chainComparison_twocells_injective x y
      ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega) hi)
      ((tensorFunctor.obj M.nu).source_fixed_upwards (by omega) hj) he
  · exact congrArg Subtype.val (h (max i j) (by omega)
      ⟨x,(tensorFunctor.obj M.nu).source_fixed_upwards (le_max_left i j) hi⟩
      ⟨y,(tensorFunctor.obj M.nu).source_fixed_upwards (le_max_right i j) hj⟩
      hxs hxt hys hyt he)

theorem fullMain_of_standard_higher_crossing_injective
    (h : ∀ m n : ℕ, 3 ≤ n →
      ∀ x y : (tensorFunctor.obj (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).nu).Cells n,
      tensorLabel x.val false = 0 → tensorLabel x.val true = 1 →
      tensorLabel y.val false = 0 → tensorLabel y.val true = 1 →
      (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map x.val =
        (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map y.val → x = y) :
    FullMain.{u} := by
  apply fullMain_of_standardSimplexComparison_isIso
  intro m
  exact chainComparison_finiteSimplex_isIso_of_injective _
    (chainComparison_injective_of_higher_crossing (h m))

theorem fullMain_of_standard_top_crossing_injective
    (h : ∀ m : ℕ,
      ∀ x y : (tensorFunctor.obj (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).nu).Cells (m+3),
      tensorLabel x.val false = 0 → tensorLabel x.val true = 1 →
      tensorLabel y.val false = 0 → tensorLabel y.val true = 1 →
      (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map x.val =
        (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map y.val → x = y) :
    FullMain.{u} := by
  apply fullMain_of_standardSimplexComparison_isIso
  intro m
  apply chainComparison_finiteSimplex_isIso_of_injective
  apply chainComparison_injective_of_crossing
  intro x y hxs hxt hys hyt he
  have hb : (tensorFunctor.obj (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).nu).IsTruncated (m+3) :=
    tensor_truncated (NormalizedChains.table_truncated_of_card_le (n := m+2) (by simp))
  exact congrArg Subtype.val (h m ⟨x,hb x⟩ ⟨y,hb y⟩ hxs hxt hys hyt he)

lemma chainComparison_precomp_bijective_of_injective
    (P : Type u) [LinearOrder P] [Finite P] (n : ℕ)
    (h : Function.Injective ((chainComparison (NormalizedChains.complex P)).onCells n))
    (Y : OmegaCategory.{u}) (hY : Y.IsTruncated n) :
    Function.Bijective (fun G : (NormalizedChains.complex P).cylinder.nu ⟶ Y =>
      chainComparison (NormalizedChains.complex P) ≫ G) := by
  let F := chainComparison (NormalizedChains.complex P)
  have hs : ∀ k, k ≤ n+1 → Function.Surjective (F.onCells k) := by
    intro k hk
    apply chainComparison_finiteSimplex_surjective_of_lower_injective P k
    intro j hj
    exact F.onCells_injective_mono (by omega : j ≤ n) h
  exact F.precomp_bijective_truncated ⟨h,hs n (by omega)⟩ (hs (n+1) le_rfl) hY

lemma chainComparison_onCells_injective_of_iso {M N : DirectedComplex.{u}}
    (e : M ≅ N) (n : ℕ)
    (h : Function.Injective ((chainComparison M).onCells n)) :
    Function.Injective ((chainComparison N).onCells n) := by
  have : IsIso (tensorFunctor.map e.inv.nu) :=
    show IsIso ((DirectedComplex.nuFunctor ⋙ tensorFunctor).map e.inv) from inferInstance
  intro x y he
  apply (tensorFunctor.map e.inv.nu).onCells_injective_of_isIso n
  apply h
  apply Subtype.ext
  have hn := chainComparison_natural e.inv
  have hx := congrArg (fun F : tensorFunctor.obj N.nu ⟶ M.cylinder.nu => F.map x.val) hn
  have hy := congrArg (fun F : tensorFunctor.obj N.nu ⟶ M.cylinder.nu => F.map y.val) hn
  change (chainComparison M).map ((tensorFunctor.map e.inv.nu).map x.val) =
    e.inv.cylinder.nu.map ((chainComparison N).map x.val) at hx
  change (chainComparison M).map ((tensorFunctor.map e.inv.nu).map y.val) =
    e.inv.cylinder.nu.map ((chainComparison N).map y.val) at hy
  change (chainComparison M).map ((tensorFunctor.map e.inv.nu).map x.val) =
    (chainComparison M).map ((tensorFunctor.map e.inv.nu).map y.val)
  exact hx.trans ((congrArg e.inv.cylinder.nu.map (congrArg Subtype.val he)).trans hy.symm)

lemma chainComparison_onCells_injective_of_standard (n : ℕ)
    (h : ∀ m : ℕ, Function.Injective ((chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).onCells n))
    (P : Type u) [LinearOrder P] [Finite P] :
    Function.Injective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofFinite P
  by_cases hs : Fintype.card P ≤ 2
  · let := chainComparison_small_isIso P hs
    exact (chainComparison (NormalizedChains.complex P)).onCells_injective_of_isIso n
  · have hp : Fintype.card P = (Fintype.card P - 3) + 3 := by omega
    exact chainComparison_onCells_injective_of_iso (NormalizedChains.complexFinIso P hp) n
      (h (Fintype.card P - 3))

end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory GrayRecursive.IntervalHom

def finiteEndpointOfStandardInjectivity (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ m : ℕ, Function.Injective ((chainComparison
      (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).onCells n)) :
    ExactModelEndpoint (thomasonLeftFinite.{u} n) (thomasonRightFinite n)
      (thomasonFiniteAdjunction n) := by
  apply finiteEndpointOfCore intervalCore n ?_ hn
  intro P _ _ Y hY
  exact chainComparison_precomp_bijective_of_injective _ n
    (chainComparison_onCells_injective_of_standard n h _) Y hY
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma atom_face_coefficient_pos (b : A.Index) (p : ℕ) (hp : p < A.dim b) (e : Bool) :
    ∃ c : A.Index, 0 < A.coefficient c p ((A.atom b).row p e) := by
  induction p with
  | zero =>
    by_contra hn
    push Not at hn
    have he : (A.atom b).row 0 e = 0 := by
      apply A.ext 0
      intro c
      rw [map_zero]
      have hx := (A.positive 0 _).mp ((A.atom b).positive 0 e) c
      exact le_antisymm (hn c) hx
    have ha := (A.atom b).augmentation e
    rw [he,map_zero] at ha
    omega
  | succ p ih =>
    by_contra hn
    push Not at hn
    have he : (A.atom b).row (p+1) e = 0 := by
      apply A.ext (p+1)
      intro c
      rw [map_zero]
      exact le_antisymm (hn c)
        ((A.positive (p+1) _).mp ((A.atom b).positive (p+1) e) c)
    have hd := (A.atom b).boundary p e
    rw [he,map_zero] at hd
    have hh : (A.atom b).row p true = (A.atom b).row p false :=
      sub_eq_zero.mp hd.symm
    obtain ⟨c,hc⟩ := ih (by omega)
    have hs : A.coefficient c p ((A.atom b).row p false) ≠ 0 := by
      cases e
      · exact ne_of_gt hc
      · rw [← hh]; exact ne_of_gt hc
    have ht : A.coefficient c p ((A.atom b).row p true) ≠ 0 := by rw [hh]; exact hs
    have hr := A.ranked b p (by omega) false c hs
    have hr' := A.ranked b p (by omega) true c ht
    simp only [Bool.false_eq_true,ite_false,ite_true] at hr hr'
    omega

lemma basis_derivative_negative (p : ℕ) (b : A.Index) (hb : A.dim b = p+1) :
    ∃ c : A.Index, A.rank b < A.rank c ∧
      A.coefficient c p (K.d p (A.basis (p+1) b)) < 0 := by
  obtain ⟨c,hc⟩ := A.atom_face_coefficient_pos b p (by omega) false
  have hs : A.rank b < A.rank c := A.ranked b p (by omega) false c (ne_of_gt hc)
  have ht : A.coefficient c p ((A.atom b).row p true) = 0 := by
    by_contra hn
    have h := A.ranked b p (by omega) true c hn
    simp only [ite_true] at h
    omega
  refine ⟨c,hs,?_⟩
  have he : A.basis (p+1) b = (A.atom b).row (p+1) false := by rw [← hb,A.basis_own]
  rw [he,(A.atom b).boundary,map_sub,ht]
  omega

lemma maximal_transition_coefficient_le (p : ℕ) (z : K.Chain (p+1))
    (x : K.Chain p) (hz : z ∈ K.positive (p+1))
    (hy : x + K.d p z ∈ K.positive p) (b : A.Index)
    (hb : A.coefficient b (p+1) z ≠ 0)
    (hmax : ∀ c, A.coefficient c (p+1) z ≠ 0 → A.rank c ≤ A.rank b) :
    ∃ t : A.Index, A.coefficient b (p+1) z ≤ A.coefficient t p x := by
  classical
  obtain ⟨t,ht,hd⟩ := A.basis_derivative_negative p b (A.homogeneous b (p+1) z hb)
  have hnonpos (c : A.Index) :
      A.coefficient c (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) c)) ≤ 0 := by
    by_cases hc : A.coefficient c (p+1) z = 0
    · simp [hc]
    apply mul_nonpos_of_nonneg_of_nonpos ((A.positive (p+1) z).mp hz c)
    by_contra hn
    have h := (A.derivative_rank p c t (A.homogeneous c (p+1) z hc)).1 (lt_of_not_ge hn)
    have hm := hmax c hc
    omega
  have hsum : A.coefficient t p (K.d p z) ≤
      A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) := by
    rw [A.coefficient_derivative]
    calc
      _ ≤ ∑ c : A.Index, if c = b then A.coefficient b (p+1) z *
            A.coefficient t p (K.d p (A.basis (p+1) b)) else 0 := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : c = b
        · subst c; simp only; exact le_rfl
        · rw [ite_eq_right hc]; exact hnonpos c
      _ = _ := by simp
  have hmul : A.coefficient b (p+1) z * A.coefficient t p (K.d p (A.basis (p+1) b)) ≤
      - A.coefficient b (p+1) z := by
    calc
      _ ≤ A.coefficient b (p+1) z * (-1) := mul_le_mul_of_nonneg_left (by omega)
        ((A.positive (p+1) z).mp hz b)
      _ = _ := mul_neg_one _
  have hh := (A.positive p _).mp hy t
  rw [map_add] at hh
  exact ⟨t,by omega⟩

lemma top_coefficient_le_one (n : ℕ) (y : Table K) (hy : truncate n false y = y)
    (b : A.Index) : A.coefficient b n (y.row n false) ≤ 1 := by
  classical
  induction n generalizing y b with
  | zero =>
    obtain ⟨c,hc,rfl⟩ := A.objects_atomic y hy
    have he := A.top c b false
    rw [hc] at he
    rw [he]
    split_ifs <;> omega
  | succ n ihn =>
    generalize hm : (A.mass (n+1) (y.row (n+1) false)).toNat = m
    induction m using Nat.strong_induction_on generalizing y b with
    | h m ihm =>
      let z := y.row (n+1) false
      have hz : z ∈ K.positive (n+1) := y.positive (n+1) false
      by_cases he : z = 0
      · change A.coefficient b (n+1) z ≤ 1
        rw [he,map_zero]
        omega
      let S := Finset.univ.filter (fun c => A.coefficient c (n+1) z ≠ 0)
      have hs : S.Nonempty := by
        by_contra hn
        apply he
        apply A.ext (n+1)
        intro c
        rw [map_zero]
        by_contra hc
        exact hn ⟨c,by simp [S,hc]⟩
      obtain ⟨c,hc,hmax⟩ := Finset.exists_max_image S A.rank hs
      have hc' : A.coefficient c (n+1) z ≠ 0 := (Finset.mem_filter.mp hc).2
      have hmax' : ∀ d, A.coefficient d (n+1) z ≠ 0 → A.rank d ≤ A.rank c :=
        fun d hd => hmax d (by simp [S,hd])
      have hp : 0 < A.coefficient c (n+1) z :=
        lt_of_le_of_ne ((A.positive (n+1) z).mp hz c) (Ne.symm hc')
      have hd := A.homogeneous c (n+1) z hc'
      have hfinal : y.row n false + K.d n z ∈ K.positive n := by
        change y.row n false + K.d n (y.row (n+1) false) ∈ _
        rw [y.boundary]
        convert y.positive n true using 1; abel
      by_cases hbc : b = c
      · subst b
        obtain ⟨t,ht⟩ := A.maximal_transition_coefficient_le n z (y.row n false) hz hfinal c hc' hmax'
        have hi := ihn (truncate n false y) (by simp only [truncate_truncate,lt_self_iff_false,ite_false]) t
        change A.coefficient t n ((truncate n false y).row n false) ≤ 1 at hi
        simp only [truncate_row, lt_self_iff_false, ite_false, ite_true] at hi
        exact ht.trans hi
      · have hrem := A.peel_remainder (n+1) z hz c hp
        have hpos := A.peel_positive n z (y.row n false) hz (y.positive n false) hfinal c hp hmax'
        obtain ⟨x,w,hxw,hx,hw,hxt,hwt,heq⟩ :=
          split_top y hy (A.basis (n+1) c) (z - A.basis (n+1) c)
            (A.basis_positive (n+1) c) hrem (by dsimp [z]; abel) hpos
        have hlt : (A.mass (n+1) (w.row (n+1) false)).toNat < m := by
          rw [hwt,map_sub,A.mass_basis (n+1) c hd,← hm]
          change (A.mass (n+1) z - 1).toNat < (A.mass (n+1) z).toNat
          rw [Int.toNat_lt_toNat (A.mass_pos (n+1) z hz c hp)]
          omega
        have hi := ihm _ hlt w hw b rfl
        rw [hwt,map_sub,A.coefficient_basis,ite_eq_left hd,ite_eq_right (Ne.symm hbc),sub_zero] at hi
        exact hi

lemma row_coefficient_zero_or_one (y : Table K) (p : ℕ) (e : Bool) (b : A.Index) :
    A.coefficient b p (y.row p e) = 0 ∨ A.coefficient b p (y.row p e) = 1 := by
  have hn := (A.positive p _).mp (y.positive p e) b
  have hu := A.top_coefficient_le_one p (truncate p e y)
    (by simp only [truncate_truncate,lt_self_iff_false,ite_false]) b
  simp only [truncate_row, lt_self_iff_false, ite_false, ite_true] at hu
  omega
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
include A

lemma positive_cycle_zero (p : ℕ) (z : K.Chain (p+1))
    (hz : z ∈ K.positive (p+1)) (hd : K.d p z = 0) : z = 0 := by
  classical
  by_contra he
  let S := Finset.univ.filter (fun c => A.coefficient c (p+1) z ≠ 0)
  have hs : S.Nonempty := by
    by_contra hn
    apply he
    apply A.ext (p+1)
    intro c
    rw [map_zero]
    by_contra hc
    exact hn ⟨c,by simp [S,hc]⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S A.rank hs
  have hb' : A.coefficient b (p+1) z ≠ 0 := (Finset.mem_filter.mp hb).2
  obtain ⟨t,ht⟩ := A.maximal_transition_coefficient_le p z 0 hz
    (by rw [hd,add_zero]; exact (K.positive p).zero_mem) b hb'
    (fun c hc => hmax c (by simp [S,hc]))
  rw [map_zero] at ht
  exact hb' (le_antisymm ht ((A.positive (p+1) z).mp hz b))

lemma positiveAcyclic : PositiveAcyclic K where
  augmentation_nonneg x hx := by rw [A.augmentation_eq_mass]; exact A.mass_nonneg _ _ hx
  augmentation_zero := A.positive_augmentation_zero
  cycle_zero := A.positive_cycle_zero

lemma positive_split_basis (p : ℕ) (b : A.Index) (hb : A.dim b = p)
    (x y : K.Chain p) (hx : x ∈ K.positive p) (hy : y ∈ K.positive p)
    (he : x+y = A.basis p b) : x = 0 ∨ y = 0 := by
  have h (c : A.Index) := congrArg (A.coefficient c p) he
  simp only [map_add,A.coefficient_basis,ite_eq_left hb] at h
  have hbx := (A.positive p x).mp hx b
  have hby := (A.positive p y).mp hy b
  have hsum : A.coefficient b p x + A.coefficient b p y = 1 := by simpa using h b
  have heq (c : A.Index) (hc : c ≠ b) : A.coefficient c p x = 0 ∧ A.coefficient c p y = 0 := by
    have hh := h c
    rw [ite_eq_right (Ne.symm hc)] at hh
    have hhx := (A.positive p x).mp hx c
    have hhy := (A.positive p y).mp hy c
    omega
  have hh : A.coefficient b p x = 0 ∨ A.coefficient b p y = 0 := by omega
  rcases hh with hx0 | hy0
  · left
    apply A.ext p
    intro c
    rw [map_zero]
    by_cases hc : c = b
    · simpa only [hc] using hx0
    · exact (heq c hc).1
  · right
    apply A.ext p
    intro c
    rw [map_zero]
    by_cases hc : c = b
    · simpa only [hc] using hy0
    · exact (heq c hc).2

lemma atom_subrows_fixed (b : A.Index) (k n : ℕ) (hn : n ≤ A.dim b)
    (x : Table K) (hx : truncate n false x = x)
    (hsub : ∀ p, k < p → ∀ e c,
      A.coefficient c p (x.row p e) ≤ A.coefficient c p ((A.atom b).row p e))
    (htop : x.row (A.dim b) false = 0) : truncate k false x = x := by
  induction n generalizing x with
  | zero => exact K.nu.source_fixed_upwards (Nat.zero_le k) hx
  | succ n ih =>
    by_cases hk : n+1 ≤ k
    · exact K.nu.source_fixed_upwards hk hx
    have hkn : k < n+1 := by omega
    have he : x.row (n+1) false = 0 := by
      by_cases he : n+1 = A.dim b
      · exact (congrArg (fun p => x.row p false = 0) he).mpr htop
      apply A.ext (n+1)
      intro c
      rw [map_zero]
      have hc := (A.positive (n+1) _).mp (x.positive (n+1) false) c
      by_contra hne
      have hpos : 0 < A.coefficient c (n+1) (x.row (n+1) false) := by omega
      have hs := hsub (n+1) hkn false c
      have ht := hsub (n+1) hkn true c
      rw [← row_top_fixed x hx] at ht
      have hrs := A.ranked b (n+1) (by omega) false c (ne_of_gt (hpos.trans_le hs))
      have hrt := A.ranked b (n+1) (by omega) true c (ne_of_gt (hpos.trans_le ht))
      simp only [Bool.false_eq_true,ite_false,ite_true] at hrs hrt
      omega
    exact ih (by omega) x (fixed_of_top_zero hx he) hsub htop

lemma atom_indecomposable (b : A.Index) (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (he : comp k x y h = A.atom b) :
    truncate k false x = x ∨ truncate k false y = y := by
  have hz : truncate (A.dim b) false (comp k x y h) = comp k x y h := by
    rw [he]; exact A.bounded b
  obtain ⟨hx,hy⟩ := A.comp_dimension_factors x y h hz
  by_cases hk : A.dim b ≤ k
  · exact Or.inl (K.nu.source_fixed_upwards hk hx)
  have hkd : k < A.dim b := by omega
  have hrows (p : ℕ) (hp : k < p) (e : Bool) :
      x.row p e + y.row p e = (A.atom b).row p e := by
    have hh := congrArg (fun z : Table K => z.row p e) he
    rw [comp_row] at hh
    simpa only [show ¬p < k by omega,show p ≠ k by omega,ite_false] using hh
  have hsub (p : ℕ) (hp : k < p) (e : Bool) (c : A.Index) :
      A.coefficient c p (x.row p e) ≤ A.coefficient c p ((A.atom b).row p e) ∧
      A.coefficient c p (y.row p e) ≤ A.coefficient c p ((A.atom b).row p e) := by
    have hh := congrArg (A.coefficient c p) (hrows p hp e)
    rw [map_add] at hh
    have hhx := (A.positive p _).mp (x.positive p e) c
    have hhy := (A.positive p _).mp (y.positive p e) c
    omega
  have ht : x.row (A.dim b) false + y.row (A.dim b) false = A.basis (A.dim b) b := by
    rw [A.basis_own]; exact hrows (A.dim b) hkd false
  rcases A.positive_split_basis (A.dim b) b rfl _ _ (x.positive _ _) (y.positive _ _) ht with hxt | hyt
  · exact Or.inl (A.atom_subrows_fixed b k (A.dim b) le_rfl x hx
      (fun p hp e c => (hsub p hp e c).1) hxt)
  · exact Or.inr (A.atom_subrows_fixed b k (A.dim b) le_rfl y hy
      (fun p hp e c => (hsub p hp e c).2) hyt)
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M.cylinder)
include A

lemma chainComparison_lowers_dimension (n : ℕ)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (tensorFunctor.obj M.nu).source (n+1) z = z)
    (hzero : ((chainComparison M).map z).row (n+1) false = 0) :
    (tensorFunctor.obj M.nu).source n z = z := by
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have img_bound (z : T.Cell) (hz : T.source (n+1) z = z) :
      truncate (n+1) false (F.map z) = F.map z := by
    change M.cylinder.nu.source (n+1) (F.map z) = F.map z
    rw [← F.map_source,hz]
  apply tensor_bounded_cells_induction (n+1)
    (fun z => (F.map z).row (n+1) false = 0 → T.source n z = z) ?_ ?_ ?_ ?_ z hz hzero
  · intro a x hx he
    apply (chainComparison_endpoint_fiber (T.source n (((tensorEndpoint a).app M.nu).map x)) a x).mp
    rw [F.map_source]
    have hb : T.source (n+1) (((tensorEndpoint a).app M.nu).map x) =
        ((tensorEndpoint a).app M.nu).map x := by
      rw [← ((tensorEndpoint a).app M.nu).map_source]
      exact congrArg ((tensorEndpoint a).app M.nu).map hx
    exact (fixed_of_top_zero (img_bound _ hb) he).trans (chainComparison_endpoint_apply a x)
  · intro r hr x he
    by_cases hrn : r < n
    · exact T.source_fixed_upwards (by omega : r+1 ≤ n) (verticalCell_bounded r x)
    have hrn : r = n := by omega
    subst r
    have he' : x.val.row n false = 0 := by
      change ((chainComparison M).map (verticalCell n x)).row (n+1) false = 0 at he
      rw [chainComparison_verticalCell] at he
      have hh := congrArg (fun t : M.cylinder.Chain (n+1) => t.2.2) he
      change (verticalRow x.val (n+1) false).2.2 = 0 at hh
      simp only [verticalRow] at hh
      split_ifs at hh <;> exact hh
    cases n with
    | zero =>
      have ha := x.val.augmentation false
      rw [he',map_zero] at ha
      exact False.elim (by omega)
    | succ n =>
      exact verticalCell_bounded_of_bounded (n+1) n x (fixed_of_top_zero x.property he')
  · intro r hr y hy _
    exact T.source_fixed_upwards (by omega) hy
  · intro r hr x y hx hy h ihx ihy he
    change (F.map (T.comp r x y h)).row (n+1) false = 0 at he
    rw [F.map_comp r x y h (F.map_composable h)] at he
    change (DirectedComplex.Table.comp r (F.map x) (F.map y) (F.map_composable h)).row (n+1) false = 0 at he
    erw [comp_row] at he
    simp only [show ¬n+1 < r by omega,show n+1 ≠ r by omega,ite_false] at he
    obtain ⟨hxt,hyt⟩ := A.positive_add_zero ((F.map x).positive (n+1) false)
      ((F.map y).positive (n+1) false) he
    have hx' := ihx hxt
    have hy' := ihy hyt
    by_cases hrn : r < n
    · rw [T.source_comp_gt n r hrn x y h (T.source_composable hrn h)]
      exact T.comp_congr_cells r _ _ hx' hy'
    · have hnr : n = r := by omega
      subst r
      rw [T.comp_of_left_source_fixed n x y h hx']
      exact hy'

lemma chainComparison_reflects_dimension (n : ℕ)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : truncate n false ((chainComparison M).map z) = (chainComparison M).map z) :
    (tensorFunctor.obj M.nu).source n z = z := by
  obtain ⟨d,hd⟩ := (tensorFunctor.obj M.nu).finite_dimension z
  induction d generalizing z with
  | zero => exact (tensorFunctor.obj M.nu).source_fixed_upwards (Nat.zero_le n) hd
  | succ d ih =>
    by_cases hdn : d+1 ≤ n
    · exact (tensorFunctor.obj M.nu).source_fixed_upwards hdn hd
    have hzero := row_above_fixed ((chainComparison M).map z) hz (by omega : n < d+1) false
    exact ih z hz (chainComparison_lowers_dimension A d z hd hzero)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma cross_vertical (x : Table M) (p : ℕ) (e : Bool) :
    cross (verticalTable x) p e = x.row p e := by
  change (verticalRow x (p+1) e).2.2 = x.row p e
  simp only [verticalRow]
  split_ifs <;> rfl

lemma vertical_injective : Function.Injective (verticalTable (K := M)) := by
  intro x y h
  apply Table.ext
  funext p e
  exact (cross_vertical x p e).symm.trans
    ((congrArg (fun z => cross z p e) h).trans (cross_vertical y p e))

lemma label_vertical (x : Table M) (e : Bool) :
    label (verticalTable x) e = if e then 1 else 0 := by
  cases e
  · exact M.augmentation.map_zero
  · exact x.augmentation true

lemma vertical_ne_endpoint (x y : Table M) (a : Bool) :
    verticalTable x ≠ (M.cylinderEndpoint a).table y := by
  intro h
  have hs := congrArg (fun z => label z false) h
  have ht := congrArg (fun z => label z true) h
  rw [label_vertical,label_endpoint] at hs ht
  cases a <;> simp_all

end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}} (A : RankedAtoms.{u,v} M.cylinder)
include A

lemma chainComparison_atom_generator (b : A.Index)
    (z : (tensorFunctor.obj M.nu).Cell)
    (hz : (chainComparison M).map z = A.atom b) :
    (∃ (a : Bool) (x : M.nu.Cells (A.dim b)), z = ((tensorEndpoint a).app M.nu).map x.val) ∨
    (∃ r, r+1 = A.dim b ∧ ∃ x : M.nu.Cells r, z = verticalCell r x) := by
  let T := tensorFunctor.obj M.nu
  let F := chainComparison M
  have hb : T.source (A.dim b) z = z :=
    chainComparison_reflects_dimension A (A.dim b) z (hz ▸ A.bounded b)
  apply tensor_bounded_cells_induction (A.dim b)
    (fun z => F.map z = A.atom b →
      (∃ (a : Bool) (x : M.nu.Cells (A.dim b)), z = ((tensorEndpoint a).app M.nu).map x.val) ∨
      (∃ r, r+1 = A.dim b ∧ ∃ x : M.nu.Cells r, z = verticalCell r x)) ?_ ?_ ?_ ?_ z hb hz
  · intro a x hx _
    exact Or.inl ⟨a,⟨x,hx⟩,rfl⟩
  · intro r hr x he
    have hd : A.dim b ≤ r+1 := by
      apply A.atom_dimension_le b
      rw [← he]
      change M.cylinder.nu.source (r+1) (F.map (verticalCell r x)) = _
      rw [← F.map_source]
      exact congrArg F.map (verticalCell_bounded r x)
    exact Or.inr ⟨r,by omega,x,rfl⟩
  · intro r hr x hx he
    have hd : A.dim b ≤ r := by
      apply A.atom_dimension_le b
      rw [← he]
      change M.cylinder.nu.source r (F.map x) = _
      rw [← F.map_source]
      exact congrArg F.map hx
    omega
  · intro r hr x y hx hy h ihx ihy he
    have him : DirectedComplex.Table.comp r (F.map x) (F.map y) (F.map_composable h) = A.atom b :=
      (F.map_comp r x y h (F.map_composable h)).symm.trans he
    rcases A.atom_indecomposable b r (F.map x) (F.map y) (F.map_composable h) him with hf | hf
    · have hx' := chainComparison_reflects_dimension A r x hf
      have hc := T.comp_of_left_source_fixed r x y h hx'
      rw [hc] at he ⊢
      exact ihy he
    · have hy' := chainComparison_reflects_dimension A r y hf
      have hc := T.comp_of_right_source_fixed r x y h hy'
      rw [hc] at he ⊢
      exact ihx he

lemma chainComparison_atom_fiber_subsingleton (b : A.Index)
    (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (chainComparison M).map x = A.atom b)
    (hy : (chainComparison M).map y = A.atom b) : x = y := by
  rcases chainComparison_atom_generator A b x hx with ⟨a,t,rfl⟩ | ⟨r,_,t,rfl⟩
  · exact ((chainComparison_endpoint_fiber y a t.val).mp
      (hy.trans (hx.symm.trans (chainComparison_endpoint_apply a t.val)))).symm
  · rw [chainComparison_verticalCell] at hx
    rcases chainComparison_atom_generator A b y hy with ⟨a,s,rfl⟩ | ⟨q,_,s,rfl⟩
    · erw [chainComparison_endpoint_apply a s.val] at hy
      exact False.elim (CylinderTables.vertical_ne_endpoint t.val s.val a (hx.trans hy.symm))
    · rw [chainComparison_verticalCell] at hy
      exact verticalCell_eq_of_value t s (CylinderTables.vertical_injective (hx.trans hy.symm))

omit A in

lemma chainComparison_atom_unique {N : ℕ} {P : Type u} [LinearOrder P]
    (e : Fin (N+1) ≃o P) (b : (NormalizedChains.Prism.Basis.ofOrderIso e).Index) :
    ∃! x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cells
      ((NormalizedChains.Prism.Basis.ofOrderIso e).dim b),
      (chainComparison (NormalizedChains.complex P)).map x.val =
        (NormalizedChains.Prism.Basis.ofOrderIso e).atom b := by
  obtain ⟨x,hx⟩ := chainComparison_atom_lift e b
  refine ⟨x,hx,?_⟩
  intro y hy
  exact Subtype.ext (chainComparison_atom_fiber_subsingleton
    (NormalizedChains.Prism.Basis.ofOrderIso e) b y.val x.val hy hx)
end Thomason.GrayRecursive.IntervalHom

end

end OAI
