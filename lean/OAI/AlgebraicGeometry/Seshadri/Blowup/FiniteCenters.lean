import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.PowerContraction

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

lemma comap_mul_open {Y : Scheme.{0}} (I J : X.IdealSheafData)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (I * J).comap f = I.comap f * J.comap f := by
  ext U : 2
  let V : X.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := fun x hx => ⟨x, hx, rfl⟩
  rw [IdealPullback.comap_ideal _ f U V e]
  change ((I.ideal V) * (J.ideal V)).map _ = _
  rw [Ideal.map_mul]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    IdealPullback.comap_ideal _ f U V e]

lemma comap_prod_open {Y : Scheme.{0}} {α : Type} (s : Finset α)
    (I : α → X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f] :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, comap_mul_open, ih]

lemma comap_eq_top_of_disjoint (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (I.support : Set X) U) : I.comap U.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change x.val ∈ I.support ↔ False
  exact iff_false_intro (fun hx => Set.disjoint_left.mp h hx x.property)

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

def pointCentre : X.IdealSheafData := ∏ i, (p i).ker

def pointOpen (i : α) : X.Opens :=
  (⨆ j : {j : α // j ≠ i}, (p j).ker.support).compl

def outsideOpen : X.Opens := (pointCentre p).support.compl

omit [Fintype α] in
lemma pointOpen_comap_other (i j : α) (hji : j ≠ i) :
    (p j).ker.comap (pointOpen p i).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hx hxU
  exact hxU (show x ∈ (⨆ j : {j : α // j ≠ i}, (p j).ker.support) from
    (le_iSup (fun j : {j : α // j ≠ i} => (p j).ker.support) ⟨j, hji⟩) hx)

lemma pointOpen_comap_centre (i : α) :
    (pointCentre p).comap (pointOpen p i).ι = (p i).ker.comap (pointOpen p i).ι := by
  classical
  rw [pointCentre, comap_prod_open]
  exact Finset.prod_eq_single i (fun j _ hji => by
    simpa only [Scheme.IdealSheafData.one_eq_top] using pointOpen_comap_other p i j hji)
    (by simp)

lemma outside_comap_centre : (pointCentre p).comap (outsideOpen p).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  exact disjoint_compl_right

lemma mem_finite_iSup_closed {β : Type} [Finite β] (C : β → Closeds X) (x : X) :
    x ∈ (⨆ i, C i) ↔ ∃ i, x ∈ C i := by
  let D : Closeds X := ⟨⋃ i, (C i : Set X), isClosed_iUnion_of_finite fun i => (C i).isClosed⟩
  have he : (⨆ i, C i) = D := by
    apply le_antisymm
    · exact iSup_le (fun i y hy => Set.mem_iUnion.mpr ⟨i, hy⟩)
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact (le_iSup C i) hi
  rw [he]
  exact Set.mem_iUnion

lemma mem_pointOpen (i : α) (x : X) :
    x ∈ pointOpen p i ↔ ∀ j, j ≠ i → x ∉ (p j).ker.support := by
  change (¬ x ∈ (⨆ j : {j : α // j ≠ i}, (p j).ker.support)) ↔ _
  rw [mem_finite_iSup_closed]
  simp

lemma mem_centre_support (x : X) :
    x ∈ (pointCentre p).support ↔ ∃ i, x ∈ (p i).ker.support := by
  classical
  suffices h : ∀ s : Finset α, x ∈ (∏ i ∈ s, (p i).ker).support ↔
      ∃ i ∈ s, x ∈ (p i).ker.support by
    simpa only [Finset.mem_univ, true_and, pointCentre] using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    change False ↔ ∃ i ∈ (∅ : Finset α), x ∈ (p i).ker.support
    simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul]
    change (x ∈ (p a).ker.support ∨ x ∈ (∏ i ∈ s, (p i).ker).support) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨i, hi, hx⟩)
      · exact ⟨a, Finset.mem_insert_self .., h⟩
      · exact ⟨i, Finset.mem_insert_of_mem hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi, hx⟩

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp
omit [Fintype α] in
lemma point_support (i : α) : ((p i).ker.support : Set X) =
    {p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))} := by
  let : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
  rw [Scheme.Hom.support_ker, (p i).isClosedEmbedding.isClosed_range.closure_eq]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact congrArg (p i) (Subsingleton.elim _ _)
  · rintro rfl
    exact ⟨_, rfl⟩

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd
lemma point_mem_own_open (i : α) (z : Spec (.of K)) : p i z ∈ pointOpen p i := by
  rw [mem_pointOpen]
  intro j hji
  change p i z ∉ ((p j).ker.support : Set X)
  rw [point_support p f hp j]
  intro h
  apply hji
  apply hd
  exact (show p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K)) = p j _ from
    (congrArg (p i) (Subsingleton.elim _ z)).trans h).symm

def pointCover : X.OpenCover :=
  .mkOfCovers (Option α)
    (fun i => (i.elim (outsideOpen p) (pointOpen p)).toScheme)
    (fun i => (i.elim (outsideOpen p) (pointOpen p)).ι)
    (by
      intro x
      by_cases hx : x ∈ (pointCentre p).support
      · obtain ⟨i, hi⟩ := (mem_centre_support p x).mp hx
        change x ∈ ((p i).ker.support : Set X) at hi
        rw [point_support p f hp i] at hi
        subst x
        exact ⟨some i, ⟨_, point_mem_own_open p f hp hd i _⟩, rfl⟩
      · exact ⟨none, ⟨x, hx⟩, rfl⟩)
    (by intro i; exact inferInstance)

theorem smooth_finite_point_blowup [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) :
    SmoothOfRelativeDimension 2 (π ≫ f) := by
  let C := pointCover p f hp hd
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (C.pullback₁ π)
  change ∀ a : Option α, SmoothOfRelativeDimension 2
    (pullback.fst π (C.f a) ≫ π ≫ f)
  intro a
  cases a with
  | none =>
    change SmoothOfRelativeDimension 2
      (pullback.fst π (outsideOpen p).ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    have : IsIso (pullback.fst (outsideOpen p).ι π) := hπ.isIso_over_complement
    have : IsIso (pullback.snd π (outsideOpen p).ι) := by
      rw [← pullbackSymmetry_hom_comp_fst π (outsideOpen p).ι]
      infer_instance
    have : SmoothOfRelativeDimension 2 ((outsideOpen p).ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  | some i =>
    let U := pointOpen p i
    have hps : Set.range (p i) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, point_mem_own_open p f hp hd i z⟩, rfl⟩
    let l := IsOpenImmersion.lift U.ι (p i) hps
    have hlj : l ≫ U.ι = p i := IsOpenImmersion.lift_fac U.ι (p i) hps
    have hl : l ≫ (U.ι ≫ f) = 𝟙 _ := by rw [← Category.assoc, hlj, hp]
    have : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
    have hker : (p i).ker.comap U.ι = l.ker := by
      have sq := IsOpenImmersion.isPullback_lift_id (p i) U.ι hps
      rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (p i) U.ι,
        ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
        sq.isoPullback_hom_fst]
    have : SmoothOfRelativeDimension 2 (U.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    have hs : SmoothOfRelativeDimension 2 (pullback.fst U.ι π ≫ U.ι ≫ f) := by
      apply PointBlowup.smooth_rational_point_blowup (U.ι ≫ f) l hl
      have he : (pointCentre p).comap U.ι = l.ker :=
        (pointOpen_comap_centre p i).trans hker
      simpa only [he] using hπ.open_baseChange U.ι
    change SmoothOfRelativeDimension 2 (pullback.fst π U.ι ≫ π ≫ f)
    rw [← Category.assoc, pullback.condition, Category.assoc,
      ← pullbackSymmetry_hom_comp_fst π U.ι, Category.assoc]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

theorem exceptional_invertible (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (i : α) :
    InvertiblePullbackIdeal (p i).ker π := by
  let C := pointCover p f hp hd
  apply InvertibleLocal.invertible_of_cover (p i).ker π (C.pullback₁ π)
  change ∀ a : Option α, InvertiblePullbackIdeal (p i).ker
    (pullback.fst π (C.f a) ≫ π)
  intro a
  have : IsOpenImmersion (C.f a) := C.map_prop a
  have hInv : InvertiblePullbackIdeal (pointCentre p) (pullback.fst π (C.f a) ≫ π) :=
    InvertibleLocal.invertible_restrict_general _ π hπ.1 (pullback.fst π (C.f a))
  cases a with
  | none =>
    change InvertiblePullbackIdeal (p i).ker (pullback.fst π (outsideOpen p).ι ≫ π)
    have he : (p i).ker.comap (outsideOpen p).ι = ⊤ := by
      apply comap_eq_top_of_disjoint
      apply Set.disjoint_left.mpr
      intro x hx hxU
      exact hxU ((mem_centre_support p x).mpr ⟨i, hx⟩)
    apply (InvertibleLocal.invertible_congr (I' := ⊤)
      (f' := pullback.fst π (outsideOpen p).ι ≫ π) ?_).mpr
      (invertible_top _)
    rw [pullback.condition, Scheme.IdealSheafData.comap_comp, he]
    simp
  | some j =>
    change InvertiblePullbackIdeal (p i).ker (pullback.fst π (pointOpen p j).ι ≫ π)
    by_cases hij : i = j
    · subst j
      apply (InvertibleLocal.invertible_congr (I' := pointCentre p)
        (f' := pullback.fst π (pointOpen p i).ι ≫ π) ?_).mpr hInv
      rw [pullback.condition, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp, pointOpen_comap_centre]
    · apply (InvertibleLocal.invertible_congr (I' := ⊤)
        (f' := pullback.fst π (pointOpen p j).ι ≫ π) ?_).mpr
        (invertible_top _)
      rw [pullback.condition, Scheme.IdealSheafData.comap_comp,
        pointOpen_comap_other p j i hij]
      simp

end
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd

theorem finite_point_power_contraction [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : ℕ) :
    (((pointCentre p).comap π)^m).map π = (pointCentre p)^m := by
  let C := pointCover p f hp hd
  apply IdealPullback.power_contraction_of_openCover (pointCentre p) π C m
  intro a
  cases a with
  | none =>
    change ((((pointCentre p).comap (outsideOpen p).ι).comap
      (pullback.fst (outsideOpen p).ι π))^m).map (pullback.fst (outsideOpen p).ι π) =
      ((pointCentre p).comap (outsideOpen p).ι)^m
    rw [outside_comap_centre, Scheme.IdealSheafData.comap_top]
    simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]
    exact Scheme.IdealSheafData.map_top (pullback.fst (outsideOpen p).ι π)
  | some i =>
    let U := pointOpen p i
    have hps : Set.range (p i) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, point_mem_own_open p f hp hd i z⟩, rfl⟩
    let l := IsOpenImmersion.lift U.ι (p i) hps
    have hlj : l ≫ U.ι = p i := IsOpenImmersion.lift_fac U.ι (p i) hps
    have hl : l ≫ (U.ι ≫ f) = 𝟙 _ := by rw [← Category.assoc, hlj, hp]
    have : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
    have hker : (p i).ker.comap U.ι = l.ker := by
      have sq := IsOpenImmersion.isPullback_lift_id (p i) U.ι hps
      rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (p i) U.ι,
        ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
        sq.isoPullback_hom_fst]
    have he : (pointCentre p).comap U.ι = l.ker :=
      (pointOpen_comap_centre p i).trans hker
    have : SmoothOfRelativeDimension 2 (U.ι ≫ f) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    change ((((pointCentre p).comap U.ι).comap (pullback.fst U.ι π))^m).map
      (pullback.fst U.ι π) = ((pointCentre p).comap U.ι)^m
    rw [he]
    exact PointBlowup.rational_point_power_contraction (U.ι ≫ f) l hl _
      (by simpa only [he] using hπ.open_baseChange U.ι) m

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd in
omit [Fintype α] in
lemma point_ideals_sup (i j : α) (hij : i ≠ j) : (p i).ker ⊔ (p j).ker = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_sup]
  ext x
  change (x ∈ ((p i).ker.support : Set X) ∧ x ∈ ((p j).ker.support : Set X)) ↔ False
  rw [point_support p f hp i, point_support p f hp j]
  exact iff_false_intro (fun h => hij (hd (h.1.symm.trans h.2)))

def idealEvaluation (U : X.affineOpens) : X.IdealSheafData →* Ideal Γ(X, U.1) where
  toFun I := I.ideal U
  map_one' := by simp only [Scheme.IdealSheafData.one_eq_top,
    Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.one_eq_top]
  map_mul' _ _ := rfl

include hp hd in

theorem point_powers_prod_eq_inf (m : α → ℕ) :
    (∏ i, (p i).ker ^ m i) = ⨅ i, (p i).ker ^ m i := by
  classical
  ext U : 2
  change idealEvaluation U (∏ i, (p i).ker ^ m i) = _
  rw [map_prod]
  change (∏ i, ((p i).ker^m i).ideal U) = (⨅ i, (p i).ker^m i).ideal U
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  apply (Ideal.prod_eq_iInf_of_pairwise_isCoprime ?_).trans (by simp)
  intro i _ j _ hij
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.pow_sup_pow_eq_top
  exact congrArg (fun I : X.IdealSheafData => I.ideal U) (point_ideals_sup p f hp hd i j hij)

include hp hd in
theorem point_centre_power_eq_inf (m : ℕ) :
    (pointCentre p)^m = ⨅ i, (p i).ker^m := by
  rw [pointCentre, ← Finset.prod_pow]
  exact point_powers_prod_eq_inf p f hp hd (fun _ => m)

end
end MaximalSeshadri.FinitePointBlowup
namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_mul (I J : X.IdealSheafData) (f : Y ⟶ X) :
    (I*J).comap f = (I.comap f)*(J.comap f) := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I*J) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)*J.ideal (V y)).map _ =
      ((I.comap f).ideal (U y))*((J.comap f).ideal (U y))
    rw [Ideal.map_mul, comap_ideal I f (U y) (V y) (hUV y),
      comap_ideal J f (U y) (V y) (hUV y)]

lemma comap_prod {α : Type*} (s : Finset α) (I : α → X.IdealSheafData) (f : Y ⟶ X) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.prod_insert ha, comap_mul, ih]

end
end MaximalSeshadri.IdealPullback
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

lemma pointOpen_comap_weighted (m : α → ℕ) (i : α) :
    (∏ j, (p j).ker ^ m j).comap (pointOpen p i).ι =
      ((p i).ker.comap (pointOpen p i).ι) ^ m i := by
  classical
  rw [comap_prod_open]
  simp only [IdealPullback.comap_pow]
  apply Finset.prod_eq_single i
  · intro j _ hji
    rw [pointOpen_comap_other p i j hji]
    exact one_pow _
  · simp

lemma outside_comap_point (i : α) : (p i).ker.comap (outsideOpen p).ι = ⊤ := by
  apply comap_eq_top_of_disjoint
  apply Set.disjoint_left.mpr
  intro x hxi hxo
  exact hxo ((mem_centre_support p x).mpr ⟨i, hxi⟩)

lemma outside_comap_weighted (m : α → ℕ) :
    (∏ i, (p i).ker ^ m i).comap (outsideOpen p).ι = ⊤ := by
  rw [comap_prod_open]
  simp only [IdealPullback.comap_pow, outside_comap_point,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, Finset.prod_const_one]

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd in

theorem weighted_power_contraction [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : α → ℕ) :
    (∏ i, ((p i).ker.comap π) ^ m i).map π = ⨅ i, (p i).ker ^ m i := by
  classical
  let I : X.IdealSheafData := ∏ i, (p i).ker ^ m i
  have hI : (I.comap π).map π = I := by
    let C := pointCover p f hp hd
    suffices hh : ((I.comap π)^1).map π = I^1 by simpa only [pow_one] using hh
    apply IdealPullback.power_contraction_of_openCover I π C 1
    dsimp only [C, pointCover]
    intro a
    cases a with
    | none =>
      suffices hh : (((I.comap (outsideOpen p).ι).comap
        (pullback.fst (outsideOpen p).ι π))^1).map (pullback.fst (outsideOpen p).ι π) =
          (I.comap (outsideOpen p).ι)^1 by exact hh
      rw [pow_one, pow_one, show I.comap (outsideOpen p).ι = ⊤ from
        outside_comap_weighted p m, Scheme.IdealSheafData.comap_top]
      exact Scheme.IdealSheafData.map_top (pullback.fst (outsideOpen p).ι π)
    | some i =>
      let U := pointOpen p i
      have hps : Set.range (p i) ⊆ Set.range U.ι := by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨_, point_mem_own_open p f hp hd i z⟩, rfl⟩
      let l := IsOpenImmersion.lift U.ι (p i) hps
      have hlj : l ≫ U.ι = p i := IsOpenImmersion.lift_fac U.ι (p i) hps
      have hl : l ≫ (U.ι ≫ f) = 𝟙 _ := by rw [← Category.assoc, hlj, hp]
      have : IsClosedImmersion (p i) := isClosedImmersion_of_comp_eq_id f (p i) (hp i)
      have hker : (p i).ker.comap U.ι = l.ker := by
        have sq := IsOpenImmersion.isPullback_lift_id (p i) U.ι hps
        rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (p i) U.ι,
          ← Scheme.Hom.ker_comp_of_isIso sq.isoPullback.hom,
          sq.isoPullback_hom_fst]
      have he : (pointCentre p).comap U.ι = l.ker :=
        (pointOpen_comap_centre p i).trans hker
      have : SmoothOfRelativeDimension 2 (U.ι ≫ f) :=
        inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
      suffices hh : (((I.comap U.ι).comap (pullback.fst U.ι π))^1).map
        (pullback.fst U.ι π) = (I.comap U.ι)^1 by exact hh
      rw [pow_one, pow_one, show I.comap U.ι = (l.ker)^m i from
        (pointOpen_comap_weighted p m i).trans (congrArg (fun J => J^m i) hker),
        IdealPullback.comap_pow]
      exact PointBlowup.rational_point_power_contraction (U.ι ≫ f) l hl _
        (by simpa only [he] using hπ.open_baseChange U.ι) (m i)
  have he : I.comap π = ∏ i, ((p i).ker.comap π)^m i := by
    rw [show I = ∏ i, (p i).ker^m i from rfl, IdealPullback.comap_prod]
    simp only [IdealPullback.comap_pow]
  rw [← he, hI]
  exact point_powers_prod_eq_inf p f hp hd m

end
end MaximalSeshadri.FinitePointBlowup

end



end OAI
