import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.ExceptionalFibers
import OAI.AlgebraicGeometry.NumericalDimension.KltMembers

namespace OAI

/-! Hyperplane Dimension. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_smooth_member_strict_specialization
    {k : Type} [Field k] [CharZero k] [Uncountable k]
    {n : ℕ} {X : Scheme} [NoetherianSpace X]
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) [Smooth (U.ι ≫ sX)]
    (V : X.OpenCover) [∀ i, IsAffine (V.X i)]
    (r : ∀ i, Fin n → Γ(V.X i,⊤)) (hn : ∀ i, ∃ j, r i j = 1)
    (J : 𝔸(Fin n;X).IdealSheafData)
    (hJ : ∀ i, J.comap (AffineSpace.map (Fin n) (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}))
    {ι : Type} [Countable ι] (Z : ι → Set X) (hZ : ∀ j, IsClosed (Z j)) :
    ∃ p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)),
      p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧
      Smooth (((J.comap (parameterSection sX p)).comap U.ι).subschemeι ≫ (U.ι ≫ sX)) ∧
      ∀ j x, x ∈ Z j → x ∈ (J.comap (parameterSection sX p)).support →
        ∃ g ∈ Z j, x < g := by
  classical
  choose G hG using fun j => closed_set_finite_generics (hZ j)
  let T := (j : ι) × ↥(G j)
  choose W hW hWp using fun t : T =>
    incidence_parameter_open_avoiding_point sX V r hn J hJ t.2.1
  have : Smooth (J.subschemeι ≫ 𝔸(Fin n;X) ↘ X) :=
    universal_incidence_smooth_over V r hn J hJ
  obtain ⟨p,hp,hpW,hsm⟩ := exists_very_general_incidence_member_on_open sX U J W hW
  refine ⟨p,hp,hsm,fun j x hx hxI => ?_⟩
  obtain ⟨g,hg,hxg⟩ := (hG j x).mp hx
  have hgI : g ∉ (J.comap (parameterSection sX p)).support :=
    hWp ⟨j,⟨g,hg⟩⟩ p hp (hpW _)
  refine ⟨g,(hG j g).mpr ⟨g,hg,subset_closure (by simp)⟩,
    lt_iff_le_not_ge.mpr ⟨specializes_iff_mem_closure.mpr hxg,?_⟩⟩
  intro h
  exact hgI ((show x ⤳ g from h).mem_closed
    (J.comap (parameterSection sX p)).support.isClosed hxI)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
universe u
lemma universalLinearSection_map {n : Type u} [Fintype n] {Y X : Scheme.{u}}
    (g : Y ⟶ X) (r : n → Γ(X,⊤)) :
    (AffineSpace.map n g).appTop (universalLinearSection r) =
      universalLinearSection (fun j => g.appTop (r j)) := by
  simp only [universalLinearSection,map_sum,map_mul,AffineSpace.map_appTop_coord]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ((𝔸(n;X) ↘ X).appTop ≫ (AffineSpace.map n g).appTop) _ = _
  rw [← Scheme.Hom.comp_appTop,AffineSpace.map_over,Scheme.Hom.comp_appTop]
  rfl

theorem normalized_incidence_baseChange
    {n : Type u} [Fintype n] {X Y : Scheme.{u}} (g : Y ⟶ X) [IsAffineHom g]
    (V : X.OpenCover) [∀ i, IsAffine (V.X i)]
    (r : ∀ i, n → Γ(V.X i,⊤))
    (J : 𝔸(n;X).IdealSheafData)
    (hJ : ∀ i, J.comap (AffineSpace.map n (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)})) :
    let W := V.pullback₁ g
    let r' : ∀ i, n → Γ(W.X i,⊤) := fun i j => (pullback.snd g (V.f i)).appTop (r i j)
    ∀ i, (J.comap (AffineSpace.map n g)).comap (AffineSpace.map n (W.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r' i)}) := by
  dsimp only
  intro i
  change V.I₀ at i
  have h : AffineSpace.map n (pullback.fst g (V.f i)) ≫ AffineSpace.map n g =
      AffineSpace.map n (pullback.snd g (V.f i)) ≫ AffineSpace.map n (V.f i) := by
    rw [← AffineSpace.map_comp,← AffineSpace.map_comp,pullback.condition]
  change (J.comap (AffineSpace.map n g)).comap
    (AffineSpace.map n (pullback.fst g (V.f i))) = _
  rw [← Scheme.IdealSheafData.comap_comp,h,Scheme.IdealSheafData.comap_comp,hJ,
    idealSheaf_comap_ofIdealTop_affine,Ideal.map_span,Set.image_singleton,
    universalLinearSection_map]
  rfl
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section
universe u

theorem smooth_preimage_open_of_comap
    {X B : Scheme.{u}} (sX : X ⟶ B) (U : X.Opens) (I : X.IdealSheafData)
    [Smooth ((I.comap U.ι).subschemeι ≫ U.ι ≫ sX)] :
    Smooth ((I.subschemeι ⁻¹ᵁ U).ι ≫ I.subschemeι ≫ sX) := by
  have h : Smooth (pullback.fst U.ι I.subschemeι ≫ U.ι ≫ sX) := by
    have he : pullback.fst U.ι I.subschemeι ≫ U.ι ≫ sX =
        (I.comapIso U.ι).inv ≫ ((I.comap U.ι).subschemeι ≫ U.ι ≫ sX) := by
      simp only [← Category.assoc,I.comapIso_inv_subschemeι]
    rw [he]
    infer_instance
  have hp := isPullback_morphismRestrict I.subschemeι U
  have he : hp.isoPullback.hom ≫ pullback.fst U.ι I.subschemeι = I.subschemeι ∣_ U :=
    hp.isoPullback_hom_fst
  have hs : Smooth ((I.subschemeι ∣_ U) ≫ U.ι ≫ sX) := by
    rw [← he,Category.assoc]
    infer_instance
  rw [← Category.assoc,morphismRestrict_ι,Category.assoc] at hs
  exact hs
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

inductive IncidenceCutChain {k : Type} [Field k] {n : ℕ} :
    (X : Scheme) → (X ⟶ Spec (.of k)) → 𝔸(Fin n;X).IdealSheafData → ℕ →
      (S : Scheme) → (S ⟶ X) → Prop
  | nil (X : Scheme) (sX : X ⟶ Spec (.of k)) (J : 𝔸(Fin n;X).IdealSheafData) :
      IncidenceCutChain X sX J 0 X (𝟙 X)
  | cons {X : Scheme} (sX : X ⟶ Spec (.of k)) (J : 𝔸(Fin n;X).IdealSheafData)
      (p : Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)))
      (hp : p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _)
      (hproper : ∀ x ∈ (J.comap (parameterSection sX p)).support, ∃ g : X, x < g)
      {r : ℕ} {S : Scheme} (i : S ⟶ (J.comap (parameterSection sX p)).subscheme)
      (h : IncidenceCutChain (J.comap (parameterSection sX p)).subscheme
        ((J.comap (parameterSection sX p)).subschemeι ≫ sX)
        (J.comap (AffineSpace.map (Fin n) (J.comap (parameterSection sX p)).subschemeι)) r S i) :
      IncidenceCutChain X sX J (r+1) S (i ≫ (J.comap (parameterSection sX p)).subschemeι)

lemma IncidenceCutChain.isClosedImmersion
    {k : Type} [Field k] {n r : ℕ} {X S : Scheme}
    {sX : X ⟶ Spec (.of k)} {J : 𝔸(Fin n;X).IdealSheafData} {i : S ⟶ X}
    (h : IncidenceCutChain X sX J r S i) : IsClosedImmersion i := by
  induction h with
  | nil => infer_instance
  | cons sX J p hp hproper i h ih =>
    have := ih
    infer_instance
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology

namespace NumericalDimensionOne
noncomputable section

theorem exists_smooth_complete_intersection_avoiding
    {k : Type} [Field k] [CharZero k] [Uncountable k] {n : ℕ} (d : ℕ) :
    ∀ {X : Scheme} [NoetherianSpace X]
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) [Smooth (U.ι ≫ sX)]
    (V : X.OpenCover) [∀ i, IsAffine (V.X i)]
    (r : ∀ i, Fin n → Γ(V.X i,⊤)) (_ : ∀ i, ∃ j, r i j = 1)
    (J : 𝔸(Fin n;X).IdealSheafData)
    (_ : ∀ i, J.comap (AffineSpace.map (Fin n) (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}))
    {ι : Type} [Countable ι] (Z : ι → Set X) (_ : ∀ j, IsClosed (Z j))
    (_ : ∀ x : X, x ∉ U → Order.height x < d)
    (_ : ∀ j x, x ∈ Z j → Order.height x < d),
    ∃ (S : Scheme) (i : S ⟶ X), IncidenceCutChain X sX J d S i ∧
      Smooth (i ≫ sX) ∧ ∀ j x, i x ∉ Z j := by
  induction d with
  | zero =>
    intro X _ sX U _ V _ r hn J hJ ι _ Z hZ hdU hdZ
    have hU : U = ⊤ := by
      apply top_unique
      intro x _
      by_contra hx
      exact (not_lt_of_ge bot_le) (hdU x hx)
    have hs : Smooth sX := by
      have hst : Smooth ((⊤ : X.Opens).ι ≫ sX) := by rw [← hU]; infer_instance
      have he : sX = X.topIso.inv ≫ ((⊤ : X.Opens).ι ≫ sX) := by simp
      rw [he]
      infer_instance
    refine ⟨X,𝟙 X,.nil X sX J,?_,?_⟩
    · simpa using hs
    · intro j x hx
      exact (not_lt_of_ge bot_le) (hdZ j x hx)
  | succ d ih =>
    intro X _ sX U _ V _ r hn J hJ ι _ Z hZ hdU hdZ
    let T : Option (Option ι) → Set X := fun a => a.elim Set.univ (fun b => b.elim ((U : Set X)ᶜ) Z)
    have hT : ∀ a, IsClosed (T a) := by
      intro a
      rcases a with _ | a
      · exact isClosed_univ
      rcases a with _ | a
      · exact U.isOpen.isClosed_compl
      · exact hZ a
    obtain ⟨p,hp,hsm,hstrict⟩ := exists_smooth_member_strict_specialization sX U V r hn J hJ T hT
    let I := J.comap (parameterSection sX p)
    let Y := I.subscheme
    let sY := I.subschemeι ≫ sX
    let UY := I.subschemeι ⁻¹ᵁ U
    have : NoetherianSpace Y := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
    have hc : Smooth ((I.comap U.ι).subschemeι ≫ U.ι ≫ sX) := hsm
    have : Smooth (UY.ι ≫ sY) := smooth_preimage_open_of_comap sX U I
    let W := V.pullback₁ I.subschemeι
    have : ∀ a, IsAffine (W.X a) := by
      intro a
      change V.I₀ at a
      exact inferInstanceAs (IsAffine (pullback I.subschemeι (V.f a)))
    let r' : ∀ a, Fin n → Γ(W.X a,⊤) := fun a j => (pullback.snd I.subschemeι (V.f a)).appTop (r a j)
    have hn' : ∀ a, ∃ j, r' a j = 1 := by
      intro a
      change V.I₀ at a
      obtain ⟨j,hj⟩ := hn a
      refine ⟨j,?_⟩
      change (pullback.snd I.subschemeι (V.f a)).appTop (r a j) = 1
      rw [hj]
      exact map_one _
    let JY := J.comap (AffineSpace.map (Fin n) I.subschemeι)
    have hJY : ∀ a, JY.comap (AffineSpace.map (Fin n) (W.f a)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r' a)}) :=
      normalized_incidence_baseChange I.subschemeι V r J hJ
    let ZY : ι → Set Y := fun j => I.subschemeι ⁻¹' Z j
    have hZY : ∀ j, IsClosed (ZY j) := fun j => (hZ j).preimage I.subschemeι.continuous
    have hyI (y : Y) : I.subschemeι y ∈ I.support := by
      change I.subschemeι y ∈ (I.support : Set X)
      rw [← I.range_subschemeι]
      exact Set.mem_range_self y
    have hbound (a : Option ι) (y : Y) (hy : I.subschemeι y ∈ T (some a)) :
        Order.height y < d := by
      obtain ⟨g,hg,hyg⟩ := hstrict (some a) (I.subschemeι y) hy (hyI y)
      have hdg : Order.height g < (d+1 : ℕ) := by
        rcases a with _ | a
        · exact hdU g hg
        · exact hdZ a g hg
      have hdg' : Order.height g ≤ d := by
        exact ENat.lt_natCast_add_one_iff.mp (by simpa only [Nat.cast_add,Nat.cast_one] using hdg)
      rw [height_eq_of_closedImmersion I.subschemeι]
      exact (Order.height_le_coe_iff.mp hdg') _ hyg
    have hdUY : ∀ y : Y, y ∉ UY → Order.height y < d := fun y hy => hbound none y hy
    have hdZY : ∀ j y, y ∈ ZY j → Order.height y < d := fun j y hy => hbound (some j) y hy
    obtain ⟨S,i,hi,hs,ha⟩ := ih sY UY W r' hn' JY hJY ZY hZY hdUY hdZY
    have hproper : ∀ x ∈ I.support, ∃ g : X, x < g := by
      intro x hx
      obtain ⟨g,_,hxg⟩ := hstrict none x (Set.mem_univ x) hx
      exact ⟨g,hxg⟩
    refine ⟨S,i ≫ I.subschemeι,.cons sX J p hp hproper i hi,?_,?_⟩
    · simpa only [Category.assoc] using hs
    · intro j x
      exact ha j x
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
noncomputable section
attribute [-instance] Subtype.instLE Subtype.instLT Subtype.preorder Subtype.partialOrder in

theorem height_le_closed_topologicalKrullDim {X : Scheme} {Z : Set X}
    (hZ : IsClosed Z) (x : Z) :
    (Order.height (x : X) : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  let : PartialOrder Z := specializationOrder Z
  have : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hle (a b : Z) : (a : X) ≤ (b : X) ↔ a ≤ b :=
by
    change ((b : X) ⤳ (a : X)) ↔ b ⤳ a
    exact Topology.IsInducing.subtypeVal.specializes_iff
  have hlt (a b : Z) : (a : X) < (b : X) ↔ a < b := by
    simp only [lt_iff_le_not_ge,hle]
  have hh : Order.height x = Order.height (x : X) := by
    apply Order.height_eq_of_strictMono (Subtype.val : Z → X) (fun a b h => (hlt a b).mpr h)
    intro a b h
    have hb : b ∈ Z := (show (a : X) ⤳ b from h.le).mem_closed hZ a.2
    exact ⟨⟨b,hb⟩,(hlt ⟨b,hb⟩ a).mp h,rfl⟩
  have h := Order.height_le_krullDim ((irreducibleSetEquivPoints (α := Z)).symm x)
  rw [Order.height_orderIso,hh] at h
  exact h

lemma height_lt_of_closed_dim_lt {X : Scheme} {Z : Set X}
    (hZ : IsClosed Z) {d : ℕ} (hd : topologicalKrullDim Z < d) :
    ∀ x ∈ Z, Order.height x < d := by
  intro x hx
  have h := (height_le_closed_topologicalKrullDim hZ ⟨x,hx⟩).trans_lt hd
  exact_mod_cast h
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
noncomputable section

theorem exists_generated_complete_intersection_avoiding
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    [CompactSpace X] (sX : X ⟶ Spec (.of ℂ)) (U : X.Opens)
    [Smooth (U.ι ≫ sX)] {N : ℕ} (d : ℕ) (D : WeilDivisor X)
    (hD : IsCartierDivisor D) (s : Fin (N+1) → X.functionField)
    (hs : ∀ j, s j ≠ 0 ∧ IsDivisorSection D (s j))
    (hgen : ∀ x : X, ∃ j, x ∈ sectionNonvanishing D (s j))
    {ι : Type} [Countable ι] (Z : ι → Set X) (hZ : ∀ j, IsClosed (Z j))
    (hdU : topologicalKrullDim ↥((U : Set X)ᶜ) < d)
    (hdZ : ∀ j, topologicalKrullDim (Z j) < d) :
    ∃ (A : DivisorAffineAtlas X D s) (J : 𝔸(Fin (N+1);X).IdealSheafData)
      (S : Scheme) (i : S ⟶ X),
      (∀ a, J.comap (AffineSpace.map _ (A.cover.f a)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate a)})) ∧
      IncidenceCutChain X sX J d S i ∧ Smooth (i ≫ sX) ∧
      Set.range i ⊆ U ∧ ∀ j x, i x ∉ Z j := by
  classical
  have : IsNoetherian X := ⟨⟩
  have : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum)
  obtain ⟨A⟩ := exists_divisorAffineAtlas hD hs hgen
  obtain ⟨J,hJ⟩ := A.incidence_exists (fun j => (hs j).1)
  let T : Option ι → Set X := fun a => a.elim ((U : Set X)ᶜ) Z
  have hT : ∀ a, IsClosed (T a) := by
    intro a
    rcases a with _ | a
    · exact U.isOpen.isClosed_compl
    · exact hZ a
  have hdT : ∀ a x, x ∈ T a → Order.height x < d := by
    intro a
    rcases a with _ | a
    · exact height_lt_of_closed_dim_lt U.isOpen.isClosed_compl hdU
    · exact height_lt_of_closed_dim_lt (hZ a) (hdZ a)
  obtain ⟨S,i,hchain,hsm,ha⟩ := exists_smooth_complete_intersection_avoiding d sX U
    A.cover A.coordinate
    (fun a => ⟨(A.chart a).unit_index,by simp [DivisorAffineAtlas.coordinate,
      DivisorProjectiveChart.normalized_index]; rfl⟩) J hJ T hT
    (height_lt_of_closed_dim_lt U.isOpen.isClosed_compl hdU) hdT
  refine ⟨A,J,S,i,hJ,hchain,hsm,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact Classical.not_not.mp (ha none x)
  · intro j
    exact ha (some j)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
universe u

theorem ideal_map_comap_closedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (J : Y.IdealSheafData) :
    (J.comap f).map f = J ⊔ f.ker := by
  let K := J ⊔ f.ker
  let g := IsClosedImmersion.lift f K.subschemeι (by
    rw [K.ker_subschemeι]
    exact le_sup_right)
  have hg : g ≫ f = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hk : g.ker.map f = K := by
    rw [← Scheme.Hom.ker_comp,hg,K.ker_subschemeι]
  apply le_antisymm
  · have hj : J ≤ g.ker.map f := by rw [hk]; exact le_sup_left
    have h := Scheme.IdealSheafData.map_mono f
      (Scheme.IdealSheafData.le_map_iff_comap_le.mp hj)
    exact h.trans_eq hk
  · apply sup_le
    · exact Scheme.IdealSheafData.le_map_comap _ _
    · simpa only [Scheme.IdealSheafData.map_bot] using
        (Scheme.IdealSheafData.map_mono f (show ⊥ ≤ J.comap f from bot_le))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
noncomputable section
universe u

def incidenceIntersectionIdeal {n : Type u} {X B : Scheme.{u}}
    (sX : X ⟶ B) (J : 𝔸(n;X).IdealSheafData) :
    List (B ⟶ 𝔸(n;B)) → X.IdealSheafData
  | [] => ⊥
  | p::ps => J.comap (parameterSection sX p) ⊔ incidenceIntersectionIdeal sX J ps
lemma incidenceIntersectionIdeal_comap {n : Type u} {X Y B : Scheme.{u}}
    (f : Y ⟶ X) (sX : X ⟶ B) (J : 𝔸(n;X).IdealSheafData)
    (ps : List (B ⟶ 𝔸(n;B))) :
    (incidenceIntersectionIdeal sX J ps).comap f =
      incidenceIntersectionIdeal (f ≫ sX) (J.comap (AffineSpace.map n f)) ps := by
  induction ps with
  | nil => simp [incidenceIntersectionIdeal]
  | cons p ps ih =>
    simp only [incidenceIntersectionIdeal,Scheme.IdealSheafData.comap_sup,ih]
    congr 1
    rw [← Scheme.IdealSheafData.comap_comp,parameterSection_naturality,
      Scheme.IdealSheafData.comap_comp]

theorem IncidenceCutChain.exists_parameters
    {k : Type} [Field k] {n r : ℕ} {X S : Scheme}
    {sX : X ⟶ Spec (.of k)} {J : 𝔸(Fin n;X).IdealSheafData} {i : S ⟶ X}
    (h : IncidenceCutChain X sX J r S i) :
    ∃ ps : List (Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k))), ps.length = r ∧
      (∀ p ∈ ps, p ≫ 𝔸(Fin n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) ∧
      i.ker = incidenceIntersectionIdeal sX J ps := by
  induction h with
  | nil X sX J =>
    exact ⟨[],rfl,by simp,by simp [incidenceIntersectionIdeal]⟩
  | cons sX J p hp hproper i h ih =>
    obtain ⟨ps,hps,hh,he⟩ := ih
    refine ⟨p::ps,by simp [hps],?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hh q hq
    · rw [Scheme.Hom.ker_comp,he,← incidenceIntersectionIdeal_comap,
        ideal_map_comap_closedImmersion,Scheme.IdealSheafData.ker_subschemeι]
      exact sup_comm _ _
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
universe u

theorem isIso_pullback_snd_of_range_subset_isoLocus
    {X Y S : Scheme.{u}} (π : Y ⟶ X) (i : S ⟶ X) (U : X.Opens)
    [IsIso (π ∣_ U)] (hi : Set.range i ⊆ U) :
    IsIso (pullback.snd π i) := by
  let j := IsOpenImmersion.lift U.ι i (by simpa using hi)
  have hj : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  have h : IsPullback (pullback.fst π i) (pullback.snd π i) π (j ≫ U.ι) := by
    rw [hj]
    exact IsPullback.of_hasPullback π i
  exact (h.of_right' (isPullback_morphismRestrict π U).flip).isIso_snd_of_isIso
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem finiteType_maximal_height (k R : Type*) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (p : Ideal R) [p.IsMaximal] : (p.height : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨n,g,hg,hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let B := MvPolynomial (Fin n) k
  let : Algebra B R := g.toRingHom.toAlgebra
  have : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr hg
  have : Module.Finite B R := hfin
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let q := p.under B
  have : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap B R) (Algebra.IsIntegral.isIntegral) p
  have : p.LiesOver q := ⟨rfl⟩
  have hlow : (n : ℕ∞) ≤ p.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p]
    have he : q.height = n := polynomial_maximal_height k n q
    rw [he]
    exact le_self_add
  have hd : ringKrullDim R = n := by
    rw [ringKrullDim_eq_of_integral_faithful B R]
    simp [B]
  apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : p.IsMaximal).ne_top)
  rw [hd]
  exact_mod_cast hlow
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]

private theorem affine_dimension_of_functionField (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (n : ℕ)
    (ht : let := schemeFieldAlgebra (.of k) sX; Algebra.trdeg k X.functionField = n)
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) : ringKrullDim Γ(X,U) = n := by
  let := schemeFieldAlgebra (.of k) sX
  let := schemeOpenAlgebra sX U
  have : Algebra.FiniteType k Γ(X,U) :=
    (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  obtain ⟨m,hm,hmt⟩ := finiteType_dimension_trdeg k Γ(X,U)
  have hmn : m = n := by
    exact_mod_cast hmt.symm.trans ((affine_functionField_trdeg k sX U hU).trans ht)
  simpa only [hmn] using hm

omit [IsIntegral X] in
private theorem affine_prime_coheight (U : X.Opens) (hU : IsAffineOpen U) (y : U) :
    (hU.primeIdealOf y).asIdeal.height = Order.coheight (y : X) := by
  let P : Spec Γ(X,U) := hU.primeIdealOf y
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  calc
    P.asIdeal.height = Order.coheight P := idealHeight_eq_coheight Γ(X,U) P
    _ = Order.coheight (hU.fromSpec P) :=
      (coheight_eq_of_isOpenImmersion hU.fromSpec).symm
    _ = Order.coheight (y : X) := congrArg Order.coheight (hU.fromSpec_primeIdealOf y)

private theorem affine_closed_point_height (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (y : U) (hclosed : IsClosed {(y : X)}) :
    ((hU.primeIdealOf y).asIdeal.height : WithBot ℕ∞) = ringKrullDim Γ(X,U) := by
  let := schemeOpenAlgebra sX U
  have : Algebra.FiniteType k Γ(X,U) :=
    (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  have : (hU.primeIdealOf y).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed y hclosed
  exact finiteType_maximal_height k Γ(X,U) (hU.primeIdealOf y).asIdeal

theorem scheme_dimension_of_functionField (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (n : ℕ)
    (ht : let := schemeFieldAlgebra (.of k) sX; Algebra.trdeg k X.functionField = n) :
    (∀ x : X, Order.coheight x ≤ n) ∧
    (∀ x : X, IsClosed {x} → Order.coheight x = n) ∧
    (∀ x : X, Order.height x ≤ n) := by
  let := schemeFieldAlgebra (.of k) sX
  have hlocal (x : X) : Order.coheight x ≤ n ∧
      (IsClosed {x} → Order.coheight x = n) := by
    obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    have : Nonempty U := ⟨⟨x,hx⟩⟩
    let := schemeOpenAlgebra sX U
    have hr : ringKrullDim Γ(X,U) = n :=
      affine_dimension_of_functionField k sX n ht U hU
    let y : U := ⟨x,hx⟩
    let P : Spec Γ(X,U) := hU.primeIdealOf y
    have he : P.asIdeal.height = Order.coheight x := affine_prime_coheight U hU y
    constructor
    · have hb := Ideal.height_le_ringKrullDim_of_ne_top P.isPrime.ne_top
      rw [hr,he] at hb
      exact WithBot.coe_le_coe.mp hb
    · intro hxc
      have hm := affine_closed_point_height k sX U hU y hxc
      rw [hr,he] at hm
      exact WithBot.coe_eq_coe.mp hm
  have hco (x : X) : Order.coheight x ≤ n := (hlocal x).1
  refine ⟨hco,fun x => (hlocal x).2,?_⟩
  intro x
  apply Order.height_le
  intro l _
  exact Order.length_le_coheight_head.trans (hco l.head)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
noncomputable def projectiveLinearPolynomial {N : ℕ} (a : Fin (N+1) → ℂ) :
    MvPolynomial (Fin (N+1)) ℂ := ∑ i, a i • MvPolynomial.X i
lemma projectiveLinearPolynomial_homogeneous {N : ℕ} (a : Fin (N+1) → ℂ) :
    (projectiveLinearPolynomial a).IsHomogeneous 1 := by
  change (∑ i, a i • MvPolynomial.X i) ∈
    MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ 1
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (MvPolynomial.isHomogeneous_X ℂ i)

end NumericalDimensionOne

end OAI
