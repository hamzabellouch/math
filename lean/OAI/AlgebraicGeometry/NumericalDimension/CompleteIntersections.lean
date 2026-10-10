import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.HyperplaneDimension

namespace OAI

/-! Complete Intersections. -/

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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_hyperplane_local_equations {X : Scheme} {N : ℕ}
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f] (p : X)
    {ι : Type*} (A : ι → Fin (N+1) → ℂ) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), p ∈ U ∧
      ∃ a : ι → Γ(X,U), ∀ i (q : U),
        a i ∈ (hU.primeIdealOf q).asIdeal ↔
          f q ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
            (projectiveLinearPolynomial (A i)) := by
  obtain ⟨k,hk⟩ := Opens.mem_iSup.mp ((projective_coordinate_cover N).ge
    (show f p ∈ (⊤ : (complexProjectiveSpace N).Opens) from trivial))
  let V : (complexProjectiveSpace N).Opens :=
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X k)
  let U := f ⁻¹ᵁ V
  have hV : IsAffineOpen V := Proj.isAffineOpen_basicOpen _ _
    (projectiveVariable_mem k) (by decide : 0 < 1)
  have hU : IsAffineOpen U := hV.preimage f
  let a := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
    (MvPolynomial.X k) (projectiveVariable_mem k) (by decide : 0 < 1)
  let u := hU.fromSpec ≫ f
  have hr : Set.range u ⊆ Set.range a := by
    rintro _ ⟨q,rfl⟩
    change u q ∈ a.opensRange
    rw [Proj.opensRange_awayι]
    change hU.fromSpec q ∈ U
    have hmem : hU.fromSpec q ∈ Set.range hU.fromSpec := Set.mem_range_self q
    rw [hU.range_fromSpec] at hmem
    exact hmem
  let v := IsOpenImmersion.lift a u hr
  have hv : v ≫ a = u := IsOpenImmersion.lift_fac a u hr
  obtain ⟨ψ,hψ⟩ := Spec.map_surjective v
  let c := ψ.hom.comp (projectiveChartConstants k)
  let x (j : Fin (N+1)) := ψ.hom (projectiveChartRatio k j)
  have hx : x k = 1 := by dsimp only [x]; rw [projectiveChartRatio_self,map_one]
  have hu : projectiveAffineMap c x k hx = u := by
    rw [← hv,← hψ]
    unfold projectiveAffineMap
    congr 1
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
      (projectiveChart_hom_reconstruct k ψ.hom)
  refine ⟨U,hU,hk,fun i => MvPolynomial.eval₂Hom c x (projectiveLinearPolynomial (A i)),?_⟩
  intro i q
  have he := projectiveAffineMap_preimage_homogeneous c x k hx 1 (by decide)
    (projectiveLinearPolynomial (A i)) (projectiveLinearPolynomial_homogeneous (A i))
  rw [hu] at he
  have heq := congrArg (fun W => (hU.primeIdealOf q) ∈ W) he
  change (u (hU.primeIdealOf q) ∈ Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (projectiveLinearPolynomial (A i))) =
    (MvPolynomial.eval₂Hom c x (projectiveLinearPolynomial (A i)) ∉ (hU.primeIdealOf q).asIdeal) at heq
  dsimp only [u] at heq
  erw [Scheme.Hom.comp_apply,hU.fromSpec_primeIdealOf] at heq
  exact (not_not.symm.trans (not_congr (eq_iff_iff.mp heq)).symm)
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

theorem affine_section_dimension_lower
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (s : Finset R) (hs : (s : Set R) ⊆ p)
    (d : ℕ) (hd : (d+s.card : ℕ) ≤ p.height) :
    ∃ q : PrimeSpectrum R, q.asIdeal ≤ p ∧ (s : Set R) ⊆ q.asIdeal ∧
      (d : ℕ∞) ≤ Order.coheight q := by
  classical
  let I : Ideal R := Ideal.span (s : Set R)
  have hIp : I ≤ p := Ideal.span_le.mpr hs
  let p' : Ideal (R ⧸ I) := p.map (Ideal.Quotient.mk I)
  have : p'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  have hbd : (d : ℕ∞) ≤ p'.height := by
    apply (ENat.add_le_add_iff_right (show (s.card : ℕ∞) ≠ ⊤ by simp)).mp
    have h := hd.trans (Ideal.height_le_height_add_encard_of_subset (s : Set R) hs)
    simpa [p',I] using h
  obtain ⟨l,hl,hlen⟩ := Order.exists_series_of_le_height
    (⟨p',inferInstance⟩ : PrimeSpectrum (R ⧸ I))
      (by rwa [← PrimeSpectrum.height_eq_orderHeight])
  let L := l.map (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
  refine ⟨L.head,?_,?_,?_⟩
  · have hle := l.head_le_last
    rw [hl] at hle
    intro a ha
    exact (Ideal.mem_quotient_iff_mem hIp).mp (hle ha)
  · intro a ha
    change Ideal.Quotient.mk I a ∈ l.head.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha)]
    exact Ideal.zero_mem _
  · have hdim := Order.length_le_coheight_head (p := L)
    simpa only [L,LTSeries.map_length,hlen] using hdim
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

theorem scheme_section_dimension_lower {X : Scheme} [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) (p : U)
    (s : Finset Γ(X,U)) (hs : (s : Set Γ(X,U)) ⊆ (hU.primeIdealOf p).asIdeal)
    (d : ℕ) (hd : (d+s.card : ℕ) ≤ Order.coheight (p : X)) :
    ∃ q : U, (p : X) ≤ (q : X) ∧ (d : ℕ∞) ≤ Order.height (q : X) ∧
      (s : Set Γ(X,U)) ⊆ (hU.primeIdealOf q).asIdeal := by
  have : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hdp : (d+s.card : ℕ) ≤ (hU.primeIdealOf p).asIdeal.height := by
    let point : Spec Γ(X,U) := hU.primeIdealOf p
    have he : point.asIdeal.height = Order.coheight (p : X) := by
      calc
        point.asIdeal.height = Order.coheight point := idealHeight_eq_coheight Γ(X,U) point
        _ = Order.coheight (hU.fromSpec point) :=
          (coheight_eq_of_isOpenImmersion hU.fromSpec).symm
        _ = Order.coheight (p : X) := congrArg Order.coheight (hU.fromSpec_primeIdealOf p)
    exact he ▸ hd
  obtain ⟨q,hqp,hqs,hqd⟩ := affine_section_dimension_lower
    (hU.primeIdealOf p).asIdeal s hs d hdp
  let q' : U := hU.isoSpec.inv q
  have hqeq : hU.primeIdealOf q' = q := by
    change hU.isoSpec.hom (hU.isoSpec.inv q) = q
    exact congrArg (fun morphism : Spec Γ(X,U) ⟶ Spec Γ(X,U) => morphism (q : Spec Γ(X,U)))
      hU.isoSpec.inv_hom_id
  have hstrict : StrictMono hU.fromSpec := by
    intro a b hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    refine ⟨Specializes.map hab.le hU.fromSpec.continuous, ?_⟩
    intro h
    exact hab.not_ge (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h)
  refine ⟨q',?_,?_,by rwa [hqeq]⟩
  · rw [← hU.fromSpec_primeIdealOf p, ← hU.fromSpec_primeIdealOf q',hqeq]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hqp).map hU.fromSpec.continuous
  · have hdim := Order.height_le_height_apply_of_strictMono (α := Spec Γ(X,U))
      (β := X) hU.fromSpec hstrict q
    have he : @Order.height (Spec Γ(X,U)) _ q = Order.coheight q := by
      exact (Order.height_orderIso (specOrderIsoPrimeSpectrum Γ(X,U)) (q : Spec Γ(X,U))).symm
    rw [he] at hdim
    have heq : hU.fromSpec q = (q' : X) := by rw [← hqeq,hU.fromSpec_primeIdealOf]
    rw [heq] at hdim
    exact hqd.trans hdim
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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_section_dimension_lower {X : Scheme} [IsLocallyNoetherian X]
    {N r d : ℕ} (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (p : X) (A : Fin r → Fin (N+1) → ℂ)
    (hp : ∀ i, f p ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
      (projectiveLinearPolynomial (A i)))
    (hd : (d+r : ℕ) ≤ Order.coheight p) :
    ∃ q : X, p ≤ q ∧ (d : ℕ∞) ≤ Order.height q ∧ ∀ i,
      f q ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (A i)) := by
  classical
  obtain ⟨U,hU,hpU,a,ha⟩ := projective_hyperplane_local_equations f p A
  let s := Finset.univ.image a
  have hsp : (s : Set Γ(X,U)) ⊆ (hU.primeIdealOf ⟨p,hpU⟩).asIdeal := by
    intro b hb
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hb
    exact (ha i ⟨p,hpU⟩).mpr (hp i)
  have hcard : s.card ≤ r := by
    exact (Finset.card_image_le).trans (by simp)
  have hh : ((d+s.card : ℕ) : ℕ∞) ≤ (d+r : ℕ) := by
    exact_mod_cast Nat.add_le_add_left hcard d
  have hdp : (d+s.card : ℕ) ≤ Order.coheight p := hh.trans hd
  obtain ⟨q,hpq,hqd,hqs⟩ := scheme_section_dimension_lower U hU ⟨p,hpU⟩ s hsp d hdp
  refine ⟨q,hpq,hqd,fun i => (ha i q).mp ?_⟩
  exact hqs (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
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

theorem height_eq_zero_of_proper_affine
    {k : Type} [Field k] {X : Scheme} [IsAffine X]
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (x : X) : Order.height x = 0 := by
  have : IsFinite sX := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,inferInstance⟩
  have h := Order.height_le_height_apply_of_strictMono sX
    (strictMono_of_locallyQuasiFinite sX) x
  rw [Scheme.height_of_isClosed (isClosed_singleton : IsClosed {sX x})] at h
  exact le_antisymm h bot_le
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_hypersurface_meets_positive_dimension
    {X : Scheme} {N e : ℕ} (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (P : MvPolynomial (Fin (N+1)) ℂ) (hP : P.IsHomogeneous e) (he : 0 < e)
    (q : X) (hq : 0 < Order.height q) :
    ∃ x : X, f x ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P := by
  classical
  by_contra h
  have hall : ∀ x : X, f x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P := by
    simpa using h
  have ht : f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P = ⊤ := by
    ext x
    exact iff_true_intro (hall x)
  have hAffine : IsAffineHom f := inferInstance
  have ha : IsAffineOpen (f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) P) :=
    @IsAffineOpen.preimage X (complexProjectiveSpace N) _ (Proj.isAffineOpen_basicOpen _ P hP he) f hAffine
  rw [ht] at ha
  have : IsAffine X := by
    have : IsAffine (⊤ : X.Opens).toScheme := ha
    exact IsAffine.of_isIso X.topIso.inv
  exact hq.ne' (height_eq_zero_of_proper_affine sX q)
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

theorem exists_functionField_dimension {k : Type} [Field k] {X : Scheme}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    ∃ n : ℕ, let := schemeFieldAlgebra (.of k) sX; Algebra.trdeg k X.functionField = n := by
  let := schemeFieldAlgebra (.of k) sX
  let x := genericPoint X
  obtain ⟨_,⟨U,hU,rfl⟩,hx,-⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x,hx⟩⟩
  let := schemeOpenAlgebra sX U
  have : Algebra.FiniteType k Γ(X,U) :=
    (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  obtain ⟨n,_,hn⟩ := finiteType_dimension_trdeg k Γ(X,U)
  exact ⟨n, (affine_functionField_trdeg k sX U hU).symm.trans hn⟩
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_hyperplane_height_lower
    {X : Scheme} [IsLocallyNoetherian X] {N d : ℕ}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (q : X) (hq : (d+1 : ℕ) ≤ Order.height q) (a : Fin (N+1) → ℂ) :
    ∃ y : X, (d : ℕ∞) ≤ Order.height y ∧ y ≤ q ∧
      f y ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial a) := by
  obtain ⟨T,i,hT,hi,hr,t,ht,hth⟩ := integral_closed_closure X q
  have := hT
  have := hi
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  have htd : (d+1 : ℕ) ≤ Order.height t := hth.symm ▸ hq
  have htp : 0 < Order.height t := lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_succ d) htd
  obtain ⟨x,hx⟩ := projective_hypersurface_meets_positive_dimension (i ≫ sX) (i ≫ f)
    (projectiveLinearPolynomial a) (projectiveLinearPolynomial_homogeneous a) (by decide) t htp
  let V := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
    (projectiveLinearPolynomial a)
  let Z : Set T := ((i ≫ f) ⁻¹ᵁ V : Set T)ᶜ
  have hZ : IsClosed Z := ((i ≫ f) ⁻¹ᵁ V).isOpen.isClosed_compl
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace (i ≫ sX)
  obtain ⟨p,hp,hpc⟩ := nonempty_inter_closedPoints (show Z.Nonempty from ⟨x,hx⟩)
    hZ.isLocallyClosed
  obtain ⟨m,hm⟩ := exists_functionField_dimension (i ≫ sX)
  obtain ⟨_,hclosed,hheight⟩ := scheme_dimension_of_functionField ℂ (i ≫ sX) m hm
  have hpd : (d+1 : ℕ) ≤ Order.coheight p := by
    rw [hclosed p hpc]
    exact htd.trans (hheight t)
  obtain ⟨y,_,hyd,hy⟩ := projective_section_dimension_lower (i ≫ f) p
    (fun _ : Fin 1 => a) (fun _ => hp) hpd
  refine ⟨i y,?_,?_,hy 0⟩
  · rwa [← height_eq_of_closedImmersion i y]
  · change q ⤳ i y
    exact specializes_iff_mem_closure.mpr (hr ▸ Set.mem_range_self y)

theorem projective_intersection_height_lower
    {X : Scheme} [IsLocallyNoetherian X] {N d : ℕ}
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (A : List (Fin (N+1) → ℂ)) (q : X) (hq : (d+A.length : ℕ) ≤ Order.height q) :
    ∃ y : X, (d : ℕ∞) ≤ Order.height y ∧ y ≤ q ∧
      ∀ a ∈ A, f y ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial a) := by
  induction A generalizing q with
  | nil => exact ⟨q,by simpa using hq,le_rfl,by simp⟩
  | cons a A ih =>
      have hq' : (d+A.length+1 : ℕ) ≤ Order.height q := by simpa [Nat.add_assoc] using hq
      obtain ⟨y,hy,hyq,hya⟩ := projective_hyperplane_height_lower sX f q hq' a
      obtain ⟨z,hz,hzy,hzA⟩ := ih y hy
      refine ⟨z,hz,hzy.trans hyq,?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · subst b
        have hcl := (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
          (projectiveLinearPolynomial a)).isOpen.isClosed_compl
        exact (show f y ⤳ f z from (show y ⤳ z from hzy).map f.continuous).mem_closed hcl hya
      · exact hzA b hb
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveAffineMap_preimage_linear {R : Type} [CommRing R] {N : ℕ}
    (c : ℂ →+* R) (x : Fin (N+1) → R) (i : Fin (N+1)) (hi : x i = 1)
    (a : Fin (N+1) → ℂ) :
    projectiveAffineMap c x i hi ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial a) =
      PrimeSpectrum.basicOpen (∑ j, c (a j) * x j) := by
  change (Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)) ⁻¹ᵁ
    Proj.basicOpen _ _ = _
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (projectiveVariable_mem i) (by decide : 0 < 1)
      (projectiveLinearPolynomial_homogeneous a) (by decide : 0 < 1)]
  have he : projectiveChartRingHom c x i hi
      (Away.isLocalizationElem (projectiveVariable_mem i)
        (projectiveLinearPolynomial_homogeneous a)) = ∑ j, c (a j) * x j := by
    change projectiveChartRingHom c x i hi (Away.mk _ _ 1 (projectiveLinearPolynomial a ^ 1) _) = _
    rw [projectiveChartRingHom_mk,map_pow,pow_one]
    simp [projectiveLinearPolynomial,Algebra.smul_def]
  ext p
  change projectiveChartRingHom c x i hi _ ∉ p.asIdeal ↔ _ ∉ p.asIdeal
  rw [he]

theorem DivisorProjectiveChart.toMorphism_preimage_linear
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (C : DivisorProjectiveChart X D s) (sX : X ⟶ Spec (.of ℂ))
    (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))) :
    C.toMorphism sX ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (parameterCoefficient p)) =
      C.domain.ι ⁻¹ᵁ X.basicOpen (C.member sX p) := by
  have he := congrArg (fun W : (Spec Γ(X,C.domain)).Opens => C.domain.toSpecΓ ⁻¹ᵁ W)
    (projectiveAffineMap_preimage_linear (schemeOpenScalar sX C.domain)
      C.normalized C.unit_index C.normalized_index (parameterCoefficient p))
  refine he.trans ?_
  rw [Scheme.Opens.toSpecΓ_preimage_basicOpen]
  congr 2
  simp [DivisorProjectiveChart.member,mul_comm]
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne

theorem IncidenceCutChain.height_le
    {k : Type} [Field k] {n r d : ℕ} {X S : Scheme}
    {sX : X ⟶ Spec (.of k)} {J : 𝔸(Fin n;X).IdealSheafData} {i : S ⟶ X}
    (h : IncidenceCutChain X sX J r S i)
    (hd : ∀ x : X, Order.height x ≤ (d+r : ℕ)) :
    ∀ x : S, Order.height x ≤ d := by
  induction h with
  | nil X sX J => simpa using hd
  | @cons X sX J p hp hproper r S i h ih =>
    apply ih
    intro x
    let I := J.comap (parameterSection sX p)
    have hx : I.subschemeι x ∈ I.support := by
      change I.subschemeι x ∈ (I.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self x
    obtain ⟨g,hg⟩ := hproper _ hx
    have hlt := Order.height_add_one_le hg
    rw [← height_eq_of_closedImmersion I.subschemeι x] at hlt
    have htot := hlt.trans (hd g)
    have : Order.height x ≤ (d+r : ℕ) := by
      apply (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      simpa only [Nat.cast_add,Nat.cast_one,Nat.add_assoc,add_assoc] using htot
    exact this
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem DivisorAffineAtlas.incidence_member_support
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (A : DivisorAffineAtlas X D s) (sX : X ⟶ Spec (.of ℂ))
    (J : 𝔸(Fin (N+1);X).IdealSheafData)
    (hJ : ∀ j, J.comap (AffineSpace.map _ (A.cover.f j)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate j)}))
    (f : X ⟶ complexProjectiveSpace N)
    (hf : ∀ j, (A.chart j).domain.ι ≫ f = (A.chart j).toMorphism sX)
    (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))) :
    ((J.comap (parameterSection sX p)).support : Set X) =
      {x | f x ∉ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (parameterCoefficient p))} := by
  ext x
  obtain ⟨j,hx⟩ := A.covers x
  let C := A.chart j
  let y : C.domain := ⟨x,hx⟩
  have : IsAffine (A.cover.X j) := A.affine j
  have he := parameter_member_chart (A.cover.f j) sX p J (A.coordinate j) (hJ j)
  change (J.comap (parameterSection sX p)).comap C.domain.ι =
    Scheme.IdealSheafData.ofIdealTop (Ideal.span {linearMemberSection (C.domain.ι ≫ sX) p
      (fun z => C.domain.topIso.inv (C.normalized z))}) at he
  rw [← C.member_topIso sX p] at he
  have hs := congrArg (fun K => (y : A.cover.X j) ∈ K.support) he
  rw [Scheme.IdealSheafData.support_comap] at hs
  change (x ∈ (J.comap (parameterSection sX p)).support) =
    (y ∈ (Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {C.domain.topIso.inv (C.member sX p)})).support) at hs
  have hz : y ∈ (Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {C.domain.topIso.inv (C.member sX p)})).support ↔
      x ∉ X.basicOpen (C.member sX p) := by
    change y ∈ ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {C.domain.topIso.inv (C.member sX p)})).support : Set C.domain.toScheme) ↔ _
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop,Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    have hh := C.domain.ι_image_basicOpen_topIso_inv (C.member sX p)
    have hh' : y ∈ C.domain.toScheme.basicOpen (C.domain.topIso.inv (C.member sX p)) ↔
        x ∈ X.basicOpen (C.member sX p) := by
      rw [← hh]
      exact C.domain.ι.isOpenEmbedding.injective.mem_set_image.symm
    exact not_congr hh'
  have hm := congrArg (fun W : C.domain.toScheme.Opens => y ∈ W)
    (C.toMorphism_preimage_linear sX p)
  rw [← hf j] at hm
  change (((A.chart j).domain.ι ≫ f) y ∈
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
      (projectiveLinearPolynomial (parameterCoefficient p)) : (complexProjectiveSpace N).Opens)) =
    (x ∈ X.basicOpen (C.member sX p)) at hm
  change (f x ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
      (projectiveLinearPolynomial (parameterCoefficient p)) : (complexProjectiveSpace N).Opens)) =
    (x ∈ X.basicOpen (C.member sX p)) at hm
  change (x ∈ (J.comap (parameterSection sX p)).support) ↔ _
  exact hs.to_iff.trans (hz.trans (not_congr hm.to_iff).symm)

lemma incidenceIntersectionIdeal_mem_support {k : Type} [Field k] {n : ℕ}
    {X : Scheme} (sX : X ⟶ Spec (.of k)) (J : 𝔸(Fin n;X).IdealSheafData)
    (ps : List (Spec (.of k) ⟶ 𝔸(Fin n;Spec (.of k)))) (x : X) :
    x ∈ (incidenceIntersectionIdeal sX J ps).support ↔
      ∀ p ∈ ps, x ∈ (J.comap (parameterSection sX p)).support := by
  induction ps with
  | nil =>
    simp only [incidenceIntersectionIdeal,Scheme.IdealSheafData.support_bot,List.not_mem_nil,
      false_implies]
    exact ⟨fun _ _ => trivial,fun _ => Set.mem_univ x⟩
  | cons p ps ih =>
    simp only [incidenceIntersectionIdeal,Scheme.IdealSheafData.support_sup,
      List.mem_cons,forall_eq_or_imp]
    change (x ∈ (J.comap (parameterSection sX p)).support ∧
      x ∈ (incidenceIntersectionIdeal sX J ps).support) ↔ _
    exact and_congr_right (fun _ => ih)

theorem IncidenceCutChain.exists_height_ge_of_embedding
    {X S : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N d r : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (A : DivisorAffineAtlas X D s) (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (J : 𝔸(Fin (N+1);X).IdealSheafData)
    (hJ : ∀ j, J.comap (AffineSpace.map _ (A.cover.f j)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate j)}))
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (hf : ∀ j, (A.chart j).domain.ι ≫ f = (A.chart j).toMorphism sX)
    {i : S ⟶ X} (h : IncidenceCutChain X sX J r S i)
    (q : X) (hq : (d+r : ℕ) ≤ Order.height q) :
    ∃ x : S, (d : ℕ∞) ≤ Order.height x := by
  have := h.isClosedImmersion
  obtain ⟨ps,hps,_,hker⟩ := h.exists_parameters
  obtain ⟨y,hyd,_,hy⟩ := projective_intersection_height_lower sX f
    (ps.map parameterCoefficient) q (by simpa [hps] using hq)
  have hym : y ∈ (incidenceIntersectionIdeal sX J ps).support := by
    rw [incidenceIntersectionIdeal_mem_support]
    intro p hp
    change y ∈ ((J.comap (parameterSection sX p)).support : Set X)
    rw [A.incidence_member_support sX J hJ f hf p]
    exact hy _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hr : (i.ker.support : Set X) = Set.range i := by
    rw [Scheme.Hom.support_ker,i.isClosedEmbedding.isClosed_range.closure_eq]
  obtain ⟨x,hxy⟩ := (hr ▸ (hker.symm ▸ hym) : y ∈ Set.range i)
  refine ⟨x,?_⟩
  rwa [height_eq_of_closedImmersion i x,hxy]
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne
lemma scheme_topologicalKrullDim_eq (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints
lemma genericPoint_height_eq_dimension (X : Scheme) [IrreducibleSpace X] :
    (Order.height (genericPoint X) : WithBot ℕ∞) = topologicalKrullDim X := by
  let : OrderTop X := { top := genericPoint X, le_top := genericPoint_specializes }
  rw [scheme_topologicalKrullDim_eq]
  exact Order.height_top_eq_krullDim (α := X)
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne

theorem functionField_dimension_of_dimension {k : Type} [Field k] {X : Scheme}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (n : ℕ) (hdim : topologicalKrullDim X = n) :
    let := schemeFieldAlgebra (.of k) sX; Algebra.trdeg k X.functionField = n := by
  obtain ⟨m,hm⟩ := exists_functionField_dimension sX
  obtain ⟨_,hclosed,hheight⟩ := scheme_dimension_of_functionField k sX m hm
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨x,_,hxc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
    isClosed_univ.isLocallyClosed
  have hlo : (m : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [scheme_topologicalKrullDim_eq]
    have h := Order.coheight_le_krullDim x
    rw [hclosed x hxc] at h
    exact h
  have hup : topologicalKrullDim X ≤ m := by
    rw [scheme_topologicalKrullDim_eq,Order.krullDim_eq_iSup_height]
    exact iSup_le (fun x => WithBot.coe_le_coe.mpr (hheight x))
  have hmn : m = n := by
    exact_mod_cast (le_antisymm hup hlo).symm.trans hdim
  simpa only [hmn] using hm
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
open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace NumericalDimensionOne

theorem exists_closed_point_in_component_interior (X : Scheme)
    [NoetherianSpace X] [JacobsonSpace X]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    ∃ x : X, IsClosed {x} ∧ x ∈ Z ∧ ∀ y : X, x ≤ y → y ∈ Z := by
  classical
  let B : Set X := ⋃₀ (irreducibleComponents X \ {Z})
  have hB : IsClosed B := by
    simpa only [B,Set.sUnion_eq_biUnion] using
      (NoetherianSpace.finite_irreducibleComponents (α := X)).sdiff.isClosed_biUnion
        (fun T hT => isClosed_of_mem_irreducibleComponents T hT.1)
  have he : closure Bᶜ = Z := closure_sUnion_irreducibleComponents_sdiff_singleton
    NoetherianSpace.finite_irreducibleComponents Z hZ
  have hne : Bᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h,closure_empty] at he
    exact hZ.1.nonempty.ne_empty he.symm
  obtain ⟨x,hx,hxc⟩ := nonempty_inter_closedPoints hne
    hB.isOpen_compl.isLocallyClosed
  have hsub : Bᶜ ⊆ Z := he ▸ subset_closure
  refine ⟨x,hxc,hsub hx,fun y hy => hsub ?_⟩
  exact (show y ⤳ x from hy).mem_open hB.isOpen_compl hx
end NumericalDimensionOne

end OAI
