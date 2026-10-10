import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteProperMapOpen

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem exists_algHom_separating_element
    {k S I : Type*} [Field k] [Infinite k] [CommRing S] [Algebra k S]
    [Finite I] (f : I → (S →ₐ[k] k)) (hf : Function.Injective f) :
    ∃ t : S, Function.Injective (fun i => f i t) := by
  classical
  let J := {ij : I × I // ij.1 ≠ ij.2}
  let L : J → Module.Dual k S := fun ij =>
    (f ij.val.1).toLinearMap - (f ij.val.2).toLinearMap
  have hL : ∀ ij : J, ∃ x, L ij x ≠ 0 := by
    intro ij
    by_contra! h
    have he : f ij.val.1 = f ij.val.2 := by
      ext x
      exact sub_eq_zero.mp (h x)
    exact ij.property (hf he)
  obtain ⟨t, ht⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists L hL
  refine ⟨t, fun i j hij => ?_⟩
  by_contra hne
  exact ht ⟨(i,j), hne⟩ (sub_eq_zero.mpr hij)

theorem normalization_proper_finite {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (hgi : g.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j)) :
    IsProperMap (fun z : MvPolynomial.zeroLocus ℂ I =>
      fun j => MvPolynomial.eval z.val (P j)) ∧
    ∀ y : Fin d → ℂ, {z : MvPolynomial.zeroLocus ℂ I |
      (fun j => MvPolynomial.eval z.val (P j)) = y}.Finite := by
  choose Q hQ hQr using fun i : Fin n => hgi (quotientCoordinate I i)
  have hroot : ∀ z ∈ MvPolynomial.zeroLocus ℂ I, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0 := by
    intro z hz i
    let e := affineCharacter I ⟨z, hz⟩
    have heg : e.toRingHom.comp g.toRingHom =
        MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)) :=
      congrArg AlgHom.toRingHom (affineCharacter_normalization I g P hP ⟨z, hz⟩)
    have hh := congrArg e.toRingHom (hQr i)
    rw [map_zero, Polynomial.hom_eval₂, heg] at hh
    simpa only [e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, affineCharacter_coordinate] using hh
  constructor
  · apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨continuous_pi fun j => (P j).continuous_eval.comp continuous_subtype_val, ?_⟩
    intro K hK
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : (Subtype.val : MvPolynomial.zeroLocus ℂ I → (Fin n → ℂ)) ''
        ((fun z : MvPolynomial.zeroLocus ℂ I => fun j => MvPolynomial.eval z.val (P j)) ⁻¹' K) =
        {z ∈ MvPolynomial.zeroLocus ℂ I | (fun j => MvPolynomial.eval z (P j)) ∈ K} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w.property, hw⟩
      · rintro ⟨hz, hKz⟩; exact ⟨⟨z, hz⟩, hKz, rfl⟩
    rw [heq]
    have hclosed : IsClosed (MvPolynomial.zeroLocus ℂ I) := by
      have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
          {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
        ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
      rw [he]
      exact isClosed_iInter fun p => isClosed_iInter fun _ =>
        isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    exact isCompact_preimage_of_integral_coordinates hclosed P Q hQ hroot hK
  · intro y
    have hf := (finite_fiber_of_integral_coordinates P Q hQ hroot y).preimage
      (f := (Subtype.val : MvPolynomial.zeroLocus ℂ I → (Fin n → ℂ)))
      Subtype.val_injective.injOn
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using hf

theorem finite_algebra_complex_points_isOpenMap {d : ℕ}
    {S X : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) S]
    [Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) S]
    [Algebra.FiniteType ℂ S] [TopologicalSpace X]
    (e : X ≃ (S →ₐ[ℂ] ℂ))
    (he : ∀ t : S, Continuous (fun x => e x t))
    (π : X → (Fin d → ℂ))
    (hbase : ∀ x r, e x (algebraMap (MvPolynomial (Fin d) ℂ) S r) = MvPolynomial.eval (π x) r)
    (hπ : IsProperMap π) (hfin : ∀ y, Set.Finite {x | π x = y}) :
    IsOpenMap π := by
  classical
  let R := MvPolynomial (Fin d) ℂ
  intro N hN
  apply isOpen_iff_mem_nhds.mpr
  rintro a ⟨q, hq, rfl⟩
  let F := {x | π x = π q}
  have : Finite F := (hfin (π q)).to_subtype
  obtain ⟨t, ht⟩ := exists_algHom_separating_element
    (fun x : F => e x.val) (e.injective.comp Subtype.val_injective)
  let s := fun x => e x t
  have hsep : ∀ x, π x = π q → s x = s q → x = q := by
    intro x hx hs
    exact congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨q, rfl⟩) hs)
  have htint : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  have hroot : (minpoly R t).eval₂ (MvPolynomial.eval (π q)) (s q) = 0 := by
    rw [← algHom_aeval_of_base (e q) _ (hbase q), minpoly.aeval, map_zero]
  apply finite_proper_map_open_at_of_root_realization π hπ q (hfin (π q)) s (he t)
    hsep (minpoly R t) (minpoly.monic htint) hroot ?_ hN hq
  intro y b hb
  obtain ⟨f, hf, hfb⟩ := realize_specialized_minpoly_root (S := S)
    (MvPolynomial.aeval y) t b hb
  let x := e.symm f
  have hex : e x = f := e.apply_symm_apply f
  refine ⟨x, ?_, ?_⟩
  · ext j
    have he' := hbase x (MvPolynomial.X j)
    rw [hex, hf] at he'
    simpa only [MvPolynomial.aeval_X, MvPolynomial.eval_X] using he'.symm
  · change e x t = b
    rw [hex, hfb]

theorem normalization_isOpenMap {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (hg : Function.Injective g) (hgi : g.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j)) :
    IsOpenMap (fun z : MvPolynomial.zeroLocus ℂ I =>
      fun j => MvPolynomial.eval z.val (P j)) := by
  let normalizationAlgebra : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    g.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    normalizationAlgebra.toSMul
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    IsScalarTower.of_algHom g
  let : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ I)).mpr hg
  let : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := ⟨hgi⟩
  obtain ⟨hπ, hfin⟩ := normalization_proper_finite I g hgi P hP
  apply finite_algebra_complex_points_isOpenMap (affineCharacterEquiv I)
    (continuous_affineCharacter I) _ ?_ hπ hfin
  intro z r
  exact DFunLike.congr_fun (affineCharacter_normalization I g P hP z) r

theorem normalization_analytic_sheets {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (G : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ J))
    (hG : Function.Injective G) (hGi : G.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ J) (P j) = G (MvPolynomial.X j)) :
    ∃ (D : MvPolynomial (Fin d) ℂ) (r : ℕ), D ≠ 0 ∧ 0 < r ∧
      ∀ a : Fin d → ℂ, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (W : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen W ∧ a ∈ W ∧
        (∀ i, AnalyticOnNhd ℂ (g i) W) ∧
        ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
          ∀ z : Fin n → ℂ,
            (z ∈ MvPolynomial.zeroLocus ℂ J ∧
              (fun j => MvPolynomial.eval z (P j)) = y) ↔ ∃ i, g i y = z := by
  let normalizationAlgebra : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    G.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    normalizationAlgebra.toSMul
  let : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    @Algebra.toModule _ _ _ _ normalizationAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    IsScalarTower.of_algHom G
  let : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J)).mpr hG
  let : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := ⟨hGi⟩
  let : Algebra.FiniteType (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J)
  let : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.finite
  obtain ⟨D, r, hD, hr, hh⟩ := finite_algebra_generic_sheets_constant_degree (d := d)
    (quotientCoordinate J) (adjoin_quotientCoordinate J)
  refine ⟨D, r, hD, hr, fun a ha => ?_⟩
  obtain ⟨I, g, W, hcard, hW, haW, hg, hs⟩ := hh a ha
  refine ⟨I, g, W, hcard, hW, haW, hg, fun y hy => ⟨(hs y hy).1, fun z => ?_⟩⟩
  rw [← (hs y hy).2 z]
  constructor
  · rintro ⟨hz, hzy⟩
    refine ⟨affineCharacter J ⟨z, hz⟩, ?_, fun j => affineCharacter_coordinate J ⟨z,hz⟩ j⟩
    intro b
    have he := DFunLike.congr_fun (affineCharacter_normalization J G P hP ⟨z,hz⟩) b
    rw [hzy] at he
    exact he
  · rintro ⟨f, hf, hfz⟩
    let w := pointOfCharacter J f
    have hw : w.val = z := funext hfz
    refine ⟨hw ▸ w.property, funext fun j => ?_⟩
    have he := DFunLike.congr_fun (affineCharacter_normalization J G P hP w) (MvPolynomial.X j)
    have hef : affineCharacter J w = f := (affineCharacterEquiv J).apply_symm_apply f
    rw [hef] at he
    change f (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
      (MvPolynomial.X j)) = _ at he
    rw [hf, MvPolynomial.eval_X, MvPolynomial.aeval_X, hw] at he
    exact he.symm

noncomputable def fiberPolynomial {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y) : Polynomial ℂ := by
  classical
  exact ∏ x ∈ (hfin y).toFinset, (Polynomial.X - C (h x))

theorem fiberPolynomial_eq_prod {X Y K : Type*} [Fintype K]
    (π : X → Y) (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y)
    (s : K → X) (hinj : Function.Injective s)
    (hs : ∀ x, π x = y ↔ ∃ j, s j = x) :
    fiberPolynomial π hfin h y = ∏ j, (Polynomial.X - C (h (s j))) := by
  classical
  unfold fiberPolynomial
  symm
  apply Finset.prod_bij (fun j _ => s j)
  · intro j _
    exact (hfin y).mem_toFinset.mpr ((hs (s j)).mpr ⟨j,rfl⟩)
  · intro j _ k _ hjk
    exact hinj hjk
  · intro x hx
    obtain ⟨j, hj⟩ := (hs x).mp ((hfin y).mem_toFinset.mp hx)
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro j _
    rfl

theorem fiberPolynomial_eval_eq_zero {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (x : X) :
    (fiberPolynomial π hfin h (π x)).eval (h x) = 0 := by
  classical
  unfold fiberPolynomial
  rw [eval_prod]
  apply Finset.prod_eq_zero ((hfin (π x)).mem_toFinset.mpr (show x ∈ π ⁻¹' {π x} from rfl))
  simp

theorem fiberPolynomial_monic {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y) :
    (fiberPolynomial π hfin h y).Monic := by
  classical
  exact monic_prod_of_monic _ _ (fun point _ => monic_X_sub_C (h point))

theorem fiberPolynomial_natDegree {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y) :
    (fiberPolynomial π hfin h y).natDegree = (hfin y).toFinset.card := by
  classical
  unfold fiberPolynomial
  rw [natDegree_prod _ _ (fun x _ => (monic_X_sub_C (h x)).ne_zero)]
  simp

end Release061

end OAI
