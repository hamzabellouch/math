import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.FinrankDerivationCardTranscendenceBasis
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ParameterIdeal

namespace OAI

namespace SiegelZeros

noncomputable section
attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
open Module
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open Polynomial IsLocalRing TensorProduct
open TensorProduct IsLocalRing
open scoped TensorProduct
open scoped BigOperators
namespace WeightedTorusJets

universe u

open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

theorem scheme_coordinates_constant_of_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [UniversallyClosed p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, ∃ a : k, algebraMap k X.functionField a = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  obtain ⟨s, _, hs⟩ := scheme_global_units_of_locallyOfFiniteType_log_form p c hc f hf hω i
  obtain ⟨a, ha, _⟩ := existsUnique_globalSection_scalar k p s
  refine ⟨a, ?_⟩
  change schemeBaseToStalk p (genericPoint X) a = f i
  rw [schemeBaseToStalk_eq_global_germ, RingHom.comp_apply, ha]
  exact hs

end WeightedTorusJets

namespace WeightedTorusJets

theorem logarithmic_relation_map_algHom
    {ι k F L : Type*} [Fintype ι] [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L]
    (φ : F →ₐ[k] L) (c : ι → k) (f : ι → F)
    (h : ∑ i, (algebraMap k F (c i) / f i) • KaehlerDifferential.D k F (f i) = 0) :
    ∑ i, (algebraMap k L (c i) / φ (f i)) •
      KaehlerDifferential.D k L (φ (f i)) = 0 := by
  algebraize [φ.toRingHom]
  have hm := congrArg (KaehlerDifferential.map k k F L) h
  rw [map_zero] at hm
  convert hm using 1
  simp only [map_sum, map_smul, KaehlerDifferential.map_D]
  apply Finset.sum_congr rfl
  intro i _
  symm
  rw [← IsScalarTower.algebraMap_smul L, map_div₀,
    IsScalarTower.algebraMap_apply k F L]
  rfl



universe u

open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

theorem coordinates_constant_of_log_form_via_normal_model
    {ι F : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [Field F] [Algebra k F]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [UniversallyClosed p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    ∀ _φ : F →ₐ[k] X.functionField,
      (∑ i, (algebraMap k F (c i) / f i) • KaehlerDifferential.D k F (f i) = 0) →
      ∀ i, ∃ a : k, algebraMap k F a = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro φ hω i
  have hf' (i) : φ (f i) ≠ 0 := by
    intro hz
    apply hf i
    apply φ.injective
    change φ (f i) = φ 0
    simpa only [map_zero] using hz
  obtain ⟨a, ha⟩ := scheme_coordinates_constant_of_log_form p c hc
    (fun i => φ (f i)) hf' (logarithmic_relation_map_algHom φ c f hω) i
  refine ⟨a, ?_⟩
  apply φ.injective
  change φ (algebraMap k F a) = φ (f i)
  exact (φ.commutes a).trans ha

end WeightedTorusJets

namespace WeightedTorusJets

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem laurent_range_mem_intermediateField
    (q : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] L) (S : IntermediateField K L)
    (h : ∀ i, q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ∈ S)
    (p : AddMonoidAlgebra K (ι →₀ ℤ)) : q p ∈ S := by
  have hm (m : ι →₀ ℤ) : q (AddMonoidAlgebra.single m 1) ∈ S := by
    induction m using Finsupp.induction_linear with
    | zero => change q 1 ∈ S; simp
    | add m n hm hn =>
        rw [show AddMonoidAlgebra.single (m + n) (1 : K) =
          AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single n 1 by simp, map_mul]
        exact S.mul_mem hm hn
    | single i z =>
        let f := q.toMonoidHom.comp (AddMonoidAlgebra.of K (ι →₀ ℤ))
        have hz : q (AddMonoidAlgebra.single (Finsupp.single i z) 1) =
            q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ^ z := by
          simpa [f, ← ofAdd_zsmul, Finsupp.smul_single, zsmul_eq_mul] using
            map_zpow f (Multiplicative.ofAdd (Finsupp.single i 1)) z
        rw [hz]
        exact S.toSubfield.zpow_mem (h i) z
  induction p using AddMonoidAlgebra.induction_on with
  | of m => exact hm m
  | add p r hp hr => rw [map_add]; exact S.add_mem hp hr
  | smul c p hp => rw [map_smul, Algebra.smul_def]; exact S.mul_mem (S.algebraMap_mem c) hp

theorem laurent_fraction_adjoin_coordinates
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime] :
    IntermediateField.adjoin K (Set.range fun i : ι ↦
      algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) = ⊤ := by
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let j : B →ₐ[K] FractionRing B := IsScalarTower.toAlgHom K B (FractionRing B)
  let S := IntermediateField.adjoin K (Set.range fun i : ι ↦
    j (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1)))
  have hB (b : B) : algebraMap B (FractionRing B) b ∈ S := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K P b
    apply laurent_range_mem_intermediateField (j.comp (Ideal.Quotient.mkₐ K P)) S ?_ p
    intro i
    exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B x
  exact S.div_mem (hB a) (hB b)

theorem laurent_quotient_exists_nonconstant_coordinate
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P)) :
    ∃ i, ¬ ∃ c : K,
      algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
          (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1)) =
        algebraMap K (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P)) c := by
  by_contra! h
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let j : B →ₐ[K] FractionRing B := IsScalarTower.toAlgHom K B (FractionRing B)
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K P b
    have hp := laurent_range_mem_intermediateField
      (j.comp (Ideal.Quotient.mkₐ K P)) (⊥ : IntermediateField K (FractionRing B))
      (fun i ↦ IntermediateField.mem_bot.mpr (by
        obtain ⟨c, hc⟩ := h i
        exact ⟨c, hc.symm⟩)) p
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hp
    refine ⟨c, IsFractionRing.injective B (FractionRing B) ?_⟩
    exact (j.commutes c).trans hc
  have hle := ringKrullDim_le_of_surjective (algebraMap K B) hsurj
  have hzero : ringKrullDim K = 0 := Order.krullDim_eq_zero_of_unique
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hdim

theorem derivation_laurent_fraction_eq_zero
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (D : Derivation K (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
      (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P)))
    (h : ∀ i, D (algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
      (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) = 0) :
    D = 0 := by
  ext x
  have hx : x ∈ IntermediateField.adjoin K (Set.range fun i : ι ↦
      algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) := by
    rw [laurent_fraction_adjoin_coordinates P]
    exact IntermediateField.mem_top
  change D x = 0
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | algebraMap c => exact D.map_algebraMap c
  | add x y _ _ hx hy => simp [hx, hy]
  | inv x _ hx => simp [D.leibniz_inv, hx]
  | mul x y _ _ hx hy => simp [D.leibniz, hx, hy]

theorem laurent_finiteType [Finite ι] :
    Algebra.FiniteType K (AddMonoidAlgebra K (ι →₀ ℤ)) := by
  apply AddMonoidAlgebra.finiteType_iff_group_fg.mpr
  exact AddGroup.fg_of_surjective
    (f := (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).symm.toAddMonoidHom)
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).symm.surjective

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {k F ι : Type*} [Field k] [Field F] [Algebra k F] [Fintype ι]

noncomputable def logarithmicForm (c : ι → k) (f : ι → F) :
    KaehlerDifferential k F :=
  ∑ i, (algebraMap k F (c i) * (f i)⁻¹) • KaehlerDifferential.D k F (f i)

theorem logarithmicForm_eq_zero_iff (c : ι → k) (f : ι → F) :
    logarithmicForm c f = 0 ↔
      ∀ D : Derivation k F F, ∑ i, algebraMap k F (c i) * (f i)⁻¹ * D (f i) = 0 := by
  constructor
  · intro h D
    simpa [logarithmicForm] using congrArg D.liftKaehlerDifferential h
  · intro h
    apply (Module.forall_dual_apply_eq_zero_iff F _).mp
    intro φ
    simpa [logarithmicForm] using h (φ.compDer (KaehlerDifferential.D k F))

noncomputable def logarithmicTangentMap (f : ι → F) :
    Derivation k F F →ₗ[F] (ι → F) where
  toFun D i := (f i)⁻¹ * D (f i)
  map_add' D E := by ext i; simp [mul_add]
  map_smul' a D := by ext i; simp [mul_left_comm]

noncomputable def logarithmicLinearForm (c : ι → k) : (ι → F) →ₗ[F] F :=
  ∑ i, algebraMap k F (c i) • LinearMap.proj i

theorem logarithmicLinearForm_apply (c : ι → k) (v : ι → F) :
    logarithmicLinearForm c v = ∑ i, algebraMap k F (c i) * v i := by
  simp [logarithmicLinearForm, Algebra.smul_def]

theorem logarithmicForm_ne_zero_iff_tangent_not_le (c : ι → k) (f : ι → F) :
    logarithmicForm c f ≠ 0 ↔
      ¬ LinearMap.range (logarithmicTangentMap (k := k) f) ≤
        LinearMap.ker (logarithmicLinearForm (F := F) c) := by
  rw [not_iff_not, logarithmicForm_eq_zero_iff]
  constructor
  · intro h v hv
    obtain ⟨D, rfl⟩ := hv
    rw [LinearMap.mem_ker, logarithmicLinearForm_apply]
    simpa only [logarithmicTangentMap, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using h D
  · intro h D
    have hD := h (LinearMap.mem_range_self (logarithmicTangentMap (k := k) f) D)
    rw [LinearMap.mem_ker, logarithmicLinearForm_apply] at hD
    simpa only [logarithmicTangentMap, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc] using hD

variable {L : Type*} [Field L] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

universe u

open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

theorem logarithmicForm_ne_zero_on_torus_subvariety_of_normal_model
    {K : Type u} {ι : Type} [Field K] [CharZero K] [IsAlgClosed K] [Fintype ι]
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
    (c : ι → K) (hc : LinearIndependent ℚ c)
    {N : Scheme.{u}} [IsIntegral N] [IsLocallyNoetherian N]
    [∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)]
    (p : N ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [UniversallyClosed p] :
    let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
    ∀ _φ : FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P) →ₐ[K] N.functionField,
      logarithmicForm c (fun i ↦ algebraMap _
        (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
          (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) ≠ 0 := by
  let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  dsimp only
  intro φ hform
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let q : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] FractionRing B :=
    (IsScalarTower.toAlgHom K B (FractionRing B)).comp (Ideal.Quotient.mkₐ K P)
  have hf (i : ι) : q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ≠ 0 :=
    ((Group.isUnit (Multiplicative.ofAdd (Finsupp.single i 1))).map
      (q.toMonoidHom.comp (AddMonoidAlgebra.of K (ι →₀ ℤ)))).ne_zero
  have hconst := coordinates_constant_of_log_form_via_normal_model p c hc
    (fun i => q (AddMonoidAlgebra.single (Finsupp.single i 1) 1)) hf φ
    (by simpa only [logarithmicForm, div_eq_mul_inv, q, B, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk] using hform)
  obtain ⟨i, hi⟩ := laurent_quotient_exists_nonconstant_coordinate P hdim
  obtain ⟨a, ha⟩ := hconst i
  exact hi ⟨a, ha.symm⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

universe u

open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry

theorem logarithmicForm_ne_zero_on_torus_subvariety
    {K : Type u} {ι : Type} [Field K] [CharZero K] [IsAlgClosed K] [Fintype ι]
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
    (c : ι → K) (hc : LinearIndependent ℚ c) :
    logarithmicForm c (fun i ↦ algebraMap _
      (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) ≠ 0 := by
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  have : Algebra.FiniteType K (AddMonoidAlgebra K (ι →₀ ℤ)) := laurent_finiteType
  obtain ⟨N, hN, hrest⟩ := exists_normal_proper_model_of_finiteType_domain K B
  let := hN
  obtain ⟨p, hNoeth, hNormal, hFT, hClosed, hφ⟩ := hrest
  have := hNoeth
  have := hFT
  have := hClosed
  have : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x) := hNormal
  let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  obtain ⟨φ⟩ := hφ
  exact logarithmicForm_ne_zero_on_torus_subvariety_of_normal_model P hdim c hc p φ

end WeightedTorusJets.Geometry






namespace WeightedTorusJets.Geometry

theorem finrank_normal_image_of_not_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (T : Submodule K V) (h : ¬ T ≤ LinearMap.ker ω) :
    Module.finrank K (LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω))) =
      Module.finrank K V - Module.finrank K T := by
  have hs : LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω)) = ⊤ := by
    rw [LinearMap.range_domRestrict, Submodule.map_mkQ_eq_top]
    obtain ⟨x, hxT, hxω⟩ := SetLike.not_le_iff_exists.mp h
    apply top_unique
    rw [← LinearMap.span_singleton_sup_ker_eq_top ω hxω]
    exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).mpr hxT) _
  rw [hs, finrank_top, Submodule.finrank_quotient]



theorem logarithmicHyperplane_normal_rank_at_point
    {K : Type*} [Field K] [CharZero K] (x c : Fin 4 → K)
    (hc : LinearIndependent ℚ c) :
    Module.finrank K (LinearMap.range
      ((LinearMap.range (logarithmicTangentMap (k := K) x)).mkQ.domRestrict
        (LinearMap.ker (logarithmicLinearForm (F := K) c)))) = 3 := by
  have hT : LinearMap.range (logarithmicTangentMap (k := K) x) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext D i
    change (x i)⁻¹ * D (x i) = 0
    have hD : D (x i) = 0 := by simpa using D.map_algebraMap (x i)
    rw [hD, mul_zero]
  have hi : Function.Injective ((⊥ : Submodule K (Fin 4 → K)).mkQ.domRestrict
      (LinearMap.ker (logarithmicLinearForm (F := K) c))) := by
    have hq : Function.Injective (⊥ : Submodule K (Fin 4 → K)).mkQ := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
    exact hq.comp (LinearMap.ker (logarithmicLinearForm (F := K) c)).injective_subtype
  rw [hT, LinearMap.finrank_range_of_inj hi]
  have hω : logarithmicLinearForm (F := K) c ≠ 0 := by
    intro h
    have hh := LinearMap.congr_fun h (Pi.single (0 : Fin 4) 1)
    simp [logarithmicLinearForm_apply, Pi.single_apply] at hh
    exact hc.ne_zero 0 hh
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hω
  have hd : Module.finrank K (Fin 4 → K) = 4 := by simp
  omega



theorem logarithmicTangentMap_injective_laurent_quotient
    {K ι : Type*} [Field K]
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime] :
    Function.Injective (logarithmicTangentMap (k := K)
      (fun i ↦ algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1)))) := by
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let q : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] FractionRing B :=
    (IsScalarTower.toAlgHom K B (FractionRing B)).comp (Ideal.Quotient.mkₐ K P)
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro D hD
  rw [LinearMap.mem_ker] at hD
  apply WeightedTorusJets.derivation_laurent_fraction_eq_zero P D
  intro i
  have hi := congrFun hD i
  have hcoord : q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ≠ 0 :=
    ((Group.isUnit (Multiplicative.ofAdd (Finsupp.single i 1))).map
      (q.toMonoidHom.comp (AddMonoidAlgebra.of K (ι →₀ ℤ)))).ne_zero
  change (q (AddMonoidAlgebra.single (Finsupp.single i 1) 1))⁻¹ *
    D (q (AddMonoidAlgebra.single (Finsupp.single i 1) 1)) = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero hcoord)



theorem logarithmicHyperplane_generic_normal_rank_eq_codim
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (P : Ideal (AddMonoidAlgebra K (Fin 4 →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P))
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let A := AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P
    let F := FractionRing A
    let x := fun i ↦ algebraMap _ F
      (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
    let T := LinearMap.range (logarithmicTangentMap (k := K) x)
    finrank F (LinearMap.range
      (T.mkQ.domRestrict (LinearMap.ker (logarithmicLinearForm c)))) =
        4 - ((ringKrullDim A).unbotD 0).toNat := by
  dsimp only
  let A := AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P
  let F := FractionRing A
  have := WeightedTorusJets.laurent_finiteType (K := K) (ι := Fin 4)
  have hd := ringKrullDim_eq_finrank_derivation (K := K) (A := A) (F := F)
  let x := fun i ↦ algebraMap _ F
    (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
  have hn := (logarithmicForm_ne_zero_iff_tangent_not_le c x).mp
    (logarithmicForm_ne_zero_on_torus_subvariety (K := K) (ι := Fin 4) P hdim c hc)
  have hr := finrank_normal_image_of_not_le (logarithmicLinearForm (F := F) c)
    (LinearMap.range (logarithmicTangentMap (k := K) x)) hn
  rw [LinearMap.finrank_range_of_inj
    (logarithmicTangentMap_injective_laurent_quotient P)] at hr
  dsimp only [A, F] at hd
  simpa [hd] using hr



theorem logarithmic_form_lemma_exact
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    (∀ (P : Ideal (AddMonoidAlgebra K (Fin 4 →₀ ℤ))) (hP : P.IsPrime),
      letI := hP
      0 < ringKrullDim (AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P) →
      let A := AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸ P
      let F := FractionRing A
      let x := fun i ↦ algebraMap _ F
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
      let T := LinearMap.range (logarithmicTangentMap (k := K) x)
      logarithmicForm c x ≠ 0 ∧
      Module.finrank F (LinearMap.range
        (T.mkQ.domRestrict (LinearMap.ker (logarithmicLinearForm c)))) =
          4 - ((ringKrullDim A).unbotD 0).toNat) ∧
    ∀ y : Fin 4 → Kˣ,
      Module.finrank K (LinearMap.range
        ((LinearMap.range (logarithmicTangentMap (k := K) (fun i ↦ (y i : K)))).mkQ.domRestrict
          (LinearMap.ker (logarithmicLinearForm (F := K) c)))) = 3 := by
  constructor
  · intro P hP hdim
    let := hP
    exact ⟨logarithmicForm_ne_zero_on_torus_subvariety (K := K) (ι := Fin 4) P hdim c hc,
      logarithmicHyperplane_generic_normal_rank_eq_codim P hdim c hc⟩
  · intro y
    exact logarithmicHyperplane_normal_rank_at_point (fun i ↦ (y i : K)) c hc

end WeightedTorusJets.Geometry

end

open Module CategoryTheory _root_.AlgebraicGeometry _root_.OAI.SiegelZeros.AlgebraicGeometry
open scoped BigOperators TensorProduct

end SiegelZeros

end OAI
