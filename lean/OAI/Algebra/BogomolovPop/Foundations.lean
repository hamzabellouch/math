import Mathlib

namespace OAI

/-! Literal Galois objects, quotient topology and continuous ell-adic actions. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

def proEllKernel (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ (H : OpenNormalSubgroup G) (_ : IsPGroup ell (G ⧸ H.toSubgroup)), H.toSubgroup

instance proEllKernel_normal (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    (proEllKernel ell G).Normal := by
  unfold proEllKernel
  exact Subgroup.normal_iInf_normal fun H =>
    Subgroup.normal_iInf_normal fun _ => H.isNormal'

abbrev ProEll (ell : ℕ) (F : Type*) [Field F] :=
  Field.absoluteGaloisGroup F ⧸ proEllKernel ell (Field.absoluteGaloisGroup F)

def closedGammaThree (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup G :=
  (⁅(commutator G).topologicalClosure, (⊤ : Subgroup G)⁆).topologicalClosure

instance closedGammaThree_normal (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : (closedGammaThree G).Normal := by
  unfold closedGammaThree
  exact Subgroup.is_normal_topologicalClosure _

abbrev PiA (ell : ℕ) (F : Type*) [Field F] := TopologicalAbelianization (ProEll ell F)

abbrev PiC (ell : ℕ) (F : Type*) [Field F] := ProEll ell F ⧸ closedGammaThree (ProEll ell F)

theorem closedGammaThree_le (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : closedGammaThree G ≤ (commutator G).topologicalClosure := by
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_left _ _)
    (Subgroup.isClosed_topologicalClosure _)

def centralProjection (ell : ℕ) (F : Type*) [Field F] : PiC ell F →* PiA ell F :=
  QuotientGroup.map _ _ (MonoidHom.id _) (closedGammaThree_le _)

abbrev Delta (ell : ℕ) (F : Type*) [Field F] := (centralProjection ell F).ker

def sourceCommutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

def abelianLift (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) : ProEll ell F :=
  Quotient.out x

theorem abelianLift_spec (ell : ℕ) (F : Type*) [Field F] (x : PiA ell F) :
    QuotientGroup.mk' _ (abelianLift ell F x) = x := Quotient.out_eq x

def bracket (ell : ℕ) (F : Type*) [Field F] (x y : PiA ell F) : Delta ell F :=
  ⟨QuotientGroup.mk' _ (sourceCommutator (abelianLift ell F x) (abelianLift ell F y)), by
    change centralProjection ell F _ = 1
    simp only [centralProjection, sourceCommutator, map_mul, map_inv]
    simp [mul_comm]⟩

def BracketCompatible {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (φ : PiA ell L ≃ₜ* PiA ell K) : Prop :=
  ∃ ψ : Delta ell L ≃ₜ* Delta ell K,
    ∀ σ τ, ψ (bracket ell L σ τ) = bracket ell K (φ σ) (φ τ)

abbrev PerfectFieldClosure (F : Type*) [Field F] := perfectClosure F (AlgebraicClosure F)

def PerfectIsom (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  { α : PerfectFieldClosure K ≃+* PerfectFieldClosure L //
    α '' Set.range (algebraMap k (PerfectFieldClosure K)) =
      Set.range (algebraMap l (PerfectFieldClosure L)) }

def FrobeniusStep {k K l L : Type*} [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] (α β : PerfectIsom k K l L) : Prop :=
  ∃ p : ℕ, p.Prime ∧ (p : L) = 0 ∧
    ∀ x : PerfectFieldClosure K, β.1 x = (α.1 x) ^ p

abbrev IsomF (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [Algebra k K] [Algebra l L] :=
  Quotient (Relation.EqvGen.setoid (FrobeniusStep (k := k) (K := K) (l := l) (L := L)))

abbrev IsomC (ell : ℕ) (K L : Type*) [Field K] [Field L] :=
  {φ : PiA ell L ≃ₜ* PiA ell K // BracketCompatible φ}

def ScalarStep {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) : Prop :=
  ∃ u : (PadicInt ell)ˣ, ∀ x : PiA ell L,
    Filter.Tendsto (fun n : ℕ => (φ.1 x) ^ PadicInt.appr (u : PadicInt ell) n)
      Filter.atTop (nhds (χ.1 x))

abbrev IsomCUnits (ell : ℕ) [Fact ell.Prime] (K L : Type*) [Field K] [Field L] :=
  Quotient (Relation.EqvGen.setoid (ScalarStep (ell := ell) (K := K) (L := L)))

def absoluteToPiA (ell : ℕ) (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* PiA ell F :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

def absoluteAction {F : Type*} [Field F] (σ : Field.absoluteGaloisGroup F)
    (x : AlgebraicClosure F) : AlgebraicClosure F := by
  change AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F at σ
  exact σ x

def PullbackGraph {ell : ℕ} {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (φ : IsomC ell K L) : Prop :=
  ∃ β : AlgebraicClosure K ≃+* AlgebraicClosure L,
    (∀ x : PerfectFieldClosure K, β x = ((α.1 x : PerfectFieldClosure L) :
      AlgebraicClosure L)) ∧
    ∀ σ : Field.absoluteGaloisGroup L, ∃ τ : Field.absoluteGaloisGroup K,
      (∀ x : AlgebraicClosure K,
        β (absoluteAction τ x) = absoluteAction σ (β x)) ∧
      φ.1 (absoluteToPiA ell L σ) = absoluteToPiA ell K τ

def PhiGraph {ell : ℕ} [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (a : IsomF k K l L) (b : IsomCUnits ell K L) : Prop :=
  ∃ α : PerfectIsom k K l L, ∃ φ : IsomC ell K L,
    Quotient.mk _ α = a ∧ Quotient.mk _ φ = b ∧ PullbackGraph α φ

def MainStatement (ell : ℕ) [Fact ell.Prime] (k K l L : Type*)
    [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L] : Prop :=
  (ell : k) ≠ 0 → (ell : l) ≠ 0 →
  2 ≤ Algebra.trdeg k K → 2 ≤ Algebra.trdeg l L →
    (∀ a : IsomF k K l L, ∃! b : IsomCUnits ell K L, PhiGraph a b) ∧
    (∀ b : IsomCUnits ell K L, ∃! a : IsomF k K l L, PhiGraph a b)

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

theorem closedCommutator_image_commute {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {z : G}
    (hz : z ∈ (commutator G).topologicalClosure) (g : G) :
    Commute (QuotientGroup.mk' (closedGammaThree G) z)
      (QuotientGroup.mk' (closedGammaThree G) g) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator hz (Subgroup.mem_top g))

theorem quotient_commutator_independent {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {a a' b b' : G}
    (ha : QuotientGroup.mk' (commutator G).topologicalClosure a =
      QuotientGroup.mk' (commutator G).topologicalClosure a')
    (hb : QuotientGroup.mk' (commutator G).topologicalClosure b =
      QuotientGroup.mk' (commutator G).topologicalClosure b') :
    QuotientGroup.mk' (closedGammaThree G) ⁅a, b⁆ =
      QuotientGroup.mk' (closedGammaThree G) ⁅a', b'⁆ := by
  let q := QuotientGroup.mk' (closedGammaThree G)
  have haz : a⁻¹ * a' ∈ (commutator G).topologicalClosure :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact ha)
  have hbz : b⁻¹ * b' ∈ (commutator G).topologicalClosure :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hb)
  have hea : q a' = q a * q (a⁻¹ * a') := by rw [← map_mul]; simp
  have heb : q b' = q b * q (b⁻¹ * b') := by rw [← map_mul]; simp
  change q ⁅a, b⁆ = q ⁅a', b'⁆
  rw [map_commutatorElement, map_commutatorElement, hea, heb]
  have hza : Commute (q (a⁻¹ * a')) (q b * q (b⁻¹ * b')) := by
    rw [← map_mul]
    exact closedCommutator_image_commute haz _
  rw [commutatorElement_mul_left_eq_conj_mul, hza.commutator_eq]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj,
    (closedCommutator_image_commute hbz a).symm.commutator_eq]
  simp [mul_assoc]

end BogomolovPop

namespace BogomolovPop
open scoped commutatorElement

theorem sourceCommutator_independent {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {a a' b b' : G}
    (ha : QuotientGroup.mk' (commutator G).topologicalClosure a =
      QuotientGroup.mk' (commutator G).topologicalClosure a')
    (hb : QuotientGroup.mk' (commutator G).topologicalClosure b =
      QuotientGroup.mk' (commutator G).topologicalClosure b') :
    QuotientGroup.mk' (closedGammaThree G) (sourceCommutator a b) =
      QuotientGroup.mk' (closedGammaThree G) (sourceCommutator a' b') := by
  have ha' : QuotientGroup.mk' (commutator G).topologicalClosure a⁻¹ =
      QuotientGroup.mk' (commutator G).topologicalClosure a'⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv ha
  have hb' : QuotientGroup.mk' (commutator G).topologicalClosure b⁻¹ =
      QuotientGroup.mk' (commutator G).topologicalClosure b'⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hb
  simpa only [commutatorElement_def, inv_inv, sourceCommutator] using
    quotient_commutator_independent ha' hb'

theorem bracket_eq_of_lifts (ell : ℕ) (F : Type*) [Field F]
    (x y : PiA ell F) (a b : ProEll ell F)
    (ha : QuotientGroup.mk' _ a = x) (hb : QuotientGroup.mk' _ b = y) :
    (bracket ell F x y : PiC ell F) =
      QuotientGroup.mk' _ (sourceCommutator a b) := by
  exact sourceCommutator_independent ((abelianLift_spec ell F x).trans ha.symm)
    ((abelianLift_spec ell F y).trans hb.symm)

theorem quotient_nonarchimedean {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] : NonarchimedeanGroup (G ⧸ N) where
  is_nonarchimedean U hU := by
    let q := QuotientGroup.mk' N
    have hpre : q ⁻¹' U ∈ nhds (1 : G) := by
      apply (QuotientGroup.continuous_mk.continuousAt :
        ContinuousAt (fun x : G => (QuotientGroup.mk x : G ⧸ N)) 1).preimage_mem_nhds
      simpa using hU
    obtain ⟨V, hV, hVo, h1V⟩ := mem_nhds_iff.mp hpre
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1V
    refine ⟨{ H.toSubgroup.map q with
      isOpen' := QuotientGroup.isOpenMap_coe _ H.isOpen }, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hV (hH hg)

theorem proEllKernel_isClosed (ell : ℕ) (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : IsClosed (proEllKernel ell G : Set G) := by
  simp only [proEllKernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun H => isClosed_iInter fun _ => H.toOpenSubgroup.isClosed

theorem restrictScalarsHom_continuous {F P A : Type*} [Field F] [Field P] [Field A]
    [Algebra F P] [Algebra P A] [Algebra F A] [IsScalarTower F P A]
    [Algebra.IsAlgebraic P A] :
    Continuous (AlgEquiv.restrictScalarsHom F : (A ≃ₐ[P] A) →* (A ≃ₐ[F] A)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, heU⟩ := hU
  let : FiniteDimensional F E := hE
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := F) (A := E))
  let S : Set A := (algebraMap E A) '' (s : Set E)
  have hS : S.Finite := s.finite_toSet.image _
  let : Finite S := hS.to_subtype
  let E' := IntermediateField.adjoin P S
  have : FiniteDimensional P E' := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := P) x).isIntegral)
  apply (krullTopology_mem_nhds_one_iff P A _).mpr
  refine ⟨E', inferInstance, ?_⟩
  intro σ hσ
  apply heU
  change (σ.restrictScalars F) ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have heq : ((σ.restrictScalars F).toAlgHom.comp E.val) = E.val := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro x hx
    exact ((IntermediateField.mem_fixingSubgroup_iff E' σ).mp hσ) _
      (IntermediateField.subset_adjoin P S ⟨x, hx, rfl⟩)
  intro x hx
  exact DFunLike.congr_fun heq ⟨x, hx⟩

theorem restrictScalarsHom_surjective_of_purelyInseparable {F P A : Type*}
    [Field F] [Field P] [Field A] [Algebra F P] [Algebra P A] [Algebra F A]
    [IsScalarTower F P A] [IsPurelyInseparable F P] :
    Function.Surjective (AlgEquiv.restrictScalarsHom F : (A ≃ₐ[P] A) →* (A ≃ₐ[F] A)) := by
  intro σ
  have hfix : σ.toAlgHom.comp (IsScalarTower.toAlgHom F P A) =
      IsScalarTower.toAlgHom F P A := Subsingleton.elim _ _
  refine ⟨{ σ.toRingEquiv with commutes' := fun p => DFunLike.congr_fun hfix p }, ?_⟩
  ext x
  rfl

theorem absoluteGaloisGroup_compact (F : Type*) [Field F] :
    CompactSpace (Field.absoluteGaloisGroup F) := by
  let P := perfectClosure F (AlgebraicClosure F)
  have : Algebra.IsAlgebraic P (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.tower_top (K := F) P
  have : Normal P (AlgebraicClosure F) := ⟨fun x => IsAlgClosed.splits _⟩
  have : IsGalois P (AlgebraicClosure F) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  change CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  exact Function.Surjective.compactSpace
    (restrictScalarsHom_continuous (F := F) (P := P) (A := AlgebraicClosure F))
    (restrictScalarsHom_surjective_of_purelyInseparable (F := F) (P := P)
      (A := AlgebraicClosure F))

theorem absoluteGaloisGroup_nonarchimedean (F : Type*) [Field F] :
    NonarchimedeanGroup (Field.absoluteGaloisGroup F) where
  is_nonarchimedean U hU := by
    change U ∈ nhds (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) at hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F (AlgebraicClosure F) U).mp hU
    let := hE
    exact ⟨{ E.fixingSubgroup with isOpen' := E.fixingSubgroup_isOpen }, hEU⟩

instance (F : Type*) [Field F] : CompactSpace (Field.absoluteGaloisGroup F) :=
  absoluteGaloisGroup_compact F

instance (F : Type*) [Field F] : NonarchimedeanGroup (Field.absoluteGaloisGroup F) :=
  absoluteGaloisGroup_nonarchimedean F

instance (F : Type*) [Field F] : T2Space (Field.absoluteGaloisGroup F) := by
  change T2Space (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

instance ProEll.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (ProEll ell F) := by
  have := proEllKernel_isClosed ell (Field.absoluteGaloisGroup F)
  infer_instance

instance ProEll.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (ProEll ell F) := by
  have := quotient_nonarchimedean (proEllKernel ell (Field.absoluteGaloisGroup F))
  infer_instance

instance PiA.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (PiA ell F) := by
  have := Subgroup.isClosed_topologicalClosure (commutator (ProEll ell F))
  infer_instance

instance PiA.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (PiA ell F) := by
  have := quotient_nonarchimedean (commutator (ProEll ell F)).topologicalClosure
  infer_instance

instance PiC.t2Space (ell : ℕ) (F : Type*) [Field F] : T2Space (PiC ell F) := by
  have : IsClosed (closedGammaThree (ProEll ell F) : Set (ProEll ell F)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

instance PiC.totallyDisconnectedSpace (ell : ℕ) (F : Type*) [Field F] :
    TotallyDisconnectedSpace (PiC ell F) := by
  have := quotient_nonarchimedean (closedGammaThree (ProEll ell F))
  infer_instance

open Filter

def EllQuotients (ell : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :=
  {H : OpenNormalSubgroup G // IsPGroup ell (G ⧸ H.toSubgroup)}

instance ellQuotient_normal {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (H : EllQuotients ell G) : H.1.toSubgroup.Normal := H.1.isNormal'

theorem proEllKernel_le {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (H : EllQuotients ell G) : proEllKernel ell G ≤ H.1.toSubgroup := by
  exact iInf_le_of_le H.1 (iInf_le _ H.2)

def proEllEval {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G] :
    (G ⧸ proEllKernel ell G) →* (∀ H : EllQuotients ell G, G ⧸ H.1.toSubgroup) :=
  MonoidHom.pi fun H => QuotientGroup.map _ _ (MonoidHom.id G) (proEllKernel_le H)

theorem proEllEval_injective {ell : ℕ} {G : Type*} [Group G] [TopologicalSpace G] :
    Function.Injective (proEllEval (ell := ell) (G := G)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  induction z using QuotientGroup.induction_on with | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    simp only [proEllKernel, Subgroup.mem_iInf]
    intro H hH
    exact (QuotientGroup.eq_one_iff x).mp (congrFun hz ⟨H, hH⟩)

theorem proEllEval_continuous {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] : Continuous (proEllEval (ell := ell) (G := G)) := by
  apply continuous_pi
  intro H
  apply (QuotientGroup.isQuotientMap_mk (proEllKernel ell G)).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

theorem proEllEval_isClosedEmbedding {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] :
    Topology.IsClosedEmbedding (proEllEval (ell := ell) (G := G)) := by
  have (H : EllQuotients ell G) : DiscreteTopology (G ⧸ H.1.toSubgroup) :=
    QuotientGroup.discreteTopology H.1.isOpen
  exact proEllEval_continuous.isClosedEmbedding proEllEval_injective

theorem proEll_pow_tendsto_one {ell : ℕ} {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (x : G ⧸ proEllKernel ell G) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  apply proEllEval_isClosedEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro H
  obtain ⟨k, hk⟩ := H.2 (proEllEval x H)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  change (1 : G ⧸ H.1.toSubgroup) = proEllEval (x ^ ell ^ n) H
  rw [map_pow]
  change 1 = (proEllEval x H) ^ ell ^ n
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, pow_mul, hk, one_pow]

theorem isPGroup_of_proEll_image {ell : ℕ} {G A Q : Type*} [Group G] [Group A] [Group Q]
    [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace Q]
    [IsTopologicalGroup G] [CompactSpace G] [DiscreteTopology Q]
    (f : (G ⧸ proEllKernel ell G) →* A) (hf : Continuous f) (hs : Function.Surjective f)
    (q : A →* Q) (hq : Continuous q) (hqs : Function.Surjective q) : IsPGroup ell Q := by
  intro y
  obtain ⟨a, rfl⟩ := hqs y
  obtain ⟨x, rfl⟩ := hs a
  have ht := (hq.tendsto (f 1)).comp ((hf.tendsto 1).comp (proEll_pow_tendsto_one x))
  simp only [Function.comp_def, map_one, map_pow] at ht
  have he : ∀ᶠ n : ℕ in atTop, q (f x) ^ ell ^ n = 1 :=
    (tendsto_pure.mp (by simpa only [nhds_discrete, QuotientAddGroup.mk'_apply] using ht))
  exact he.exists

variable {ell : ℕ} [Fact ell.Prime]

theorem continuous_padic_toZModPow (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := ell) n) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, (nhds_discrete (ZMod (ell ^ n))), tendsto_pure]
  have hpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr (Fact.out : ell.Prime).pos
  have hr : (ell : ℝ) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ (ne_of_gt hpos)
  have hb := (IsUltrametricDist.isOpen_closedBall (0 : PadicInt ell) hr).mem_nhds
    (Metric.mem_closedBall_self (le_of_lt (by positivity : (0 : ℝ) < ell ^ (-(n : ℤ)))))
  filter_upwards [hb] with x hx
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

omit [Fact ell.Prime] in
theorem finite_abelian_ell_exponent {A : Type*} [AddCommGroup A] [Finite A]
    (h : IsPGroup ell (Multiplicative A)) : ∃ n, ∀ x : A, ell ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp h
  exact ⟨n, fun x => congrArg Multiplicative.toAdd (hn (Multiplicative.ofAdd x))⟩

abbrev finiteEllModule {A : Type*} [AddCommGroup A] [Finite A]
    (h : IsPGroup ell (Multiplicative A)) : Module (PadicInt ell) A := by
  let n := (finite_abelian_ell_exponent h).choose
  letI := AddCommGroup.zmodModule (finite_abelian_ell_exponent h).choose_spec
  exact Module.compHom A (PadicInt.toZModPow n)

theorem finiteEllModule_continuous {A : Type*} [AddCommGroup A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (h : IsPGroup ell (Multiplicative A)) :
    letI := finiteEllModule h
    ContinuousSMul (PadicInt ell) A := by
  let n := (finite_abelian_ell_exponent h).choose
  let := AddCommGroup.zmodModule (finite_abelian_ell_exponent h).choose_spec
  let : ContinuousSMul (ZMod (ell ^ n)) A := ⟨continuous_of_discreteTopology⟩
  exact MulAction.continuousSMul_compHom (continuous_padic_toZModPow n)

section Profinite
variable {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [NonarchimedeanAddGroup A] [CompactSpace A] [T2Space A]

abbrev AllLevels (A : Type*) [AddCommGroup A] [TopologicalSpace A] :=
  ∀ H : OpenAddSubgroup A, A ⧸ H.toAddSubgroup

instance levelDiscrete (H : OpenAddSubgroup A) :
    DiscreteTopology (A ⧸ H.toAddSubgroup) := QuotientAddGroup.discreteTopology H.isOpen

instance levelFinite (H : OpenAddSubgroup A) :
    Finite (A ⧸ H.toAddSubgroup) := finite_of_compact_of_discrete

def levelEval : A →+ AllLevels A :=
  AddMonoidHom.pi fun H => QuotientAddGroup.mk' H.toAddSubgroup

omit [CompactSpace A] in
theorem levelEval_injective : Function.Injective (levelEval (A := A)) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  rw [AddSubgroup.mem_bot]
  by_contra h
  have hU : {x}ᶜ ∈ nhds (0 : A) := isClosed_singleton.isOpen_compl.mem_nhds (by simpa using Ne.symm h)
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hxH : x ∈ H := (QuotientAddGroup.eq_zero_iff x).mp (congrFun hx H)
  exact hH hxH (Set.mem_singleton x)

omit [NonarchimedeanAddGroup A] [CompactSpace A] [T2Space A] in
theorem levelEval_continuous : Continuous (levelEval (A := A)) :=
  continuous_pi fun _ => QuotientAddGroup.continuous_mk

theorem levelEval_closedEmbedding :
    Topology.IsClosedEmbedding (levelEval (A := A)) :=
  levelEval_continuous.isClosedEmbedding levelEval_injective

def AllLevelsEll (ell : ℕ) (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Prop :=
  ∀ H : OpenAddSubgroup A, IsPGroup ell (Multiplicative (A ⧸ H.toAddSubgroup))

variable [hA : Fact (AllLevelsEll ell A)]

instance levelsModule : Module (PadicInt ell) (AllLevels A) := by
  letI (H : OpenAddSubgroup A) := finiteEllModule (hA.out H)
  exact Pi.module _ _ _

omit [T2Space A] in
theorem levels_continuous : ContinuousSMul (PadicInt ell) (AllLevels A) := by
  let (H : OpenAddSubgroup A) := finiteEllModule (hA.out H)
  let (H : OpenAddSubgroup A) := finiteEllModule_continuous (hA.out H)
  infer_instance

def levelImage : Submodule (PadicInt ell) (AllLevels A) where
  carrier := Set.range (levelEval (A := A))
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    let := levels_continuous (ell := ell) (A := A)
    rintro c _ ⟨x, rfl⟩
    refine (PadicInt.denseRange_natCast (p := ell)).induction_on c ?_ ?_
    · exact levelEval_closedEmbedding.isClosed_range.preimage (continuous_id.smul continuous_const)
    · intro n
      exact ⟨n • x, by simp [Nat.cast_smul_eq_nsmul]⟩

def levelImageEquiv : A ≃+ levelImage (ell := ell) (A := A) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨levelEval x, ⟨x, rfl⟩⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ x y) } : A →+ levelImage (ell := ell))
    ⟨fun _ _ h => levelEval_injective (congrArg Subtype.val h), by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩⟩

abbrev abelianEllModule : Module (PadicInt ell) A :=
  (levelImageEquiv (ell := ell) (A := A)).module (PadicInt ell)

theorem levelEval_smul (c : PadicInt ell) (x : A) :
    letI := abelianEllModule (ell := ell) (A := A)
    levelEval (c • x) = c • levelEval x := by
  let := abelianEllModule (ell := ell) (A := A)
  exact congrArg Subtype.val
    (((levelImageEquiv (ell := ell) (A := A)).linearEquiv (PadicInt ell)).map_smul c x)

theorem abelianEllModule_continuous :
    letI := abelianEllModule (ell := ell) (A := A)
    ContinuousSMul (PadicInt ell) A := by
  let := abelianEllModule (ell := ell) (A := A)
  let := levels_continuous (ell := ell) (A := A)
  constructor
  apply levelEval_closedEmbedding.isEmbedding.continuous_iff.mpr
  change Continuous (fun z : PadicInt ell × A => levelEval (z.1 • z.2))
  simp_rw [levelEval_smul]
  exact continuous_fst.smul (levelEval_continuous.comp continuous_snd)

end Profinite

theorem padic_appr_tendsto (c : PadicInt ell) :
    Tendsto (fun n : ℕ => (PadicInt.appr c n : PadicInt ell)) atTop (nhds c) := by
  have hpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr (Fact.out : ell.Prime).pos
  have hlt : 1 < (ell : ℝ) := by exact_mod_cast (Fact.out : ell.Prime).one_lt
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    have hb := (PadicInt.norm_le_pow_iff_mem_span_pow (c - (PadicInt.appr c n : PadicInt ell)) n).mpr
      (PadicInt.appr_spec n c)
    simpa only [dist_eq_norm, norm_sub_rev, zpow_neg, zpow_natCast, inv_pow] using hb
  · simpa only [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpos.le) (inv_lt_one_of_one_lt₀ hlt)

theorem continuous_addHom_padic_linear {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    [Module (PadicInt ell) A] [Module (PadicInt ell) B]
    [ContinuousSMul (PadicInt ell) A] [ContinuousSMul (PadicInt ell) B]
    (f : A →+ B) (hf : Continuous f) (c : PadicInt ell) (x : A) :
    f (c • x) = c • f x := by
  refine (PadicInt.denseRange_natCast (p := ell)).induction_on c ?_ ?_
  · exact isClosed_eq (hf.comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
  · intro n
    simp only [Nat.cast_smul_eq_nsmul, map_nsmul]

theorem padic_appr_smul_tendsto {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [Module (PadicInt ell) A] [ContinuousSMul (PadicInt ell) A]
    (c : PadicInt ell) (x : A) :
    Tendsto (fun n : ℕ => PadicInt.appr c n • x) atTop (nhds (c • x)) := by
  simpa only [Nat.cast_smul_eq_nsmul] using (padic_appr_tendsto c).smul_const x

end BogomolovPop

end
end

end OAI
