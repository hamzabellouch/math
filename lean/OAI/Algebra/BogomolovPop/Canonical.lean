import Mathlib
import OAI.Algebra.BogomolovPop.Foundations

namespace OAI

/-! Canonical Galois transport, bracket compatibility and quotient-map well-definedness. -/

noncomputable section
open scoped Topology

namespace BogomolovPop
open scoped Topology commutatorElement
open Filter

instance PiA.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (PiA ell F) :=
  quotient_nonarchimedean (commutator (ProEll ell F)).topologicalClosure

instance additive_nonarchimedean (G : Type*) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] : NonarchimedeanAddGroup (Additive G) where
  is_nonarchimedean U hU := by
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (G := G) U hU
    exact ⟨{ V.toSubgroup.toAddSubgroup with isOpen' := V.isOpen }, hV⟩

instance PiA.allLevelsEll (ell : ℕ) (F : Type*) [Field F] :
    Fact (AllLevelsEll ell (Additive (PiA ell F))) := ⟨by
  intro H
  let q : PiA ell F →* Multiplicative (Additive (PiA ell F) ⧸ H.toAddSubgroup) :=
    { toFun := fun x => Multiplicative.ofAdd (QuotientAddGroup.mk (Additive.ofMul x))
      map_one' := by rfl
      map_mul' := fun x y => by rfl }
  have hq : Continuous q :=
    (QuotientAddGroup.continuous_mk :
      Continuous (QuotientAddGroup.mk : Additive (PiA ell F) → Additive (PiA ell F) ⧸ H.toAddSubgroup))
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
    exact ⟨Additive.toMul x, hx⟩
  exact isPGroup_of_proEll_image (QuotientGroup.mk' _) QuotientGroup.continuous_mk
    QuotientGroup.mk_surjective q hq hqs⟩

instance PiA.padicModule (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    Module (PadicInt ell) (Additive (PiA ell F)) := abelianEllModule

instance PiA.padicContinuousSMul (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    ContinuousSMul (PadicInt ell) (Additive (PiA ell F)) := abelianEllModule_continuous

instance PiA.additiveT2 (ell : ℕ) (F : Type*) [Field F] :
    T2Space (Additive (PiA ell F)) := PiA.t2Space ell F

theorem PiA.continuous_linear {ell : ℕ} [Fact ell.Prime] {F E : Type*} [Field F] [Field E]
    (f : PiA ell F →* PiA ell E) (hf : Continuous f) (c : PadicInt ell) (x : PiA ell F) :
    Additive.ofMul (f (Additive.toMul (c • Additive.ofMul x))) = c • Additive.ofMul (f x) :=
  continuous_addHom_padic_linear f.toAdditive hf c (Additive.ofMul x)

theorem scalarStep_iff_unit {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) :
    ScalarStep φ χ ↔ ∃ u : (PadicInt ell)ˣ, ∀ x : PiA ell L,
      Additive.ofMul (χ.1 x) = (u : PadicInt ell) • Additive.ofMul (φ.1 x) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    exact tendsto_nhds_unique (hu x) (padic_appr_smul_tendsto (u : PadicInt ell) (Additive.ofMul (φ.1 x)))
  · rintro ⟨u, hu⟩
    refine ⟨u, fun x => ?_⟩
    have ht := padic_appr_smul_tendsto (u : PadicInt ell) (Additive.ofMul (φ.1 x))
    rw [← hu x] at ht
    exact ht

theorem delta_commute {ell : ℕ} {F : Type*} [Field F]
    (z : Delta ell F) (x : PiC ell F) : Commute (z : PiC ell F) x := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) z.1
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) x
  rw [← ha]
  apply closedCommutator_image_commute
  apply (QuotientGroup.eq_one_iff a).mp
  have hz := z.property
  rw [← ha] at hz
  exact hz

instance Delta.commGroup (ell : ℕ) (F : Type*) [Field F] : CommGroup (Delta ell F) :=
  { (inferInstance : Group (Delta ell F)) with
    mul_comm := fun z x => Subtype.ext (delta_commute z x).eq }

theorem centralProjection_continuous (ell : ℕ) (F : Type*) [Field F] :
    Continuous (centralProjection ell F) := by
  apply (QuotientGroup.isQuotientMap_mk (closedGammaThree (ProEll ell F))).continuous_iff.mpr
  exact QuotientGroup.continuous_mk

instance Delta.compactSpace (ell : ℕ) (F : Type*) [Field F] : CompactSpace (Delta ell F) := by
  have h : IsClosed ((centralProjection ell F).ker : Set (PiC ell F)) :=
    isClosed_singleton.preimage (centralProjection_continuous ell F)
  exact isCompact_iff_compactSpace.mp h.isCompact

instance PiC.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (PiC ell F) := quotient_nonarchimedean _

instance Delta.nonarchimedean (ell : ℕ) (F : Type*) [Field F] :
    NonarchimedeanGroup (Delta ell F) where
  is_nonarchimedean U hU := by
    obtain ⟨V, hV, hVo, h1V⟩ := mem_nhds_iff.mp hU
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1V
    exact ⟨H.toOpenSubgroup, hH.trans hV⟩

theorem PiC.pow_tendsto_one {ell : ℕ} {F : Type*} [Field F] (x : PiC ell F) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (closedGammaThree (ProEll ell F)) x
  have hq : Continuous (QuotientGroup.mk' (closedGammaThree (ProEll ell F))) :=
    QuotientGroup.continuous_mk
  simpa only [map_one, Function.comp_def, map_pow] using
    (hq.tendsto (1 : ProEll ell F)).comp (proEll_pow_tendsto_one a)

theorem Delta.pow_tendsto_one {ell : ℕ} {F : Type*} [Field F] (x : Delta ell F) :
    Tendsto (fun n : ℕ => x ^ ell ^ n) atTop (nhds 1) := by
  apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
  exact PiC.pow_tendsto_one x.1

instance Delta.allLevelsEll (ell : ℕ) (F : Type*) [Field F] :
    Fact (AllLevelsEll ell (Additive (Delta ell F))) := ⟨by
  intro H y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd y)
  have hq : Continuous (QuotientAddGroup.mk' H.toAddSubgroup) :=
    QuotientAddGroup.continuous_mk
  have hx : Tendsto (fun n : ℕ => ell ^ n • x) atTop (nhds 0) :=
    Delta.pow_tendsto_one (Additive.toMul x)
  have ht := (hq.tendsto (0 : Additive (Delta ell F))).comp hx
  simp only [Function.comp_def, map_zero] at ht
  have he : ∀ᶠ n : ℕ in atTop,
      (QuotientAddGroup.mk (ell ^ n • x) : Additive (Delta ell F) ⧸ H.toAddSubgroup) = 0 := by
    exact tendsto_pure.mp (by simpa only [nhds_discrete, QuotientAddGroup.mk'_apply] using ht)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn⟩⟩

instance Delta.additiveT2 (ell : ℕ) (F : Type*) [Field F] :
    T2Space (Additive (Delta ell F)) := inferInstanceAs (T2Space (Delta ell F))

instance Delta.padicModule (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    Module (PadicInt ell) (Additive (Delta ell F)) := abelianEllModule

instance Delta.padicContinuousSMul (ell : ℕ) [Fact ell.Prime] (F : Type*) [Field F] :
    ContinuousSMul (PadicInt ell) (Additive (Delta ell F)) := abelianEllModule_continuous

theorem Delta.continuous_linear {ell : ℕ} [Fact ell.Prime] {F E : Type*} [Field F] [Field E]
    (f : Delta ell F →* Delta ell E) (hf : Continuous f) (c : PadicInt ell) (x : Delta ell F) :
    Additive.ofMul (f (Additive.toMul (c • Additive.ofMul x))) = c • Additive.ofMul (f x) :=
  continuous_addHom_padic_linear f.toAdditive hf c (Additive.ofMul x)

theorem map_sourceCommutator {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) :
    f (sourceCommutator a b) = sourceCommutator (f a) (f b) := by
  simp only [sourceCommutator, map_mul, map_inv]

theorem sourceCommutator_mul_left_of_central {G : Type*} [Group G]
    (a b c : G) (h : Commute (sourceCommutator a c) b) :
    sourceCommutator (a * b) c = sourceCommutator a c * sourceCommutator b c := by
  calc
    sourceCommutator (a * b) c = b⁻¹ * sourceCommutator a c * b * sourceCommutator b c := by
      simp only [sourceCommutator]
      group
    _ = sourceCommutator a c * sourceCommutator b c := by
      rw [h.symm.inv_left.eq]
      simp only [mul_assoc, inv_mul_cancel, one_mul]

theorem bracket_on_lifts {ell : ℕ} {F : Type*} [Field F] (a b : ProEll ell F) :
    (bracket ell F (QuotientGroup.mk' _ a) (QuotientGroup.mk' _ b) : PiC ell F) =
      QuotientGroup.mk' _ (sourceCommutator a b) :=
  bracket_eq_of_lifts ell F _ _ a b rfl rfl

theorem bracket_mul_left {ell : ℕ} {F : Type*} [Field F] (x y z : PiA ell F) :
    bracket ell F (x * y) z = bracket ell F x z * bracket ell F y z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator (ProEll ell F)).topologicalClosure x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (commutator (ProEll ell F)).topologicalClosure y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (commutator (ProEll ell F)).topologicalClosure z
  apply Subtype.ext
  change (bracket ell F _ _ : PiC ell F) =
    (bracket ell F _ _ : PiC ell F) * (bracket ell F _ _ : PiC ell F)
  rw [← map_mul, bracket_on_lifts, bracket_on_lifts, bracket_on_lifts]
  simp only [map_sourceCommutator, map_mul]
  apply sourceCommutator_mul_left_of_central
  rw [← map_sourceCommutator]
  apply closedCommutator_image_commute
  apply Subgroup.le_topologicalClosure
  have hm : ⁅a⁻¹, c⁻¹⁆ ∈ commutator (ProEll ell F) := by
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet _ _)
  simpa only [sourceCommutator, commutatorElement_def, inv_inv] using hm

theorem bracket_swap {ell : ℕ} {F : Type*} [Field F] (x y : PiA ell F) :
    bracket ell F y x = (bracket ell F x y)⁻¹ := by
  apply Subtype.ext
  change QuotientGroup.mk' _ _ = (QuotientGroup.mk' _ _)⁻¹
  rw [← map_inv]
  congr 1
  simp only [sourceCommutator]
  group

theorem bracket_mul_right {ell : ℕ} {F : Type*} [Field F] (x y z : PiA ell F) :
    bracket ell F x (y * z) = bracket ell F x y * bracket ell F x z := by
  rw [bracket_swap, bracket_mul_left, mul_inv_rev, ← bracket_swap, ← bracket_swap]
  exact mul_comm _ _

theorem bracket_alternating {ell : ℕ} {F : Type*} [Field F] (x : PiA ell F) :
    bracket ell F x x = 1 := by
  apply Subtype.ext
  change QuotientGroup.mk' _ _ = 1
  simp [sourceCommutator]

theorem bracket_one_left {ell : ℕ} {F : Type*} [Field F] (x : PiA ell F) :
    bracket ell F 1 x = 1 := by
  have h := bracket_mul_left (1 : PiA ell F) 1 x
  simp only [one_mul] at h
  exact (mul_left_cancel (a := bracket ell F 1 x) (by simpa using h.symm)).symm

theorem bracket_continuous (ell : ℕ) (F : Type*) [Field F] :
    Continuous (fun z : PiA ell F × PiA ell F => bracket ell F z.1 z.2) := by
  have h : Continuous (fun z : PiA ell F × PiA ell F => (bracket ell F z.1 z.2 : PiC ell F)) := by
    apply ((QuotientGroup.isOpenQuotientMap_mk (N := (commutator (ProEll ell F)).topologicalClosure)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := (commutator (ProEll ell F)).topologicalClosure))).isQuotientMap.continuous_iff.mpr
    have hq : Continuous (QuotientGroup.mk' (closedGammaThree (ProEll ell F))) :=
      QuotientGroup.continuous_mk
    convert hq.comp (((continuous_fst.inv.mul continuous_snd.inv).mul continuous_fst).mul continuous_snd) using 1
    funext z
    exact bracket_on_lifts z.1 z.2
  exact h.subtype_mk _

def bracketLeftHom {ell : ℕ} {F : Type*} [Field F] (y : PiA ell F) :
    PiA ell F →* Delta ell F where
  toFun := fun x => bracket ell F x y
  map_one' := bracket_one_left y
  map_mul' := fun x z => bracket_mul_left x z y

theorem bracket_smul_left {ell : ℕ} [Fact ell.Prime] {F : Type*} [Field F]
    (c : PadicInt ell) (x y : PiA ell F) :
    Additive.ofMul (bracket ell F (Additive.toMul (c • Additive.ofMul x)) y) =
      c • Additive.ofMul (bracket ell F x y) := by
  exact continuous_addHom_padic_linear (bracketLeftHom y).toAdditive
    ((bracket_continuous ell F).comp (continuous_id.prodMk continuous_const)) c (Additive.ofMul x)

def bracketRightHom {ell : ℕ} {F : Type*} [Field F] (x : PiA ell F) :
    PiA ell F →* Delta ell F where
  toFun := fun y => bracket ell F x y
  map_one' := by rw [bracket_swap, bracket_one_left, inv_one]
  map_mul' := fun y z => bracket_mul_right x y z

theorem bracket_smul_right {ell : ℕ} [Fact ell.Prime] {F : Type*} [Field F]
    (c : PadicInt ell) (x y : PiA ell F) :
    Additive.ofMul (bracket ell F x (Additive.toMul (c • Additive.ofMul y))) =
      c • Additive.ofMul (bracket ell F x y) := by
  exact continuous_addHom_padic_linear (bracketRightHom x).toAdditive
    ((bracket_continuous ell F).comp (continuous_const.prodMk continuous_id)) c (Additive.ofMul y)

def unitScalarEquiv {R G : Type*} [CommRing R] [TopologicalSpace R]
    [CommGroup G] [TopologicalSpace G] [Module R (Additive G)]
    [ContinuousSMul R (Additive G)] (u : Rˣ) : G ≃ₜ* G where
  toMulEquiv := (DistribMulAction.toAddEquiv (Additive G) u).toMultiplicative
  continuous_toFun := by
    change Continuous (fun x : Additive G => (u : R) • x)
    exact continuous_const.smul continuous_id
  continuous_invFun := by
    change Continuous (fun x : Additive G => ((u⁻¹ : Rˣ) : R) • x)
    exact continuous_const.smul continuous_id

@[simp] theorem unitScalarEquiv_apply {R G : Type*} [CommRing R] [TopologicalSpace R]
    [CommGroup G] [TopologicalSpace G] [Module R (Additive G)]
    [ContinuousSMul R (Additive G)] (u : Rˣ) (x : G) :
    unitScalarEquiv u x = Additive.toMul ((u : R) • Additive.ofMul x) := rfl

def scalarIsomC {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (u : (PadicInt ell)ˣ) (φ : IsomC ell K L) : IsomC ell K L := by
  refine ⟨φ.1.trans (unitScalarEquiv u), ?_⟩
  obtain ⟨ψ, hψ⟩ := φ.2
  refine ⟨ψ.trans (unitScalarEquiv (u * u)), fun x y => ?_⟩
  change Additive.toMul (((u * u : (PadicInt ell)ˣ) : PadicInt ell) • Additive.ofMul (ψ (bracket ell L x y))) = _
  rw [hψ]
  change _ = Additive.ofMul (bracket ell K
    (Additive.toMul ((u : PadicInt ell) • Additive.ofMul (φ.1 x)))
    (Additive.toMul ((u : PadicInt ell) • Additive.ofMul (φ.1 y))))
  rw [bracket_smul_left, bracket_smul_right, Units.val_mul, mul_smul]
  rfl

theorem scalarStep_equivalence {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L] :
    Equivalence (ScalarStep (ell := ell) (K := K) (L := L)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    rw [scalarStep_iff_unit]
    exact ⟨1, fun x => by simp⟩
  · intro φ χ h
    obtain ⟨u, hu⟩ := (scalarStep_iff_unit φ χ).mp h
    rw [scalarStep_iff_unit]
    exact ⟨u⁻¹, fun x => by rw [hu, ← mul_smul]; simp⟩
  · intro φ χ ψ h h'
    obtain ⟨u, hu⟩ := (scalarStep_iff_unit φ χ).mp h
    obtain ⟨v, hv⟩ := (scalarStep_iff_unit χ ψ).mp h'
    rw [scalarStep_iff_unit]
    exact ⟨v * u, fun x => by rw [hv, hu, Units.val_mul, mul_smul]⟩

theorem scalarEqvGen_iff {ell : ℕ} [Fact ell.Prime] {K L : Type*} [Field K] [Field L]
    (φ χ : IsomC ell K L) :
    Relation.EqvGen ScalarStep φ χ ↔ ScalarStep φ χ := by
  exact scalarStep_equivalence.eqvGen_iff

end BogomolovPop

namespace BogomolovPop
open scoped Topology commutatorElement

theorem quotient_comap_map_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (N : Subgroup H) [N.Normal] :
    Function.Injective (QuotientGroup.map (N.comap f) N f le_rfl) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  induction z using QuotientGroup.induction_on with | H x =>
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (QuotientGroup.eq_one_iff (f x)).mp hz

theorem proEllKernel_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (ell : ℕ) (f : G →* H)
    (hf : Continuous f) : proEllKernel ell G ≤ (proEllKernel ell H).comap f := by
  intro x hx
  simp only [proEllKernel, Subgroup.mem_comap, Subgroup.mem_iInf] at hx ⊢
  intro N hN
  let U : OpenNormalSubgroup G :=
    { N.toOpenSubgroup.comap f hf with
      isNormal' := by
        change (N.toSubgroup.comap f).Normal
        infer_instance }
  have : U.toSubgroup.Normal := U.isNormal'
  have hU : IsPGroup ell (G ⧸ U.toSubgroup) :=
    hN.of_injective (QuotientGroup.map (N.toSubgroup.comap f) N.toSubgroup f le_rfl)
      (quotient_comap_map_injective f N.toSubgroup)
  exact hx U hU

theorem continuous_quotientMap {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (hf : Continuous f) :
    Continuous (QuotientGroup.map N M f h) := by
  apply (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp hf

theorem closedCommutator_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change f ⁅x, y⁆ ∈ (commutator H).topologicalClosure
    rw [map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · exact (Subgroup.isClosed_topologicalClosure _).preimage hf

theorem closedGammaThree_map_le {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) :
    closedGammaThree G ≤ (closedGammaThree H).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · apply Subgroup.commutator_le.mpr
    intro x hx y _
    change f ⁅x, y⁆ ∈ closedGammaThree H
    rw [map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (closedCommutator_map_le f hf hx)
        (Subgroup.mem_top _))
  · exact (Subgroup.isClosed_topologicalClosure _).preimage hf

def quotientContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (f : G ≃ₜ* H)
    (hf : N ≤ M.comap f.toMonoidHom) (hi : M ≤ N.comap f.symm.toMonoidHom) :
    (G ⧸ N) ≃ₜ* (H ⧸ M) where
  toFun := QuotientGroup.map N M f.toMonoidHom hf
  invFun := QuotientGroup.map M N f.symm.toMonoidHom hi
  left_inv x := by
    induction x using QuotientGroup.induction_on with | H x =>
      change QuotientGroup.mk' N (f.symm (f x)) = QuotientGroup.mk' N x
      rw [f.symm_apply_apply]
  right_inv x := by
    induction x using QuotientGroup.induction_on with | H x =>
      change QuotientGroup.mk' M (f (f.symm x)) = QuotientGroup.mk' M x
      rw [f.apply_symm_apply]
  map_mul' := map_mul _
  continuous_toFun := continuous_quotientMap N M f.toMonoidHom hf f.continuous
  continuous_invFun := continuous_quotientMap M N f.symm.toMonoidHom hi f.symm.continuous

def proEllContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (ell : ℕ) (f : G ≃ₜ* H) :
    (G ⧸ proEllKernel ell G) ≃ₜ* (H ⧸ proEllKernel ell H) :=
  quotientContinuousEquiv _ _ f (proEllKernel_map_le ell f.toMonoidHom f.continuous)
    (proEllKernel_map_le ell f.symm.toMonoidHom f.symm.continuous)

def abelianContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G ≃ₜ* H) :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization H :=
  quotientContinuousEquiv _ _ f (closedCommutator_map_le f.toMonoidHom f.continuous)
    (closedCommutator_map_le f.symm.toMonoidHom f.symm.continuous)

def centralContinuousEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    [IsTopologicalGroup H] (f : G ≃ₜ* H) :
    (G ⧸ closedGammaThree G) ≃ₜ* (H ⧸ closedGammaThree H) :=
  quotientContinuousEquiv _ _ f (closedGammaThree_map_le f.toMonoidHom f.continuous)
    (closedGammaThree_map_le f.symm.toMonoidHom f.symm.continuous)

end BogomolovPop

noncomputable section
namespace BogomolovPop
open scoped Topology

theorem isAlgClosure_perfectClosure (F : Type*) [Field F] :
    IsAlgClosure (PerfectFieldClosure F) (AlgebraicClosure F) := by
  have : Algebra.IsAlgebraic (PerfectFieldClosure F) (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.tower_top (K := F) (PerfectFieldClosure F)
  exact ⟨inferInstance, inferInstance⟩

def extendPerfectEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L) :
    AlgebraicClosure K ≃+* AlgebraicClosure L := by
  letI := isAlgClosure_perfectClosure K
  letI := isAlgClosure_perfectClosure L
  exact IsAlgClosure.equivOfEquiv (AlgebraicClosure K) (AlgebraicClosure L) α

theorem extendPerfectEquiv_spec {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L) (x : PerfectFieldClosure K) :
    extendPerfectEquiv α x = (α x : AlgebraicClosure L) := by
  let := isAlgClosure_perfectClosure K
  let := isAlgClosure_perfectClosure L
  exact IsAlgClosure.equivOfEquiv_algebraMap (AlgebraicClosure K) (AlgebraicClosure L) α x

theorem perfectClosure_fixed {F : Type*} [Field F]
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (x : PerfectFieldClosure F) :
    σ (x : AlgebraicClosure F) = x := by
  have h : σ.toAlgHom.comp (perfectClosure F (AlgebraicClosure F)).val =
      (perfectClosure F (AlgebraicClosure F)).val := Subsingleton.elim _ _
  exact DFunLike.congr_fun h x

def absoluteConjugate {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K where
  toRingEquiv := (β.trans σ.toRingEquiv).trans β.symm
  commutes' x := by
    change β.symm (σ (β (algebraMap K (AlgebraicClosure K) x))) = _
    apply β.injective
    rw [β.apply_symm_apply]
    change σ (β ((algebraMap K (PerfectFieldClosure K) x : PerfectFieldClosure K) :
      AlgebraicClosure K)) = β _
    rw [hβ, perfectClosure_fixed]
    exact (hβ _).symm

@[simp] theorem absoluteConjugate_apply {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (x : AlgebraicClosure K) :
    absoluteConjugate α β hβ σ x = β.symm (σ (β x)) := rfl

theorem perfectExtension_symm {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    ∀ y : PerfectFieldClosure L, β.symm y = (α.symm y : AlgebraicClosure K) := by
  intro y
  apply β.injective
  rw [β.apply_symm_apply, hβ, α.apply_symm_apply]

def absoluteConjugateEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) ≃*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  toFun := absoluteConjugate α β hβ
  invFun := absoluteConjugate α.symm β.symm (perfectExtension_symm α β hβ)
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
  map_mul' σ τ := by ext x; simp [AlgEquiv.mul_apply]

theorem absoluteConjugate_continuous {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    Continuous (absoluteConjugate α β hβ) := by
  change Continuous (absoluteConjugateEquiv α β hβ).toMonoidHom
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  rw [map_one, krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨E, hE, heU⟩ := hU
  let : FiniteDimensional K E := hE
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := K) (A := E))
  let S : Set (AlgebraicClosure L) := (fun x : E => β (x : AlgebraicClosure K)) '' (s : Set E)
  have hS : S.Finite := s.finite_toSet.image _
  let : Finite S := hS.to_subtype
  let E' := IntermediateField.adjoin L S
  have : FiniteDimensional L E' := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := L) x).isIntegral)
  apply (krullTopology_mem_nhds_one_iff L (AlgebraicClosure L) _).mpr
  refine ⟨E', inferInstance, ?_⟩
  intro σ hσ
  apply heU
  change absoluteConjugate α β hβ σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have heq : (absoluteConjugate α β hβ σ).toAlgHom.comp E.val = E.val := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro x hx
    change β.symm (σ (β (x : AlgebraicClosure K))) = x
    rw [((IntermediateField.mem_fixingSubgroup_iff E' σ).mp hσ) _
      (IntermediateField.subset_adjoin L S ⟨x, hx, rfl⟩), β.symm_apply_apply]
  intro x hx
  exact DFunLike.congr_fun heq ⟨x, hx⟩

def absoluteConjugateContinuousEquiv {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    Field.absoluteGaloisGroup L ≃ₜ* Field.absoluteGaloisGroup K where
  toMulEquiv := absoluteConjugateEquiv α β hβ
  continuous_toFun := absoluteConjugate_continuous α β hβ
  continuous_invFun := absoluteConjugate_continuous α.symm β.symm
    (perfectExtension_symm α β hβ)

end BogomolovPop

namespace BogomolovPop
open scoped Topology

theorem centralProjection_natural {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) (z : PiC ell L) :
    centralProjection ell K (centralContinuousEquiv f z) =
      abelianContinuousEquiv f (centralProjection ell L z) := by
  induction z using QuotientGroup.induction_on with | H z => rfl

def deltaContinuousEquiv {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) : Delta ell L ≃ₜ* Delta ell K where
  toFun x := ⟨centralContinuousEquiv f x, by
    change centralProjection ell K _ = 1
    rw [centralProjection_natural, x.property, map_one]⟩
  invFun x := ⟨(centralContinuousEquiv f).symm x, by
    change centralProjection ell L _ = 1
    apply (abelianContinuousEquiv f).injective
    rw [map_one, ← centralProjection_natural, ContinuousMulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := by ext; exact (centralContinuousEquiv f).symm_apply_apply x
  right_inv x := by ext; exact (centralContinuousEquiv f).apply_symm_apply x
  map_mul' x y := by ext; exact map_mul (centralContinuousEquiv f) (x : PiC ell L) (y : PiC ell L)
  continuous_toFun := Continuous.subtype_mk
    ((centralContinuousEquiv f).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((centralContinuousEquiv f).symm.continuous.comp continuous_subtype_val) _

theorem induced_bracketCompatible {ell : ℕ} {K L : Type*} [Field K] [Field L]
    (f : ProEll ell L ≃ₜ* ProEll ell K) :
    BracketCompatible (abelianContinuousEquiv f) := by
  refine ⟨deltaContinuousEquiv f, ?_⟩
  intro σ τ
  apply Subtype.ext
  change centralContinuousEquiv f (bracket ell L σ τ : PiC ell L) = _
  rw [bracket_eq_of_lifts ell K _ _ (f (abelianLift ell L σ))
    (f (abelianLift ell L τ))]
  · change QuotientGroup.mk' _ (f (sourceCommutator (abelianLift ell L σ)
      (abelianLift ell L τ))) = _
    simp only [sourceCommutator, map_mul, map_inv]
  · change abelianContinuousEquiv f (QuotientGroup.mk' _ (abelianLift ell L σ)) = _
    rw [abelianLift_spec]
  · change abelianContinuousEquiv f (QuotientGroup.mk' _ (abelianLift ell L τ)) = _
    rw [abelianLift_spec]

def isomCOfExtension (ell : ℕ) {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L)) :
    IsomC ell K L :=
  ⟨abelianContinuousEquiv (proEllContinuousEquiv ell
      (absoluteConjugateContinuousEquiv α β hβ)), induced_bracketCompatible _⟩

theorem pullbackGraph_of_extension (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (β : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α.1 x : AlgebraicClosure L)) :
    PullbackGraph α (isomCOfExtension ell α.1 β hβ) := by
  refine ⟨β, hβ, ?_⟩
  intro σ
  refine ⟨absoluteConjugate α.1 β hβ σ, ?_, rfl⟩
  intro x
  exact β.apply_symm_apply _

theorem exists_pullbackGraph (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : ∃ φ : IsomC ell K L, PullbackGraph α φ := by
  exact ⟨isomCOfExtension ell α.1 (extendPerfectEquiv α.1) (extendPerfectEquiv_spec α.1),
    pullbackGraph_of_extension ell α _ (extendPerfectEquiv_spec α.1)⟩

end BogomolovPop

namespace BogomolovPop

 theorem absoluteToPiA_surjective (ell : ℕ) (F : Type*) [Field F] :
    Function.Surjective (absoluteToPiA ell F) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

def extensionDifference {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L)) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K where
  toRingEquiv := β.trans γ.symm
  commutes' x := by
    change γ.symm (β (algebraMap K (AlgebraicClosure K) x)) = _
    apply γ.injective
    rw [γ.apply_symm_apply]
    exact (hβ (algebraMap K (PerfectFieldClosure K) x)).trans
      (hγ (algebraMap K (PerfectFieldClosure K) x)).symm

theorem absoluteConjugate_extensionDifference {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L))
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) :
    absoluteConjugate α γ hγ σ = extensionDifference α β γ hβ hγ *
      absoluteConjugate α β hβ σ * (extensionDifference α β γ hβ hγ)⁻¹ := by
  ext x
  simp [AlgEquiv.mul_apply, extensionDifference, absoluteConjugate]
  change γ x = β (β.symm (γ x))
  exact (β.apply_symm_apply _).symm

theorem isomCOfExtension_eq (ell : ℕ) {K L : Type*} [Field K] [Field L]
    (α : PerfectFieldClosure K ≃+* PerfectFieldClosure L)
    (β γ : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hβ : ∀ x : PerfectFieldClosure K, β x = (α x : AlgebraicClosure L))
    (hγ : ∀ x : PerfectFieldClosure K, γ x = (α x : AlgebraicClosure L)) :
    isomCOfExtension ell α β hβ = isomCOfExtension ell α γ hγ := by
  apply Subtype.ext
  ext x
  obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
  change absoluteToPiA ell K (absoluteConjugate α β hβ σ) =
    absoluteToPiA ell K (absoluteConjugate α γ hγ σ)
  rw [absoluteConjugate_extensionDifference α β γ hβ hγ σ]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* PiA ell K := absoluteToPiA ell K
  change f _ = f _
  simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]

theorem pullbackGraph_eq_extension (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) (φ : IsomC ell K L) (hφ : PullbackGraph α φ) :
    φ = isomCOfExtension ell α.1 (extendPerfectEquiv α.1) (extendPerfectEquiv_spec α.1) := by
  obtain ⟨β, hβ, h⟩ := hφ
  have heq : φ = isomCOfExtension ell α.1 β hβ := by
    apply Subtype.ext
    ext x
    obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
    obtain ⟨τ, hτ, hφτ⟩ := h σ
    have hτ' : τ = absoluteConjugate α.1 β hβ σ := by
      apply AlgEquiv.ext
      intro x
      apply β.injective
      exact (hτ x).trans (β.apply_symm_apply _).symm
    change φ.1 (absoluteToPiA ell L σ) =
      absoluteToPiA ell K (absoluteConjugate α.1 β hβ σ)
    exact hφτ.trans (congrArg (absoluteToPiA ell K) hτ')
  exact heq.trans (isomCOfExtension_eq ell α.1 β (extendPerfectEquiv α.1) hβ
    (extendPerfectEquiv_spec α.1))

theorem existsUnique_pullbackGraph (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : ∃! φ : IsomC ell K L, PullbackGraph α φ := by
  obtain ⟨φ, hφ⟩ := exists_pullbackGraph ell α
  refine ⟨φ, hφ, fun χ hχ => ?_⟩
  exact (pullbackGraph_eq_extension ell α χ hχ).trans
    (pullbackGraph_eq_extension ell α φ hφ).symm

end BogomolovPop

namespace BogomolovPop

def canonicalPullback (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : IsomC ell K L :=
  isomCOfExtension ell α.1 (extendPerfectEquiv α.1) (extendPerfectEquiv_spec α.1)

theorem canonicalPullback_spec (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (α : PerfectIsom k K l L) : PullbackGraph α (canonicalPullback ell α) :=
  pullbackGraph_of_extension ell α _ (extendPerfectEquiv_spec α.1)

theorem canonicalPullback_frobenius (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {α χ : PerfectIsom k K l L} (h : FrobeniusStep α χ) :
    canonicalPullback ell α = canonicalPullback ell χ := by
  obtain ⟨p, hp, hpL, hχ⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := (CharP.charP_iff_prime_eq_zero hp).mpr hpL
  let β := extendPerfectEquiv α.1
  have hβ := extendPerfectEquiv_spec α.1
  let γ := β.trans (frobeniusEquiv (AlgebraicClosure L) p)
  have hγ : ∀ x : PerfectFieldClosure K, γ x = (χ.1 x : AlgebraicClosure L) := by
    intro x
    change (β x) ^ p = (χ.1 x : AlgebraicClosure L)
    rw [hβ, hχ x]
    rfl
  have heq : isomCOfExtension ell α.1 β hβ = isomCOfExtension ell χ.1 γ hγ := by
    apply Subtype.ext
    ext x
    obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective ell L x
    change absoluteToPiA ell K (absoluteConjugate α.1 β hβ σ) =
      absoluteToPiA ell K (absoluteConjugate χ.1 γ hγ σ)
    congr 1
    apply AlgEquiv.ext
    intro x
    apply γ.injective
    let σ' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ
    change γ (β.symm (σ' (β x))) = γ (γ.symm (σ' (γ x)))
    rw [γ.apply_symm_apply]
    change (β (β.symm (σ' (β x)))) ^ p = σ' ((β x) ^ p)
    rw [β.apply_symm_apply, map_pow]
  exact heq.trans (isomCOfExtension_eq ell χ.1 γ (extendPerfectEquiv χ.1) hγ
    (extendPerfectEquiv_spec χ.1))

theorem canonicalPullback_eq_of_frobeniusOrbit (ell : ℕ) {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {α χ : PerfectIsom k K l L}
    (h : Relation.EqvGen (FrobeniusStep (k := k) (K := K) (l := l) (L := L)) α χ) :
    canonicalPullback ell α = canonicalPullback ell χ := by
  induction h with
  | rel a b hab => exact canonicalPullback_frobenius ell hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def canonicalPhi (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L] :
    IsomF k K l L → IsomCUnits ell K L :=
  Quotient.lift (fun α => Quotient.mk _ (canonicalPullback ell α)) (by
    intro α χ h
    rw [canonicalPullback_eq_of_frobeniusOrbit ell h])

theorem canonicalPhi_graph (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    (a : IsomF k K l L) : PhiGraph a (canonicalPhi ell a) := by
  induction a using Quotient.inductionOn with | h α =>
    exact ⟨α, canonicalPullback ell α, rfl, rfl, canonicalPullback_spec ell α⟩

theorem phiGraph_eq_canonicalPhi (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L]
    {a : IsomF k K l L} {b : IsomCUnits ell K L} (h : PhiGraph a b) :
    b = canonicalPhi ell a := by
  obtain ⟨α, φ, rfl, rfl, hφ⟩ := h
  change Quotient.mk _ φ = Quotient.mk _ (canonicalPullback ell α)
  rw [pullbackGraph_eq_extension ell α φ hφ]
  rfl

theorem main_wellDefined (ell : ℕ) [Fact ell.Prime] {k K l L : Type*}
    [Field k] [Field K] [Field l] [Field L] [Algebra k K] [Algebra l L] :
    ∀ a : IsomF k K l L, ∃! b : IsomCUnits ell K L, PhiGraph a b := by
  intro a
  exact ⟨canonicalPhi ell a, canonicalPhi_graph ell a,
    fun b hb => phiGraph_eq_canonicalPhi ell hb⟩

end BogomolovPop

namespace BogomolovPop

theorem main_canonical_wellDefined (ell : ℕ) [Fact ell.Prime]
    (k K l L : Type*) [Field k] [Field K] [Field l] [Field L]
    [IsAlgClosed k] [IsAlgClosed l] [Algebra k K] [Algebra l L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType l L]
    (_hk : (ell : k) ≠ 0) (_hl : (ell : l) ≠ 0)
    (_hK : 2 ≤ Algebra.trdeg k K) (_hL : 2 ≤ Algebra.trdeg l L) :
    ∀ a : IsomF k K l L, ∃! b : IsomCUnits ell K L, PhiGraph a b := by
  exact main_wellDefined ell

end BogomolovPop

end
end

end OAI
