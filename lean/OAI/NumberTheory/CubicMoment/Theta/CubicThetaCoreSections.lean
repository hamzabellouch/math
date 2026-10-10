import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! The finite core cutoffs are norms of genuine compact smooth cubic
sections. Thus they supply actual local test sections, including at every
point of the compact core. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators CompactlySupported ContDiff Manifold MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCoreSeed_support (c : CubicThetaQuotient) :
    Function.support (cubicThetaCoreSeed c) ⊆
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)).source := by
  intro p hp
  change cubicThetaCoreProfile c p.val≠0 at hp
  have ht := cubicThetaCoreProfile_support_target c (subset_tsupport _ hp)
  change p.val∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm p.val∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source at ht
  have hi : cubicThetaPointInclusion.symm p.val=p :=
    cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)
  rw [hi] at ht
  exact ht.2

def cubicThetaCoreSection (c : CubicThetaQuotient) : cubicThetaSmoothTests :=
  ⟨cubicThetaPoincareSection (cubicThetaCoreSeed c),
    cubicThetaPoincareSection_contDiffOn _ (cubicThetaCoreSeed_contDiffOn c),
    cubicThetaPoincareSection_compact _⟩

lemma cubicThetaCoreSection_on_sheet (c : CubicThetaQuotient) {p : CubicThetaPoint}
    (hp : p∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source) :
    (cubicThetaCoreSection c).val.val p=cubicThetaCoreProfile c p.val :=
  cubicThetaPoincareSection_on_sheet _ _ (cubicThetaCoveringChart_coe _)
    (cubicThetaCoreSeed_support c) hp

lemma cubicThetaCoreSeed_eq_bump (c : CubicThetaQuotient) {p : CubicThetaPoint}
    (hp : p∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source) :
    cubicThetaCoreProfile c p.val=(cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ) := by
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  have hq : cubicThetaQuotientMap p∈(cubicThetaQuotientChart c).source := by
    refine ⟨?_,?_⟩
    · change cubicThetaQuotientMap p∈e.target
      rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
      exact e.map_source hp
    · rw [cubicThetaPointInclusion_source]
      trivial
  have hb := (cubicThetaCoreBump c).eqOn_source hq
  have he : cubicThetaQuotientChart c (cubicThetaQuotientMap p)=p.val := by
    change cubicThetaPointInclusion (e.symm (cubicThetaQuotientMap p))=p.val
    rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
    rw [e.left_inv hp]
    rfl
  simp only [extChartAt_coe,Function.comp_def,modelWithCornersSelf_coe,id_eq] at hb
  change cubicThetaCoreBump c (cubicThetaQuotientMap p)=
    (cubicThetaCoreBump c).toContDiffBump (cubicThetaQuotientChart c (cubicThetaQuotientMap p)) at hb
  rw [he] at hb
  exact congrArg (fun r : ℝ => (r:ℂ)) hb.symm

lemma cubicThetaCoreSection_norm (c q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaCoreSection c) q=cubicThetaCoreBump c q := by
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift c)
  by_cases hq : q∈e.target
  · let p := e.symm q
    have hp : p∈e.source := e.map_target hq
    have he : cubicThetaQuotientMap p=q := by
      rw [← cubicThetaCoveringChart_coe (cubicThetaQuotientLift c)]
      exact e.right_inv hq
    rw [← he,cubicThetaSectionNorm_apply,cubicThetaCoreSection_on_sheet c hp,
      cubicThetaCoreSeed_eq_bump c hp,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (cubicThetaCoreBump c).nonneg]
  · have hb : cubicThetaCoreBump c q=0 := by
      apply Function.notMem_support.mp
      intro h
      have hs := (cubicThetaCoreBump c).support_subset_source h
      exact hq hs.1
    rw [hb]
    unfold cubicThetaSectionNorm
    apply norm_eq_zero.mpr
    change (∑ᶠ g : cubicThetaPrincipalGroup,
      cubicThetaPoincareTerm (cubicThetaCoreSeed c) g (cubicThetaQuotientLift q))=0
    have hzero (g : cubicThetaPrincipalGroup) :
        cubicThetaPoincareTerm (cubicThetaCoreSeed c) g (cubicThetaQuotientLift q)=0 := by
      have hz : cubicThetaCoreSeed c (g • cubicThetaQuotientLift q)=0 := by
        by_contra hn
        have hp := cubicThetaCoreSeed_support c hn
        have he := e.map_source hp
        rw [cubicThetaCoveringChart_coe,cubicThetaQuotient_covering.map_smul,
          cubicThetaQuotientLift_map] at he
        exact hq he
      simp only [cubicThetaPoincareTerm,hz,mul_zero]
    simp only [hzero,finsum_zero]

lemma cubicThetaCoreSection_finite_cover (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      1≤∑ c∈A, (cubicThetaSectionNorm (cubicThetaCoreSection c) q)^2 := by
  simpa only [cubicThetaCoreSection_norm] using cubicThetaCoreBump_sum_sq S V

end CubicFirstMoment

end

end OAI
