import Mathlib
import OAI.Geometry.SplitTangent.CompactSetLimits
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PolynomialRelationLocus

namespace OAI

/-! Compact Polynomial Relations. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X) {n k : ℕ}
  (Q : Fin n → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k)

lemma joint_relation_zero_isClosed :
    IsClosed {p : (Fin n → ℂ) × X.Carrier |
      p.2∈e.homogeneousZeroLocus (relationPolynomial e Q p.1).val} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨c,x⟩ hx
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i≠0 at hi
  let f : (Fin n → ℂ) × X.Carrier → ℂ := fun p =>
    ∑j,MvPolynomial.eval (projectiveCoordinates i (e.map p.2)) (Q j).val*p.1 j
  have hc : ContinuousAt f (c,x) := by
    apply tendsto_finsetSum (f := fun j (p : (Fin n → ℂ) × X.Carrier) =>
      MvPolynomial.eval (projectiveCoordinates i (e.map p.2)) (Q j).val*p.1 j) Finset.univ
    intro j hj
    apply ContinuousAt.mul _ ((continuous_apply j).continuousAt.comp continuousAt_fst)
    have hh : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
        (fun z => MvPolynomial.eval (projectiveCoordinates i (e.map z)) (Q j).val) x :=
      _root_.OAI.MvPolynomial.contMDiffAt_eval_comp (ModelWithCorners X) (Q j).val (fun a =>
        contMDiffAt_pi_space.mp ((e.holomorphic i).contMDiffAt ((e.open_patch i).mem_nhds hi)) a)
    exact ContinuousAt.comp (f := Prod.snd)
      (g := fun z : X.Carrier => MvPolynomial.eval (projectiveCoordinates i (e.map z)) (Q j).val)
      hh.continuousAt (continuousAt_snd (p := (c,x)))
  have he (c' : Fin n → ℂ) (y : X.Carrier) (hy : (e.map y).rep i≠0) :
      y∈e.homogeneousZeroLocus (relationPolynomial e Q c').val ↔ f (c',y)=0 := by
    rw [e.homogeneous_coordinates_zero_iff (relationPolynomial e Q c').property i hy,relation_eval]
  have hn : f (c,x)≠0 := fun h => hx ((he c x hi).mpr h)
  have hpatch : ∀ᶠ p : (Fin n → ℂ) × X.Carrier in 𝓝 (c,x),(e.map p.2).rep i≠0 :=
    (continuousAt_snd (p := (c,x))).preimage_mem_nhds ((e.open_patch i).mem_nhds hi)
  filter_upwards [hc.eventually_ne hn,hpatch] with p hp hp'
  exact fun hh => hp ((he p.1 p.2 hp').mp hh)

def compactRelationLocus : Set (Compacts X.Carrier) :=
  {K | ∃c : Fin n → ℂ,c≠0 ∧
    (K : Set X.Carrier)⊆e.homogeneousZeroLocus (relationPolynomial e Q c).val}

lemma compactRelationLocus_isClosed : IsClosed (compactRelationLocus e Q) := by
  classical
  let V := {c : Fin n → ℂ | ‖c‖=1}
  have hV : IsCompact V := by
    simpa only [Metric.sphere,dist_zero_right] using (isCompact_sphere (0 : Fin n → ℂ) 1)
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have hC : IsClosed {p : V × Compacts X.Carrier |
      ∀x∈(p.2 : Set X.Carrier),x∈e.homogeneousZeroLocus (relationPolynomial e Q p.1.val).val} := by
    exact (CompactSetLimits.isClosed_forall_mem (joint_relation_zero_isClosed e Q)).preimage
      (continuous_subtype_val.prodMap continuous_id)
  have hh := isClosedMap_snd_of_compactSpace _ hC
  convert hh using 1
  ext K
  constructor
  · rintro ⟨c,hc,hzero⟩
    let a : ℂ := (‖c‖ : ℂ)⁻¹
    have ha : a≠0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hc)
    have hnorm : ‖a • c‖=1 := by
      simp only [norm_smul,a,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)
    refine ⟨(⟨a • c,hnorm⟩,K),?_,rfl⟩
    intro x hx
    have h := hzero hx
    change MvPolynomial.eval (e.map x).rep (relationPolynomial e Q (a • c)).val=0
    change MvPolynomial.eval (e.map x).rep (relationPolynomial e Q c).val=0 at h
    rw [relation_eval] at h ⊢
    simp only [Pi.smul_apply,smul_eq_mul]
    have he : (∑j,MvPolynomial.eval (e.map x).rep (Q j).val*(a*c j))=
        a*(∑j,MvPolynomial.eval (e.map x).rep (Q j).val*c j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he,h,mul_zero]
  · rintro ⟨⟨c,L⟩,hzero,rfl⟩
    refine ⟨c.val,?_,hzero⟩
    intro hc
    have hn := c.property
    simp [V,hc] at hn

end SplitTangent.LeafJetAtlas

end

end OAI
