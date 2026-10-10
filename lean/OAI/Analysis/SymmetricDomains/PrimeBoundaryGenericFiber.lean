import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryParameterPeakMaximizer
import OAI.Analysis.SymmetricDomains.PositiveMaximizerFiber
import OAI.Analysis.SymmetricDomains.PrimeZeroLocusFixed
import OAI.Analysis.SymmetricDomains.SemialgebraicPolynomialNonzero

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set MeasureTheory
open scoped Classical

theorem finite_patch_exception_polynomial {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (Q : MvPolynomial (Fin n) ℂ) (hQ : Q ∉ I) (C : Finset (NashPatch (n+n)))
    (hC : ∀ p : C,
      (∃ R : MvPolynomial (Fin n) ℂ, R ∉ I ∧
        ∀ x ∈ p.val.domain, MvPolynomial.eval (p.val.complexMap x) R = 0) ∨
      volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m} = 0) :
    ∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
      (∀ z, MvPolynomial.eval z P ≠ 0 → MvPolynomial.eval z Q ≠ 0) ∧
      ∀ p : C, volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧
        MvPolynomial.eval (p.val.complexMap x) P ≠ 0} = 0 := by
  have hchoose (p : C) : ∃ R : MvPolynomial (Fin n) ℂ, R ∉ I ∧
      (volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m} = 0 ∨
        ∀ x ∈ p.val.domain, MvPolynomial.eval (p.val.complexMap x) R = 0) := by
    rcases hC p with ⟨R,hR,hv⟩ | hn
    · exact ⟨R,hR,Or.inr hv⟩
    · exact ⟨1,Ideal.one_notMem I,Or.inl hn⟩
  choose R hRI hR using hchoose
  let P := Q * ∏ p : C, R p
  have hPn : P ∉ I := by
    intro hp
    rcases ((inferInstance : I.IsPrime).mul_mem_iff_mem_or_mem).mp hp with h | h
    · exact hQ h
    · obtain ⟨p,_,hp⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hRI p hp
  have hfactor (z : Affine n) (hz : MvPolynomial.eval z P ≠ 0) :
      MvPolynomial.eval z Q ≠ 0 ∧ ∀ p : C, MvPolynomial.eval z (R p) ≠ 0 := by
    have hh : MvPolynomial.eval z Q * ∏ p : C, MvPolynomial.eval z (R p) ≠ 0 := by
      simpa only [P,map_mul,map_prod] using hz
    exact ⟨(mul_ne_zero_iff.mp hh).1,fun p =>
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).2) p (Finset.mem_univ p)⟩
  refine ⟨P,hPn,fun z hz => (hfactor z hz).1,?_⟩
  intro p
  rcases hR p with hn | hv
  · exact measure_mono_null (t := {x | x ∈ p.val.domain ∧ p.val.complexRank x < m})
      (fun _ hx => ⟨hx.1,hx.2.1⟩) hn
  · have he : {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧
        MvPolynomial.eval (p.val.complexMap x) P ≠ 0} = (∅ : Set (Fin p.val.dim → ℝ)) := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (hfactor _ hx.2.2).2 p (hv x hx.1)
    rw [he,measure_empty]

end

open Set Filter Topology MeasureTheory
open scoped Classical

theorem prime_boundary_generic_fiber {n : ℕ} {U : Set (Affine n)}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hI : I = MvPolynomial.vanishingIdeal ℂ U)
    (hU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
      (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
      (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
        p.complexMap x ∈ closure U \ U ∧
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
          ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  have hV : IsAffineAlgebraic (MvPolynomial.zeroLocus ℂ I) := ⟨I,rfl⟩
  have hUV : U ⊆ MvPolynomial.zeroLocus ℂ I := by
    rw [hI]
    exact MvPolynomial.zeroLocus_vanishingIdeal_le U
  have hcl : closure U ⊆ MvPolynomial.zeroLocus ℂ I := closure_minimal hUV hV.isClosed
  obtain ⟨m,Q,hQ,hcharts⟩ := prime_zeroLocus_fixed_charts I
  let S := (closure U \ U) ∩ {z : Affine n | MvPolynomial.eval z Q ≠ 0}
  have hS : IsSemialgebraic S := (hs.closure.diff hs).inter (isSemialgebraic_polynomial_nonzero Q)
  obtain ⟨C,h0,hC⟩ := isSemialgebraic_centered_nash_cover hS
  have hpS (p : C) {x : Fin p.val.dim → ℝ} (hx : x ∈ p.val.domain) : p.val.complexMap x ∈ S :=
    (hC _).mpr ⟨p.val,p.property,mem_image_of_mem _ hx⟩
  have hAlt (p : C) := p.val.principal_rank_dichotomy I Q hcharts (h0 _ p.property)
    (fun _ hx => hcl (hpS p hx).1.1) (fun _ hx => (hpS p hx).2)
  obtain ⟨P,hPI,hPQ,hbadRank⟩ := finite_patch_exception_polynomial I Q hQ C hAlt
  have hP : ∃ u ∈ U, MvPolynomial.eval u P ≠ 0 := by
    by_contra! hv
    apply hPI
    rw [hI]
    exact hv
  refine ⟨m,P,C,hP,?_,?_⟩
  · intro p hp
    refine ⟨h0 p hp,fun x hx => ?_⟩
    have hh := hpS ⟨p,hp⟩ hx
    exact ⟨hh.1,hcharts _ (hcl hh.1.1) hh.2⟩
  · intro bad hbad
    let B (p : C) : Set (Fin p.val.dim → ℝ) :=
      {x | x ∈ p.val.domain ∧ MvPolynomial.eval (p.val.complexMap x) P ≠ 0}
    have hBo (p : C) : IsOpen (B p) := by
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      exact inter_mem (p.val.isOpen_domain.mem_nhds hx.1)
        (((MvPolynomial.continuous_eval P).continuousAt.comp
          (p.val.analytic_complexMap x hx.1).continuousAt).eventually_ne hx.2)
    let E (p : C) : Set (Fin p.val.dim → ℝ) := bad p ∪
      {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧ MvPolynomial.eval (p.val.complexMap x) P ≠ 0}
    have hE (p : C) : volume (E p) = 0 := measure_union_null (hbad p) (hbadRank p)
    have hcover (a : Affine n →L[ℂ] ℂ) :
        ∃ p : C, ∃ x, x ∈ B p ∧ IsMaxOn (parameterPotential P a) (closure U) (p.val.complexMap x) := by
      obtain ⟨z,hz,hzP,hm⟩ := exists_boundary_parameterPeak_maximizer hV hUV hU hc hn hb P hP a
      obtain ⟨p,hp,x,hx,rfl⟩ := (hC z).mp ⟨hz,hPQ z hzP⟩
      exact ⟨⟨p,hp⟩,x,⟨hx,hzP⟩,hm⟩
    obtain ⟨p,c,x,hcB,hxc,hxE,hpos⟩ := actual_positive_maximizer_fiber P (closure U) isClosed_closure
      (fun p : C => p.val.dim) B hBo (fun p => p.val.complexMap)
      (fun p x hx => (p.val.analytic_complexMap x hx.1).contDiffAt.contDiffWithinAt)
      (fun p _ hx => (hpS p hx.1).1.1) (fun _ _ hx => hx.2)
      (fun p _ hx => p.val.injective_fderiv_complexMap hx.1) E hE hcover
    have hxB := hcB hxc
    refine ⟨p,c,x,hxB.1,hxc,?_,hxB.2,?_,hpos⟩
    · apply Nat.le_of_not_gt
      intro hr
      exact hxE (Or.inr ⟨hxB.1,hr,hxB.2⟩)
    · exact fun hx => hxE (Or.inl hx)

end Release061

end

end OAI
