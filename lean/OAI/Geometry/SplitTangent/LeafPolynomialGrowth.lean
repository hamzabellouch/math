import Mathlib
import OAI.Geometry.SplitTangent.AmbientLeafSectionBound
import OAI.Geometry.SplitTangent.CurveHomogeneousSections
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.PolynomialLeafGerms

namespace OAI

/-! Leaf Polynomial Growth. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S)
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  (P : AlignedProductChart S A B)

def leafPolynomialKernel (k : ℕ) :
    Submodule ℂ (MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k) where
  carrier := {p | (fun t : A => MvPolynomial.eval
      (F.finite 1 (P.chart.symm (t,(P.chart (g.finite 1)).2))) p.val)
        =ᶠ[𝓝 (P.chart (g.finite 1)).1] 0}
  zero_mem' := by
    filter_upwards [] with t
    simp
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp,hq] with t ht ht'
    simp only [Submodule.coe_add,MvPolynomial.eval_add,ht,ht',Pi.zero_apply,add_zero]
  smul_mem' := by
    intro c p hp
    filter_upwards [hp] with t ht
    simp only [Submodule.coe_smul,MvPolynomial.smul_eval,ht,Pi.zero_apply,mul_zero]

abbrev LeafPolynomialGerms (k : ℕ) :=
  (MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ k) ⧸ F.leafPolynomialKernel P k

def coefficientQuotient (a k : ℕ) : HomogeneousTuple (e := e) a k →ₗ[ℂ]
    (Fin (a+1) → F.LeafPolynomialGerms P k) where
  toFun p i := (F.leafPolynomialKernel P k).mkQ (p i)
  map_add' _ _ := by ext i; exact map_add _ _ _
  map_smul' c p := by
    funext i
    exact (F.leafPolynomialKernel P k).mkQ.map_smul c (p i)

omit [CompleteSpace A] [CompleteSpace B] in
lemma coefficientQuotient_surjective (a k : ℕ) :
    Function.Surjective (F.coefficientQuotient P a k) := by
  intro q
  choose p hp using fun i => (F.leafPolynomialKernel P k).mkQ_surjective (q i)
  exact ⟨p,funext hp⟩

def sectionGermMap (a k : ℕ) : HomogeneousTuple (e := e) a k →ₗ[ℂ]
    (F.ambientTransition a k).GermSpace L :=
  (SeparatedQuotientFiltration.zeroPart ((F.ambientTransition a k).contact L)).mkQ.comp (F.sections a k)

lemma sectionGermMap_ker_le (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (a k : ℕ) : (F.sectionGermMap L a k).ker ≤ (F.coefficientQuotient P a k).ker := by
  intro p hp
  have hf : F.sections a k p∈SeparatedQuotientFiltration.zeroPart
      ((F.ambientTransition a k).contact L) := (Submodule.Quotient.mk_eq_zero _).mp hp
  have hc := F.flat_section_coefficients L P hy ht p hf
  change F.coefficientQuotient P a k p=0
  funext i
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hc i)

include L in
 

theorem leaf_polynomial_finite_and_bound
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first) (a k : ℕ) :
    Module.Finite ℂ (F.LeafPolynomialGerms P k) ∧
      (a+1)*Module.finrank ℂ (F.LeafPolynomialGerms P k) ≤
        (a+k*F.degree+Module.finrank ℂ (S.first (g.finite 1))).choose
          (Module.finrank ℂ (S.first (g.finite 1)))*(a+k*F.degree+1) := by
  obtain ⟨hfin,hbound⟩ := (F.ambientTransition a k).germ_finite_and_bound L hg
  let := hfin
  obtain ⟨hQ,hb⟩ := LinearKernelDimension.finite_and_bound (F.sectionGermMap L a k)
    (F.coefficientQuotient P a k) (F.sectionGermMap_ker_le L P hy ht a k)
    (F.coefficientQuotient_surjective P a k)
  let := hQ
  let ev : (Fin (a+1) → F.LeafPolynomialGerms P k) →ₗ[ℂ] F.LeafPolynomialGerms P k :=
    LinearMap.proj (0 : Fin (a+1))
  have hev : Function.Surjective ev := fun v => ⟨fun _ => v,rfl⟩
  let : Module.Finite ℂ (F.LeafPolynomialGerms P k) := Module.Finite.of_surjective ev hev
  refine ⟨inferInstance,?_⟩
  let : AddCommGroup (F.LeafPolynomialGerms P k) :=
    Module.addCommMonoidToAddCommGroup ℂ
  have he : Module.finrank ℂ (Fin (a+1) → F.LeafPolynomialGerms P k)=
      (a+1)*Module.finrank ℂ (F.LeafPolynomialGerms P k) := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [he] at hb
  exact hb.trans hbound

include L in
 

theorem leaf_polynomial_growth
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first) (k : ℕ) :
    Module.Finite ℂ (F.LeafPolynomialGerms P k) ∧
      Module.finrank ℂ (F.LeafPolynomialGerms P k) ≤
        (F.degree+Module.finrank ℂ (S.first (g.finite 1))+1)^
          (Module.finrank ℂ (S.first (g.finite 1)))*(F.degree+1)*
            (k+1)^(Module.finrank ℂ (S.first (g.finite 1))) := by
  obtain ⟨hf,hb⟩ := F.leaf_polynomial_finite_and_bound L P hy ht hg k k
  exact ⟨hf,PolynomialGrowthArithmetic.cancel_graph_dimension _ _ _ _ hb⟩

end SplitTangent.RationalCurveFrames

end

end OAI
