import Mathlib
import OAI.Geometry.SplitTangent.AmbientLeafGerm
import OAI.Geometry.SplitTangent.CurveHomogeneousSections
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.ProjectiveLineFrame
import OAI.Geometry.SplitTangent.RationalCurveFrames

namespace OAI

/-! Polynomial Leaf Germs. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)

def baseMultiplier (q : ℂ × X.Carrier) : ℂ :=
  ∑i,(F.a i).eval 1*F.finite q.1 q.2 i

lemma baseMultiplier_holomorphic :
    ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω
      F.baseMultiplier (1,g.finite 1) := by
  apply contMDiffAt_finsetSum
  intro i hi
  exact (contMDiffAt_const (I' := 𝓘(ℂ,ℂ))).mul
    (contMDiffAt_pi_space.mp (F.finite_joint_holomorphicAt 1) i)

lemma baseMultiplier_one : F.baseMultiplier (1,g.finite 1)=1 := by
  simp only [baseMultiplier,F.finite_on_curve]
  exact F.finite_unit 1

lemma base_frame_eventually : ∀ᶠ q : ℂ × X.Carrier in 𝓝 (1,g.finite 1),
    F.finite q.1 q.2=F.baseMultiplier q • F.finite 1 q.2 ∧ F.baseMultiplier q≠0 := by
  have hn : F.baseMultiplier (1,g.finite 1)≠0 := by rw [F.baseMultiplier_one]; exact one_ne_zero
  filter_upwards [F.baseMultiplier_holomorphic.continuousAt.eventually_ne hn] with q hq
  have he : F.baseMultiplier q=
      (∑i,(F.a i).eval q.1*(e.map q.2).rep i)⁻¹ *
        (∑i,(F.a i).eval 1*(e.map q.2).rep i) := by
    simp only [baseMultiplier,finite,ProjectiveEmbedding.linearFrame,Pi.smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hb : (∑i,(F.a i).eval 1*(e.map q.2).rep i)≠0 := by
    rw [he] at hq
    exact (mul_ne_zero_iff.mp hq).2
  exact ⟨e.linearFrame_change _ _ q.2 hb,hq⟩

variable (L : LeafJetAtlas S)
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

 

theorem flat_section_coefficients (P : AlignedProductChart S A B)
    (hy : g.finite 1∈P.chart.source) (ht : g.TangentTo S.first)
    {a k : ℕ} (p : HomogeneousTuple (e := e) a k)
    (hf : F.sections a k p∈SeparatedQuotientFiltration.zeroPart ((F.ambientTransition a k).contact L)) :
    ∀i,(fun t : A => MvPolynomial.eval (F.finite 1 (P.chart.symm (t,(P.chart (g.finite 1)).2))) (p i).val)
      =ᶠ[𝓝 (P.chart (g.finite 1)).1] 0 := by
  let b := (P.chart (g.finite 1)).2
  let t₀ := (P.chart (g.finite 1)).1
  have hh := (F.ambientTransition a k).flat_joint_germ L (F.sections a k p) hf ht P hy
  have hm : Tendsto (fun q : ℂ × A => (q.1,P.chart.symm (q.2,b)))
      (𝓝 (1,t₀)) (𝓝 (1,g.finite 1)) := by
    have hInv : ContinuousAt P.chart.symm (t₀,b) :=
      (P.inverse_holomorphicAt (P.chart.map_source hy)).continuousAt
    have hP : ContinuousAt (fun q : ℂ × A => P.chart.symm (q.2,b)) (1,t₀) :=
      hInv.comp (f := fun q : ℂ × A => (q.2,b)) (x := (1,t₀))
        (continuousAt_snd.prodMk continuousAt_const)
    simpa only [ContinuousAt,t₀,b,Prod.mk.eta,P.chart.left_inv hy] using continuousAt_fst.prodMk hP
  apply PolynomialCoefficientGerms.coefficient_germs _ (1 : ℂ)
  filter_upwards [hh,hm.eventually F.base_frame_eventually] with q hq hframe
  change (∑i : Fin (a+1),q.1^i.val*MvPolynomial.eval (F.finite q.1 (P.chart.symm (q.2,b))) (p i).val)=0 at hq
  have he : (∑i : Fin (a+1),q.1^i.val*MvPolynomial.eval (F.finite q.1 (P.chart.symm (q.2,b))) (p i).val)=
      (F.baseMultiplier (q.1,P.chart.symm (q.2,b)))^k*
        (∑i : Fin (a+1),q.1^i.val*MvPolynomial.eval (F.finite 1 (P.chart.symm (q.2,b))) (p i).val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hframe.1,_root_.OAI.MvPolynomial.IsHomogeneous.eval_scale (p i).property]
    ring
  rw [he] at hq
  exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hframe.2)

end SplitTangent.RationalCurveFrames

end

end OAI
