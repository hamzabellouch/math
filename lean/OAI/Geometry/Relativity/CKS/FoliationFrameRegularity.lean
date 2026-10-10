import OAI.Geometry.Relativity.CKS.FoliationOrthonormalFrame
import OAI.Geometry.Relativity.CKS.PhysicalFrameCurvature

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) :
    DifferentiableAt ℝ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have hrr : DifferentiableAt ℝ
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (CKSCalculus.diffAt_div (differentiableAt_const 1) (hU.pow 2) (pow_ne_zero _ h0)).add
      (DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum
        (fun b _ => ((hγc a b).fun_mul (hsc a)).fun_mul (hsc b))))
  have hm (a) : DifferentiableAt ℝ (fun y => ∑ b, γ y a b*s y b) x :=
    DifferentiableAt.fun_sum (fun b _ => (hγc a b).fun_mul (hsc b))
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hγc 0 0
  · exact hγc 0 1
  · exact hm 1
  · exact hγc 1 0
  · exact hγc 1 1

lemma adaptedFrame_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : DifferentiableAt ℝ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).fun_mul (hγc 1 1)).fun_sub ((hγc 0 1).fun_mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.fun_mul (hsc 0)
  · exact hU.neg.fun_mul (hsc 1)
  · exact differentiableAt_const 0
  · exact ha.inv hapos.ne'
  · exact differentiableAt_const 0
  · exact differentiableAt_const 0
  · exact CKSCalculus.diffAt_div (hγc 0 1).neg (ha.fun_mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact CKSCalculus.diffAt_div ha hb hbpos.ne'

lemma adaptedFrame_leafBracket {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : U x ≠ 0) (hγ : (γ x).IsHermitian) (a b : Fin 2) :
    frameBracketCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ 0=0 := by
  apply metricPair_normal_tangent hU hγ
  change D _ (fun y => adaptedFrame (U y) (γ y) (s y) b.succ 0) x -
      D _ (fun y => adaptedFrame (U y) (γ y) (s y) a.succ 0) x = 0
  simp only [adaptedFrame_radial]
  have hz (e : PhysicalPoint) : D e (fun _ : PhysicalPoint => (0 : ℝ)) x=0 := by
    exact CKSCalculus.D_const e x 0
  rw [hz,hz]
  ring

theorem foliation_actualAdaptedAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    ∀ᶠ y in 𝓝 x, ActualAdaptedAt
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y := by
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hu0 := hU.continuousAt.eventually_ne h0
  have hnear : ∀ᶠ y in 𝓝 x, U y ≠ 0 ∧ (γ y).PosDef := by
    filter_upwards [hu0,hp] with y hy hg
    exact ⟨hy,hg⟩
  filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
    hs1.eventually (by norm_num),hnear,hnear.eventually_nhds] with y hyu hyg hys hyp hn
  refine ⟨foliationMetric_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.1,
    fun i => adaptedFrame_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.2 i,
    foliationMetric_posDef hyp.1 hyp.2 (s y), ?_, ?_, ?_⟩
  · filter_upwards [hn] with z hz
    exact metricBlock_hermitian _ _ hz.2.isHermitian
  · filter_upwards [hn] with z hz
    exact adaptedFrame_orthonormal hz.1 hz.2 (s z)
  · exact adaptedFrame_leafBracket hyp.1 hyp.2.isHermitian

end
end CKSAngularGeometry

end

end OAI
