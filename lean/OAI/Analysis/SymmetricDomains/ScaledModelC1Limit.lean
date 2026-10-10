import Mathlib
import OAI.Analysis.SymmetricDomains.ScaledRadialOperatorApply
import OAI.Analysis.SymmetricDomains.C1PerturbedFamilyLocal

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
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric
abbrev RealDiscParams (k : ℕ) := (Fin k → ℝ) × (Fin k → ℝ)

def normalSlice {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) : Fin k → ℝ := fun i => 2*realMean (κ*Y q i)

def discSlice {k : ℕ} (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) (i : Fin k) : C(ClosedDisc,ℂ) :=
  constantDisc (q.1 i)+realSchwarz (Y q i)

def scaledModel {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (t : ℝ) (q : RealDiscParams k) : Fin k → ℂ :=
  (fun i => (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (t • q.1,q.2) i : ℂ))+
    scaledRadialOperator t (fun i => κ*Y (t • q.1,q.2) i)

def limitModel {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) : Fin k → ℂ :=
  fun i => (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (0,q.2) i : ℂ)

def scaledDisc {k : ℕ} (Y : RealDiscParams k → BoundarySpace k)
    (t : ℝ) (q : RealDiscParams k) : Fin k → ℂ :=
  t⁻¹ • fun i => discSlice Y (t • q.1,q.2) i (radialPoint t)

lemma scaledDisc_eq_model {k : ℕ} {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : RealDiscParams k → BoundarySpace k} {q : RealDiscParams k} {t : ℝ}
    (hY : ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y (t • q.1,q.2) i) = 0)
    (ht : 0 < t) (ht1 : t < 1) :
    scaledDisc Y t q = scaledModel κ Y t q := by
  funext i
  change t⁻¹ • (constantDisc ((t • q.1) i) (radialPoint t)+
    realSchwarz (Y (t • q.1,q.2) i) (radialPoint t)) =
    (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (t • q.1,q.2) i : ℂ)+
      scaledRadialOperator t (fun j => κ*Y (t • q.1,q.2) j) i
  rw [constantDisc_apply,scaledRadialOperator_apply ht.le ht1.le]
  have he : radialPoint t = ⟨1-(t : ℂ),radial_mem_closedDisc ht.le ht1.le⟩ :=
    Subtype.ext (radialPoint_coe ht.le ht1.le)
  rw [he]
  change t⁻¹ • (↑((t • q.1) i)+schwarz (Y (t • q.1,q.2) i : Space) _) = _
  rw [← discValue_eq _ (radial_mem_closedDisc ht.le ht1.le),
    localized_radial_expansion hκ (fun θ hθ => hY θ hθ i) ht.le ht1]
  dsimp only [normalSlice,Pi.smul_apply,smul_eq_mul]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [Subalgebra.coe_mul]
  field_simp [htc]
  ring

lemma normalSlice_contDiffAt {k : ℕ} (κ : realAlgebra)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0) :
    ContDiffAt ℝ 1 (normalSlice κ Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_const.mul (realMean.contDiff.contDiffAt.comp 0
    (contDiffAt_const.mul (contDiffAt_pi.mp hY i)))

theorem scaledModel_C1_limit {k : ℕ} (κ : realAlgebra)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0) :
    ∃ r : ℝ, 0 < r ∧
      TendstoUniformlyOn (scaledModel κ Y) (limitModel κ Y) (𝓝 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (scaledModel κ Y t)) (fderiv ℝ (limitModel κ Y))
        (𝓝 0) (closedBall 0 r) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ q ∈ closedBall 0 r, DifferentiableAt ℝ (scaledModel κ Y t) q) := by
  let P : ℝ × RealDiscParams k → RealDiscParams k := fun v => (v.1 • v.2.1,v.2.2)
  have hP : ContDiffAt ℝ 1 P 0 := by fun_prop
  have hYP : ContDiffAt ℝ 1 (Y ∘ P) 0 := by
    have hY' : ContDiffAt ℝ 1 Y (P 0) := by simpa [P,← Prod.zero_eq_mk] using hY
    exact hY'.comp (f := P) 0 hP
  have hNP : ContDiffAt ℝ 1 (normalSlice κ Y ∘ P) 0 := by
    have hN : ContDiffAt ℝ 1 (normalSlice κ Y) (P 0) := by
      simpa [P,← Prod.zero_eq_mk] using normalSlice_contDiffAt κ hY
    exact hN.comp (f := P) 0 hP
  let F : ℝ × RealDiscParams k → Fin k → ℂ :=
    fun v i => (v.2.1 i : ℂ)+Complex.I*(normalSlice κ Y (P v) i : ℂ)
  let G : ℝ × RealDiscParams k → BoundarySpace k := fun v i => κ*Y (P v) i
  have hF : ContDiffAt ℝ 1 F 0 := by
    apply contDiffAt_pi.mpr
    intro i
    have hh := contDiffAt_pi.mp hNP i
    dsimp only [Function.comp_def] at hh
    dsimp only [F]
    refine (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add ?_
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hh)
  have hG : ContDiffAt ℝ 1 G 0 := by
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_const.mul (contDiffAt_pi.mp hYP i)
  obtain ⟨r,hr,hv,hd,hdf⟩ := c1_perturbed_family_local hF hG
    (scaledRadialOperator (k := k)) scaledRadialOperator_norm_tendsto
  have hF0 : (fun x => F (0,x)) = limitModel κ Y := by
    funext x i
    dsimp only [F,P,limitModel]
    rw [zero_smul]
  have hsum (t : ℝ) : (fun x => F (t,x)+scaledRadialOperator t (G (t,x))) =
      scaledModel κ Y t := rfl
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hv ⊢
    intro ε hε
    filter_upwards [hv ε hε] with t ht
    intro x hx
    rw [← congrFun hF0 x,← congrFun (hsum t) x]
    exact ht x hx
  · change TendstoUniformlyOn
      (fun p => fderiv ℝ (fun x => F (p,x)+scaledRadialOperator p (G (p,x))))
      (fderiv ℝ (fun x => F (0,x))) _ _ at hd
    simpa only [hF0,hsum] using hd
  · simpa only [hsum] using hdf

end Release061.Wiener

end

end OAI
