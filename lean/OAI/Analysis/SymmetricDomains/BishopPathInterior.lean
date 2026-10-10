import Mathlib
import OAI.Analysis.SymmetricDomains.LocalBishopData

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
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def graphPoint {k : ℕ} (f : (Fin (k+1) → ℝ) → Fin k → ℝ)
    (q : (Fin k → ℝ) × ℝ) : Fin k → ℂ :=
  fun i => (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)

def imaginaryVector {k : ℕ} (e : Fin k → ℝ) : Fin k → ℂ :=
  fun i => Complex.I*(e i : ℂ)

lemma imaginaryVector_norm {k : ℕ} (e : Fin k → ℝ) : ‖imaginaryVector e‖ = ‖e‖ := by
  simp only [Pi.norm_def,imaginaryVector,nnnorm_mul,Complex.nnnorm_I,Complex.nnnorm_real,one_mul]

def DiscContinuityWithin (k : ℕ) (Ω : Set (Fin k → ℂ)) (ε : ℝ) : Prop :=
  ∀ A : Icc (0 : ℝ) 1 → ClosedDisc → Fin k → ℂ,
    Continuous (Function.uncurry A) →
    (∀ s, ∃ g : ℂ → Fin k → ℂ, AnalyticOnNhd ℂ g (ball 0 1) ∧ ∀ z : ClosedDisc, A s z = g z) →
    (∀ s z, ‖A s z‖ < ε) →
    (∀ s (z : ClosedDisc), ‖(z : ℂ)‖ = 1 → A s z ∈ Ω) →
    (∀ z, A ⟨0,by simp⟩ z ∈ Ω) → ∀ s z, A s z ∈ Ω

lemma bishopDisc_contDiffAt_at {k : ℕ} {Y : BishopParams k → BoundarySpace k}
    {p : BishopParams k} (hY : ContDiffAt ℝ 1 Y p) :
    ContDiffAt ℝ 1 (bishopDisc Y) p := by
  apply contDiffAt_pi.mpr
  intro i
  apply ContDiffAt.add
  · fun_prop
  · exact realSchwarz.contDiff.contDiffAt.comp _ (contDiffAt_pi.mp hY i)

lemma bishopDisc_eval_norm_le {k : ℕ} (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) (z : ClosedDisc) :
    ‖fun i => bishopDisc Y p i z‖ ≤ ‖bishopDisc Y p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact ((bishopDisc Y p i).norm_coe_le_norm z).trans (norm_le_pi_norm _ i)

lemma fourier_one_surjective_sphere {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ θ : Circle, fourier 1 θ = z := by
  let c : _root_.Circle := ⟨z,by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hz⟩
  obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  refine ⟨θ,?_⟩
  rw [AddCircle.homeomorphCircle_apply] at hθ
  simpa only [fourier_one] using congrArg (fun x : _root_.Circle => (x : ℂ)) hθ

lemma bishopParams_mem_ball {k : ℕ} {b e : Fin k → ℝ} {s δ r : ℝ}
    (hb : ‖b‖ < r) (he : ‖e‖ < r) (hs : |s| < r) (hδ : |δ| < r) :
    (b,e,s,δ) ∈ ball (0 : BishopParams k) r := by
  simpa only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff]
    using And.intro hb (And.intro he (And.intro hs hδ))

lemma bishop_boundary_eq_graph {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {p : BishopParams k}
    (hp : p ∈ ball 0 D.radius) (θ : Circle) :
    (fun i => bishopDisc D.Y p i ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩) =
      graphPoint f ((fun i => realEvaluation θ (D.X p i)),
        p.2.2.1*realEvaluation θ D.lam+p.2.2.2)+
          realEvaluation θ D.eta • imaginaryVector p.2.1 := by
  funext i
  rw [bishopDisc_boundary (D.equation p hp).1 θ i,(D.equation p hp).2 θ i]
  simp only [graphPoint,imaginaryVector,Pi.add_apply,Pi.smul_apply,Complex.real_smul,
    Complex.ofReal_add,Complex.ofReal_mul]
  ring

lemma bishop_path_interior {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hCP : DiscContinuityWithin k Ω ε)
    (p : Icc (0 : ℝ) 1 → BishopParams k) (hp : Continuous p)
    (hpr : ∀ s, p s ∈ ball 0 D.radius)
    (hbd : ∀ s θ, (fun i => bishopDisc D.Y (p s) i
      ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩) ∈ Ω)
    (hstart : ∀ z, (fun i => bishopDisc D.Y (p ⟨0,by simp⟩) i z) ∈ Ω) :
    ∀ s z, (fun i => bishopDisc D.Y (p s) i z) ∈ Ω := by
  apply hCP
  · have hc : ContinuousOn (bishopDisc D.Y) (ball 0 D.radius) := by
      intro q hq
      exact (bishopDisc_contDiffAt_at
        ((D.smoothY q hq).contDiffAt (isOpen_ball.mem_nhds hq))).continuousAt.continuousWithinAt
    have hB : Continuous (fun s => bishopDisc D.Y (p s)) := hc.comp_continuous hp hpr
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp (hB.comp continuous_fst)).eval continuous_snd
  · intro s
    refine ⟨fun z i => ((p s).1 i : ℂ)+discValue (D.Y (p s) i) z,
      bishopDisc_analytic D.Y (p s),?_⟩
    intro z
    funext i
    change constantDisc ((p s).1 i) z+schwarz (D.Y (p s) i) z = _
    rw [constantDisc_apply,← discValue_eq _ z.property]
  · intro s z
    exact lt_of_le_of_lt (bishopDisc_eval_norm_le D.Y (p s) z) (D.small (p s) (hpr s)).2.2
  · intro s z hz
    obtain ⟨θ,hθ⟩ := fourier_one_surjective_sphere hz
    have heq : z = ⟨fourier 1 θ,fourier_mem_closedDisc θ⟩ := Subtype.ext hθ.symm
    simpa only [heq] using hbd s θ
  · exact hstart

end Release061.Wiener

end

end OAI
