import Mathlib
import OAI.Analysis.SymmetricDomains.ProductCurveLocalAutomorphism

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
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

 theorem ambientAut_uniform_at_zero (hU : IsOpen U) [LocallyCompactSpace U]
    (g : ℝ → Biholomorph U U) (hg : ContinuousAt g 0) (hg0 : g 0=1)
    (p : U) {S : Set (Affine n)} (hS : S∈𝓝 p.val) :
    ∃ ε > (0:ℝ), ∀ t, |t|<ε → ∀ x∈ball p.val ε, (g t).ambientAut x∈S := by
  have hh : ContinuousAt (fun z : ℝ × Affine n => (g z.1).ambientAut z.2) (0,p.val) :=
    (ambientAut_joint_continuousAt hU p.property).comp
      ((hg.comp (f := fun z : ℝ × Affine n => z.1) continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
  have heq : (g 0).ambientAut p.val=p.val := by rw [hg0,ambientAut_apply,one_apply]
  have hhS := hh (show S∈𝓝 ((g 0).ambientAut p.val) from heq.symm ▸ hS)
  obtain ⟨ε,hε,hhε⟩ := Metric.mem_nhds_iff.mp hhS
  refine ⟨ε,hε,?_⟩
  intro t ht x hx
  apply hhε (a := (t,x))
  simpa only [mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using And.intro ht hx

theorem local_automorphism_ODE_group_law (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U) (X : Affine n → Affine n)
    (hX : AnalyticOnNhd ℂ X U)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ ε > (0:ℝ), ε<δ ∧ ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t := by
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val p.property).contDiffAt.restrict_scalars ℝ
  obtain ⟨L,K,hK,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨ρ,hρ,hρK⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (inter_mem hK (ball_mem_nhds p.val hr))
  obtain ⟨ε₀,hε₀,hstep₀⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hρ)
  obtain ⟨ε₁,hε₁,hstep₁⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hε₀)
  let ε : ℝ := min (δ/3) (min (ε₀/3) ε₁)
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) hε₁)
  have hεδ : ε≤δ/3 := min_le_left _ _
  have hεε₀ : ε≤ε₀/3 := (min_le_right _ _).trans (min_le_left _ _)
  have hεε₁ : ε≤ε₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,by linarith,?_⟩
  intro s t hs ht
  apply eq_of_ambientAut_eventuallyEq hU hc p
  filter_upwards [ball_mem_nhds p.val (lt_min hε₀ (lt_min hε₁ hr))] with x hx
  have hx₀ : x∈ball p.val ε₀ := ball_subset_ball (min_le_left _ _) hx
  have hx₁ : x∈ball p.val ε₁ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx
  have hxr : x∈closedBall p.val r := ball_subset_closedBall
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx)
  have hxu : x∈U := hball hxr
  have htx : (g t).ambientAut x∈ball p.val ε₀ := hstep₁ t (ht.trans_le hεε₁) x hx₁
  have htxr : (g t).ambientAut x∈closedBall p.val r := ball_subset_closedBall
    (hρK (hstep₀ t (by linarith) x hx₀)).2
  have hs' : s∈Ioo (-ε) ε := abs_lt.mp hs
  have ht' : t∈Ioo (-ε) ε := abs_lt.mp ht
  have hsum {u : ℝ} (hu : u∈Ioo (-ε) ε) : u+t∈Ioo (-δ) δ ∧ |u+t|<ε₀ := by
    have ha := abs_add_le u t
    have hu' : |u|<ε := abs_lt.mpr hu
    constructor
    · constructor <;> linarith [ht'.1,ht'.2,hu.1,hu.2]
    · linarith
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun (_ : ℝ) y => X y) (s := fun _ => K) (a := -ε) (b := ε) (t₀ := 0)
    (fun _ _ => hL) (show (0:ℝ)∈Ioo (-ε) ε from ⟨by linarith,hε⟩)
    (f := fun u => (g (u+t)).ambientAut x)
    (g := fun u => (g u).ambientAut ((g t).ambientAut x))
    (fun u hu => ⟨by
      have hshift : HasDerivAt (fun v : ℝ => v+t) 1 u := by simpa only [id_eq] using (hasDerivAt_id u).add_const t
      have hh := (hd x hxr (u+t) (hsum hu).1).hasDerivAt.scomp u hshift
      simpa only [Function.comp_def,one_smul] using hh,
      (hρK (hstep₀ (u+t) (hsum hu).2 x hx₀)).1⟩)
    (fun u hu => ⟨(hd _ htxr u (by constructor <;> linarith [hu.1,hu.2])).hasDerivAt,
      (hρK (hstep₀ u (by have hh := abs_lt.mpr hu; linarith) _ htx)).1⟩)
    (by
      rw [zero_add,hg0]
      rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,one_apply])
  have hh := heq hs'
  dsimp only at hh
  rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,
    ← mul_apply,← ambientAut_apply] at hh
  exact hh

end Biholomorph
end Release061

open Set Filter Topology

end

end OAI
