import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicLocallyUniformLimit

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
open Set Filter Metric
open scoped Topology

theorem IsSmooth.identity_principle {n m : ℕ} {S : Set (Affine n)}
    (hs : IsSmooth S) (hc : IsPreconnected S) {f : S → Affine m}
    (hf : HolomorphicOnSubset S f) {p : S} (hp : f =ᶠ[𝓝 p] 0) :
    ∀ q, f q = 0 := by
  let A : Set S := interior {q | f q = 0}
  have hAo : IsOpen A := isOpen_interior
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro q hq
    obtain ⟨d,W,hWS,hWo,hqW,D,hD,⟨e⟩⟩ := hs q
    let g : D → S := Set.inclusion hWS ∘ e.toHomeomorph.symm
    have hg : Topology.IsOpenEmbedding g :=
      (Topology.IsOpenEmbedding.inclusion hWS hWo).comp e.toHomeomorph.symm.isOpenEmbedding
    let a : D := e.toHomeomorph ⟨q.val,hqW⟩
    have hga : g a = q := by simp [g,a,Set.inclusion]
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hD a.val a.property
    let B : Set D := Subtype.val ⁻¹' ball a.val r
    have hBo : IsOpen B := isOpen_ball.preimage continuous_subtype_val
    have haB : a ∈ B := mem_ball_self hr
    have hqg : q ∈ g '' B := hga ▸ mem_image_of_mem g haB
    obtain ⟨b,hbg,hbA⟩ := (_root_.mem_closure_iff.mp hq) (g '' B) (hg.isOpenMap _ hBo) hqg
    obtain ⟨y,hyB,hyb⟩ := hbg
    have hfy : f ∘ g =ᶠ[𝓝 y] 0 := by
      have hz : f =ᶠ[𝓝 b] 0 := mem_interior_iff_mem_nhds.mp hbA
      rw [← hyb] at hz
      exact hz.comp_tendsto hg.continuous.continuousAt.tendsto
    let F := ambientExtend (f ∘ g)
    have hF : AnalyticOnNhd ℂ F D :=
      ((hf.restrict hWS).comp e.holomorphic_invFun).analyticOnNhd_extend hD
    have hFy : F =ᶠ[𝓝 y.val] 0 := by
      rw [← hD.isOpenEmbedding_subtypeVal.map_nhds_eq y]
      change (fun t : D => F t.val) =ᶠ[𝓝 y] 0
      simpa only [F,ambientExtend_apply] using hfy
    have hzero := (hF.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball a.val r).isPreconnected hyB hFy
    apply ((hg.isOpenMap _ hBo).subset_interior_iff.mpr ?_) hqg
    rintro t ⟨z,hz,rfl⟩
    change f (g z) = 0
    have ht := hzero hz
    simpa only [F,ambientExtend_apply,Function.comp_apply,Pi.zero_apply] using ht
  let : PreconnectedSpace S := Subtype.preconnectedSpace hc
  have hpu : p ∈ A := mem_interior_iff_mem_nhds.mpr hp
  have hAu : A = univ := (show IsClopen A from ⟨hAc,hAo⟩).eq_univ ⟨p,hpu⟩
  intro q
  exact (interior_subset (s := {q | f q = 0})) (show q ∈ A by rw [hAu]; trivial)

end

open Set Filter
open scoped Topology

theorem IsSmooth.vanishingIdeal_isPrime {n : ℕ} {S : Set (Affine n)}
    (hs : IsSmooth S) (hc : IsConnected S) :
    (MvPolynomial.vanishingIdeal ℂ S).IsPrime := by
  constructor
  · intro htop
    obtain ⟨p,hp⟩ := hc.nonempty
    have he : (1 : MvPolynomial (Fin n) ℂ) ∈ MvPolynomial.vanishingIdeal ℂ S := by
      rw [htop]; trivial
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using he p hp)
  · intro P Q hPQ
    by_cases hP : P ∈ MvPolynomial.vanishingIdeal ℂ S
    · exact Or.inl hP
    right
    have hex : ∃ p ∈ S, MvPolynomial.eval p P ≠ 0 := by
      change ¬ ∀ p ∈ S, MvPolynomial.eval p P = 0 at hP
      push Not at hP
      exact hP
    obtain ⟨a,ha,haP⟩ := hex
    let p : S := ⟨a,ha⟩
    let f : S → Affine 1 := fun x _ => MvPolynomial.eval x.val Q
    have hf : HolomorphicOnSubset S f := by
      intro x
      refine ⟨univ,isOpen_univ,mem_univ _,fun z _ => MvPolynomial.eval z Q,?_,?_⟩
      · intro z _
        exact analyticAt_pi_iff.mpr fun _ => (AnalyticOnNhd.eval_mvPolynomial Q) z (mem_univ _)
      · intro y _; rfl
    have hn : ∀ᶠ x : S in 𝓝 p, MvPolynomial.eval x.val P ≠ 0 := by
      exact (P.continuous_eval.comp continuous_subtype_val).continuousAt.eventually_ne haP
    have hz : f =ᶠ[𝓝 p] 0 := by
      filter_upwards [hn] with x hx
      have hmul := hPQ x.val x.property
      have hQ : MvPolynomial.eval x.val Q = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left hx
        simpa using hmul
      ext i
      exact hQ
    have hh := hs.identity_principle hc.isPreconnected hf hz
    intro x hx
    exact congrFun (hh ⟨x,hx⟩) 0

end Release061

end

end OAI
