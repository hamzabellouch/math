import Mathlib
import OAI.Analysis.SymmetricDomains.CompactFaithfulIsotropy
import OAI.Analysis.SymmetricDomains.HolomorphicIdSmallIterates

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

namespace Biholomorph
open Set Filter Metric Topology
variable {n : ℕ} {U : Set (Affine n)}

lemma ambientAut_pow_apply (a : Biholomorph U U) (j : ℕ) (p : U) :
    (a^j).ambientAut p.val=a.ambientAut^[j] p.val := by
  induction j generalizing p with
  | zero => simp only [pow_zero,ambientAut_apply,one_apply,Function.iterate_zero,id_eq]
  | succ j hj =>
    rw [pow_succ,ambientAut_apply,mul_apply,← ambientAut_apply, hj]
    rw [Function.iterate_succ_apply,ambientAut_apply]

theorem no_small_subgroups (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U] (p : U) :
    ∃ W : Set (Biholomorph U U), W ∈ 𝓝 1 ∧
      ∀ H : Subgroup (Biholomorph U U), (H : Set (Biholomorph U U)) ⊆ W → H=⊥ := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds p.property)
  let R := r/2
  have hR : 0 < R := half_pos hr
  have hKU : closedBall p.val R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hrU
  have hconv := ambientAut_tendstoLocallyUniformly
    (show Tendsto (id : Biholomorph U U → Biholomorph U U) (𝓝 1) (𝓝 1) from tendsto_id)
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_closedBall p.val R)).mp (hconv.mono hKU)
  let W : Set (Biholomorph U U) :=
    {a | ∀ x ∈ closedBall p.val R, ‖a.ambientAut x-x‖ < R/16}
  have hW : W ∈ 𝓝 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (R/16) (by positivity)] with a ha
    intro x hx
    have hh := ha x hx
    simpa only [id_eq,ambientAut_apply 1 ⟨x,hKU hx⟩,one_apply,dist_eq_norm,norm_sub_rev] using hh
  refine ⟨W,hW,?_⟩
  intro H hHW
  apply le_antisymm _ bot_le
  intro a ha
  change a=1
  have he : EqOn a.ambientAut id U := by
    apply holomorphic_eq_id_of_small_iterates hU hc hb (a.ambientAut_analytic hU)
      (fun x hx => by
        rw [ambientAut_apply a ⟨x,hx⟩]
        exact (a.toHomeomorph ⟨x,hx⟩).property) hR (ball_subset_closedBall.trans hKU)
    intro j x hx
    rw [← ambientAut_pow_apply a j ⟨x,hKU (ball_subset_closedBall hx)⟩]
    exact le_of_lt (hHW (H.pow_mem ha j) x (ball_subset_closedBall hx))
  apply ext
  intro x
  apply Subtype.ext
  simpa only [ambientAut_apply,id_eq,one_apply] using he x.property

end Biholomorph

open Set Filter Topology
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem involution_derivative_neg_id {f : E → E} {p : E} {A : E →L[ℂ] E}
    (hf : HasStrictFDerivAt f A p) (hp : f p=p)
    (hinv : ∀ᶠ x in 𝓝 p, f (f x)=x)
    (hiso : ∀ᶠ x in 𝓝 p, f x=x → x=p) : A = -1 := by
  have hff : HasFDerivAt (f ∘ f) (A.comp A) p := by
    have hh : HasFDerivAt f A (f p) := hp.symm ▸ hf.hasFDerivAt
    exact hh.comp p hf.hasFDerivAt
  have hA2 : A.comp A=1 := by
    have heq : (f ∘ f) =ᶠ[𝓝 p] id := hinv
    exact hff.unique ((hasFDerivAt_id p).congr_of_eventuallyEq heq)
  have hAA (x : E) : A (A x)=x := congrArg (fun L : E →L[ℂ] E => L x) hA2
  let φ : E → E := fun x => (1/2 : ℂ) • ((x-p)+A (f x-p))
  have hφp : φ p=0 := by simp [φ,hp]
  have hφder : HasStrictFDerivAt φ ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p := by
    have hh := (((hasStrictFDerivAt_id p).sub_const p).add
      (A.hasStrictFDerivAt.comp p (hf.sub_const p))).const_smul (1/2 : ℂ)
    convert hh using 1
    · rfl
    · change (1 : E →L[ℂ] E)=(1/2 : ℂ) • (1+A.comp A)
      rw [hA2]
      module
  have hcomm : ∀ᶠ x in 𝓝 p, φ (f x)=A (φ x) := by
    filter_upwards [hinv] with x hx
    simp only [φ,hx,map_smul,map_add,hAA]
    congr 1
    abel
  let ψ := hφder.localInverse φ (ContinuousLinearEquiv.refl ℂ E) p
  have hψ : Tendsto ψ (𝓝 0) (𝓝 p) := by
    simpa only [hφp] using hφder.localInverse_tendsto
  have hright : ∀ᶠ y in 𝓝 0, φ (ψ y)=y := by
    simpa only [hφp] using hφder.eventually_right_inverse
  have hleft : ∀ᶠ x in 𝓝 p, ψ (φ x)=x := hφder.eventually_left_inverse
  have hfc : Tendsto f (𝓝 p) (𝓝 p) := by simpa only [hp] using hf.continuousAt.tendsto
  have hleftf : ∀ᶠ x in 𝓝 p, ψ (φ (f x))=f x := hfc hleft
  have hzero : ∀ᶠ y in 𝓝 0, A y=y → y=0 := by
    filter_upwards [hright,hψ (hleftf.and (hcomm.and hiso))] with y hy hq hfix
    obtain ⟨hfl,hc,hi⟩ := hq
    have hfy : f (ψ y)=ψ y := by
      rw [hc,hy,hfix] at hfl
      exact hfl.symm
    have hqy := hi hfy
    rw [hqy,hφp] at hy
    exact hy.symm
  have hfixed : ∀ v : E, A v=v → v=0 := by
    intro v hv
    have ht : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℂ => t • v) := by fun_prop
      simpa only [zero_smul] using hcont.tendsto (0 : ℂ)
    have he : ∀ᶠ t : ℂ in 𝓝 0, t • v=0 := by
      filter_upwards [ht hzero] with t ht'
      exact ht' (by simp only [map_smul,hv])
    have he' := he.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    obtain ⟨t,ht,hne⟩ := (he'.and self_mem_nhdsWithin).exists
    exact (smul_eq_zero.mp ht).resolve_left (by simpa using hne)
  ext v
  have hh := hfixed (A v+v) (by simp only [map_add,hAA]; abel)
  simpa using eq_neg_of_add_eq_zero_left hh

end Release061

end

end OAI
