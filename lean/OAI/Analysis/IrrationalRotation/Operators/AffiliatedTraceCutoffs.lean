import OAI.Analysis.IrrationalRotation.Operators.ProjectionMeetTrace

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal
namespace Invariant233.AffiliatedTraceCutoffs
open InvariantRotation.AffiliatedTransport
open InvariantRotation.ClosedRangeTransport
open TracialProjectionTransport ProjectionMeetTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem trace_lower_of_cutoff
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (p E : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace E]
    (hp : p.starProjection ∈ M) (hE : E.starProjection ∈ M)
    (hED : E ≤ T.domain) (F : H →L[ℂ] H) (hF : F ∈ M)
    (hTF : ∀ x : E, T ⟨x, hED x.property⟩ = F x)
    (L : ℝ≥0) (hlower : ∀ x : E, ‖x‖ ≤ L * ‖F x‖) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ E.starProjection).re - 1 ≤
      (vectorTrace ξ (transported T p).starProjection).re := by
  let r := p ⊓ E
  have hrD : r ≤ T.domain := inf_le_right.trans hED
  have hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ ‖F‖ * ‖x‖ := by
    intro x
    rw [hTF ⟨x, x.property.2⟩]
    exact F.le_opNorm x
  have hlower' : ∀ x : r, ‖x‖ ≤ L * ‖T ⟨x, hrD x.property⟩‖ := by
    intro x
    rw [hTF ⟨x, x.property.2⟩]
    exact hlower ⟨x, x.property.2⟩
  have hrmem : r.starProjection ∈ M := meet_projection_mem M p E hp hE
  have hforward : forward r (cutoffMap T r hrD ‖F‖ hupper) = F * r.starProjection := by
    ext x
    exact hTF ⟨r.starProjection x, (r.starProjection_apply_mem x).2⟩
  have hforwardmem : forward r (cutoffMap T r hrD ‖F‖ hupper) ∈ M := by
    rw [hforward]
    exact mul_mem hF hrmem
  exact (faithful_vectorTrace_meet_lower_bound M ξ hξ p E hp hE).trans
    (cutoff_trace_le_transported M ξ hξ T p r inf_le_left hrD ‖F‖ hupper L
      hlower' hrmem hforwardmem)

theorem vectorTrace_transported_eq_of_cutoffs
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (hT : T.IsFormalAdjoint T) (hinj : T.toFun.ker = ⊥)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M)
    (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hE : ∀ n, (E n).starProjection ∈ M)
    (hlim : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hED : ∀ n, E n ≤ T.domain) (hEinvD : ∀ n, E n ≤ T.inverse.domain)
    (F G : ℕ → H →L[ℂ] H) (hF : ∀ n, F n ∈ M) (hG : ∀ n, G n ∈ M)
    (hTF : ∀ n, ∀ x : E n, T ⟨x, hED n x.property⟩ = F n x)
    (hTG : ∀ n, ∀ x : E n, T.inverse ⟨x, hEinvD n x.property⟩ = G n x)
    (L R : ℕ → ℝ≥0)
    (hlower : ∀ n, ∀ x : E n, ‖x‖ ≤ L n * ‖F n x‖)
    (hinvlower : ∀ n, ∀ x : E n, ‖x‖ ≤ R n * ‖G n x‖) :
    vectorTrace ξ (transported T p).starProjection = vectorTrace ξ p.starProjection := by
  have hpperp : pᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def] using
      (sub_mem (one_mem M) hp : (1 : H →L[ℂ] H) - p.starProjection ∈ M)
  have hortho := inverse_transported_le_orthogonal T p hT hinj
  apply Eq.symm
  apply vectorTrace_eq_of_cutoff_estimates ξ p (transported T p) E hlim
  · intro n
    simpa only [hξ.1, one_pow] using
      trace_lower_of_cutoff M ξ hξ T p (E n) hp (hE n) (hED n)
        (F n) (hF n) (hTF n) (L n) (hlower n)
  · intro n
    have hcut := trace_lower_of_cutoff M ξ hξ T.inverse pᗮ (E n)
      hpperp (hE n) (hEinvD n) (G n) (hG n) (hTG n) (R n) (hinvlower n)
    have hmono := vectorTrace_projection_mono ξ hortho
    simpa only [hξ.1, one_pow] using hcut.trans hmono

theorem commutant_equivariance_of_graph_cutoffs
    (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H) (hclosed : T.IsClosed)
    (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hED : ∀ n, E n ≤ T.domain)
    (hlim : ∀ x : H, Tendsto (fun n => (E n).starProjection x) atTop (𝓝 x))
    (F : ℕ → H →L[ℂ] H) (hF : ∀ n, F n ∈ M)
    (hTF : ∀ n x, T ⟨(E n).starProjection x,
      hED n ((E n).starProjection_apply_mem x)⟩ = F n x)
    (hgraphlim : ∀ x : T.domain,
      Tendsto (fun n => F n x) atTop (𝓝 (T x)))
    (W : H →L[ℂ] H) (hW : W ∈ M.commutant) (x : T.domain) :
    ∃ hx : W x ∈ T.domain, T ⟨W x, hx⟩ = W (T x) := by
  have hWF : ∀ n, W * F n = F n * W := by
    intro n
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hW) (F n) (hF n) |>.symm
  have hsecond : Tendsto (fun n => F n (W x)) atTop (𝓝 (W (T x))) := by
    have ht := W.continuous.continuousAt.tendsto.comp (hgraphlim x)
    convert ht using 1
    funext n
    exact congrArg (fun A : H →L[ℂ] H => A x) (hWF n).symm
  have hpair : ∀ n, ((E n).starProjection (W x), F n (W x)) ∈ T.graph := by
    intro n
    apply T.mem_graph_iff.mpr
    exact ⟨⟨(E n).starProjection (W x), hED n ((E n).starProjection_apply_mem _)⟩,
      rfl, hTF n (W x)⟩
  have hlimit := (hlim (W x)).prodMk_nhds hsecond
  have hmem : (W x, W (T x)) ∈ T.graph :=
    hclosed.mem_of_tendsto hlimit (Filter.Eventually.of_forall hpair)
  obtain ⟨y, hy, hTy⟩ := T.mem_graph_iff.mp hmem
  change (y : H) = W x at hy
  have hx : W x ∈ T.domain := by rw [← hy]; exact y.property
  refine ⟨hx, ?_⟩
  have hy' : y = ⟨W x, hx⟩ := Subtype.ext hy
  rw [← hy']
  exact hTy

theorem transported_projection_mem_of_graph_cutoffs
    (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H) (hclosed : T.IsClosed)
    (p : Submodule ℂ H) [p.HasOrthogonalProjection] (hp : p.starProjection ∈ M)
    (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hED : ∀ n, E n ≤ T.domain)
    (hlim : ∀ x : H, Tendsto (fun n => (E n).starProjection x) atTop (𝓝 x))
    (F : ℕ → H →L[ℂ] H) (hF : ∀ n, F n ∈ M)
    (hTF : ∀ n x, T ⟨(E n).starProjection x,
      hED n ((E n).starProjection_apply_mem x)⟩ = F n x)
    (hgraphlim : ∀ x : T.domain,
      Tendsto (fun n => F n x) atTop (𝓝 (T x))) :
    (transported T p).starProjection ∈ M := by
  have heq := commutant_equivariance_of_graph_cutoffs M T hclosed E hED hlim F hF hTF hgraphlim
  let hD : ∀ W ∈ M.commutant, ∀ x ∈ T.domain, W x ∈ T.domain :=
    fun W hW x hx => (heq W hW ⟨x, hx⟩).choose
  apply transported_projection_mem M T p hp hD
  intro W hW x
  exact (heq W hW x).choose_spec

end Invariant233.AffiliatedTraceCutoffs

end

end OAI
