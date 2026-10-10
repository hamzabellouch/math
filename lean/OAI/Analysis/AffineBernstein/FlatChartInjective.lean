import Mathlib
import OAI.Analysis.AffineBernstein.FlatSupportImmersion

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/- Flat normalization removes exactly the radial ambiguity of the actual
Gauss inverse. This is global on each compact positive fiber. -/
theorem affineEpigraph_gaussPoint_injective_flat {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e₁ e₂ d : E}
    (h₁ : inner ℝ e₁ d = 1) (h₂ : inner ℝ e₂ d = 1)
    (he : gaussPoint {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e₁ =
      gaussPoint {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e₂) : e₁ = e₂ := by
  have hn₁ : e₁ ≠ 0 := by intro h; simp [h] at h₁
  have hn₂ : e₂ ≠ 0 := by intro h; simp [h] at h₂
  obtain ⟨_,_,c₁,hc₁,hc₁e⟩ := affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hs hn₁
  obtain ⟨_,_,c₂,hc₂,hc₂e⟩ := affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hs hn₂
  rw [he] at hc₁e
  have hh : c₁ • InnerProductSpace.toDual ℝ E e₁ = c₂ • InnerProductSpace.toDual ℝ E e₂ :=
    hc₁e.symm.trans hc₂e
  have hc : c₁ = c₂ := by
    have hx := congrArg (fun f : E →L[ℝ] ℝ => f d) hh
    simpa only [smul_apply,InnerProductSpace.toDual_apply_apply,smul_eq_mul,h₁,h₂,mul_one] using hx
  rw [← hc] at hh
  exact (InnerProductSpace.toDual ℝ E).injective ((smul_right_injective _ hc₁.ne') hh)

/- The flat support parametrization is globally one-to-one after projection
to the original graph domain, not merely a local immersion. -/
theorem affineEpigraph_flat_graph_injective {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0) :
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    Set.InjOn (fun x : Space n => (a+L (supportParam Y (q₀+J x))).1)
      {x | (q₀+J x).1 ∈ B} := by
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  obtain ⟨_,_,hg,_⟩ := affineEpigraph_flat_parametrization hΩ hcv hu hp a L hB hK hzero
    q₀ d hd J hi hJ
  change Set.InjOn (fun x : Space n => (a+L (supportParam Y (q₀+J x))).1) _
  intro x hx y hy hxy
  have hab : a+L (supportParam Y (q₀+J x)) = a+L (supportParam Y (q₀+J y)) :=
    Prod.ext hxy ((hg x hx).2.trans ((congrArg u hxy).trans (hg y hy).2.symm))
  have hpq : supportParam Y (q₀+J x) = supportParam Y (q₀+J y) :=
    L.injective (add_left_cancel hab)
  have hs : (q₀+J x).1 = (q₀+J y).1 := by
    simpa only [supportParam] using congrArg Prod.fst hpq
  have heq : Y (q₀+J x) = Y (q₀+J y) := congrArg Prod.snd hpq
  have hq (z : Space n) : inner ℝ (q₀+J z).2 d = 1 := by simp [inner_add_left,hd,hJ]
  have he : (q₀+J x).2 = (q₀+J y).2 := by
    apply affineEpigraph_gaussPoint_injective_flat hΩ hcv hu hp a L hB hK hzero hy (hq x) (hq y)
    change gaussPoint _ _ = gaussPoint _ _ at heq
    rw [hs] at heq
    exact heq
  exact hi (add_left_cancel (Prod.ext hs he))

end AffineBernstein
end

end OAI
