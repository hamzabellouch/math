import Mathlib
import OAI.Analysis.AffineBernstein.NoNormalizedMaximalModel
import OAI.Analysis.AffineBernstein.NoZeroTransverse

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section MaximalModelExclusion
/-- Choose orthonormal transverse coordinates without changing the Euclidean
norm used by the spherical fiber estimates. -/
def transverseEuclideanIsometry {m d : ℕ} (hmd : m = d+1) :
    WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m := by
  have hdim : Module.finrank ℝ (WithLp 2 (Space d × ℝ)) = m := by
    rw [(WithLp.linearEquiv 2 ℝ (Space d × ℝ)).finrank_eq]
    simp [Module.finrank_prod,finrank_euclideanSpace,hmd]
  exact ((stdOrthonormalBasis ℝ (WithLp 2 (Space d × ℝ))).reindex (finCongr hdim)).repr

/-- Normalization of an actual maximal model, followed by the full sigma
mass/growth contradiction, excludes every maximal direction number at least two. -/
theorem affineMaximal_maximal_model_directions_le_one {n k m : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
    (hmax : ∀ r d : ℕ, ∀ C' : Set (Space r × Space d),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → r ≤ k) : k ≤ 1 := by
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have hm : 1 ≤ m := complete_affineMaximal_model_transverse_pos (by omega)
    hΩ hne hcv hu hp hmP hcomplete hC hf
  let d := m-1
  have hmd : m = d+1 := by dsimp [d]; omega
  have hdim := model_dimension hf
  have hnk : n = k+d := by
    simp only [Module.finrank_prod,finrank_euclideanSpace,Module.finrank_self,Fintype.card_fin] at hdim
    omega
  let e : Fin n ≃ Fin k ⊕ Fin d := Fintype.equivOfCardEq (by simp [hnk])
  let eE : Fin m ≃ Fin d ⊕ Unit := Fintype.equivOfCardEq (by simp [hmd])
  let f := transverseEuclideanIsometry hmd
  have hmax' : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False := by
    intro d' _ C' hC' hf'
    have hh := hmax (k+1) d' C' hC' hf'
    omega
  have hcl := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hned : (sourceEpigraph Ω u).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,u x),hx,le_rfl⟩
  obtain ⟨c,hc,hnorm⟩ := uniform_model_fiber_normalization hm hcl hned hmax'
  let s : Space k := WithLp.toLp 2 (fun _ => (1:ℝ))
  have hs : ∀ i, 0 < s i := by intro i; norm_num [s]
  obtain ⟨A,hC',hf',hin,hout⟩ := hnorm C hC hf s hs
  obtain ⟨a,L,hlim⟩ := hf'.epigraph_pullback_approximation
  exact affineMaximal_no_normalized_maximal_model hn hn9 hk2 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax' a L hC' hf' hlim
    (by positivity : 0 < 2/(c+1)) hin hout

/-- Every actual affine-limit model has at most one orthant direction in n=3,...,9.
This is Proposition one-direction, including the originally missing producers. -/
theorem affineMaximal_model_directions_le_one {n k m : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) : k ≤ 1 := by
  obtain ⟨x,hx⟩ := hne
  have h1 : ∃ m, ∃ C : Set (Space 1 × Space m), IsModelShape C ∧
      InAffineLimitFamily (sourceEpigraph Ω u) C :=
    ⟨n,_,tangent_epigraph_isModelShape hΩ hcv hu hp hcomplete hx,
      tangent_epigraph_in_family hΩ hcv hu hp hcomplete hx⟩
  obtain ⟨k',m',C',hk',hC',hf',hmax⟩ := exists_maximal_model h1
  exact (hmax k m C hC hf).trans
    (affineMaximal_maximal_model_directions_le_one hn hn9 hΩ ⟨x,hx⟩ hcv
      hu hp hmP hcomplete hC' hf' hmax)

/-- Full uniform section balance, produced from the original hypotheses. -/
theorem affineMaximal_section_balance {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance Ω u ρ := by
  apply sectionBalance_of_no_two_model hΩ hne hcv hu hp hc
  intro d _ C hC hf
  have hh := affineMaximal_model_directions_le_one hn hn9 hΩ hne hcv hu hp hm hc hC hf
  omega
end MaximalModelExclusion


end
end AffineBernstein
end

end OAI
