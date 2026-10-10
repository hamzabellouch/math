import OAI.Analysis.FactorGeneration.NormalTrace
import OAI.Analysis.FactorGeneration.TraceTransport
import OAI.Analysis.RelativeGeneration.ConditionalMembership

namespace OAI

noncomputable section

/- Original-factor relative transport. The forward direction is
   proved from concrete strong approximation and the constructed trace, not
   from a postulated representation/normality interface. -/
open Filter
open scoped Topology
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)
local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

/-- Strong convergence in the original representation implies trace-vector
convergence in the constructed representation. No norm bound or ambient
Hilbert-space separability is assumed. The finite-vector formula is already
proved for the faithful normalized trace of an original II₁ factor. -/
theorem traceFreeHilbertVector_tendsto_of_strong
    {I : Type*} (l : Filter I) (a : I → M.toStarSubalgebra) (x : M.toStarSubalgebra)
    (ha : ∀ v : H, Tendsto (fun i => (a i).val v) l (𝓝 (x.val v))) :
    Tendsto (fun i => π (a i) Ω) l (𝓝 (π x Ω)) := by
  obtain ⟨n,ξ,η,htrace⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have hnorm (b : M.toStarSubalgebra) :
      ‖π b Ω‖^2 = ∑ j, (inner ℂ (b.val (η j)) (b.val (ξ j))).re := by
    rw [traceFreeHilbertAction_vector, LinearIsometry.norm_map,
      traceFreeCopy_norm_sq, htrace, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (inner ℂ (η j) (star b.val (b.val (ξ j)))).re = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hdiffv (v : H) : Tendsto (fun i => ((a i)-x).val v) l (𝓝 0) := by
    change Tendsto (fun i => (a i).val v-x.val v) l (𝓝 0)
    simpa only [sub_self] using (ha v).sub
      (tendsto_const_nhds : Tendsto (fun _ : I => x.val v) l (𝓝 (x.val v)))
  have hs : Tendsto (fun i => ‖π (a i-x) Ω‖^2) l (𝓝 0) := by
    simp_rw [hnorm]
    have hh := tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => (Complex.continuous_re.tendsto _).comp ((hdiffv (η j)).inner (hdiffv (ξ j))))
    simpa only [Function.comp_apply,inner_zero_left, Complex.zero_re, Finset.sum_const_zero] using hh
  have hn : Tendsto (fun i => ‖π (a i-x) Ω‖) l (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simpa only [dist_eq_norm, map_sub, sub_apply] using hn

/-- Forward closure transport, with the actual conditional expectation used
   to pass from trace-vector closure back to bounded-algebra membership. -/
theorem traceFreeHilbert_mem_of_wstar
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAM : A ≤ M.toStarSubalgebra)
    (Q : VonNeumannAlgebra K) (hQR : Q ≤ R)
    (hAQ : ∀ a : M.toStarSubalgebra, a.val ∈ A → π a ∈ Q)
    (x : M.toStarSubalgebra) (hx : x.val ∈ wstar (A : Set (H →L[ℂ] H))) :
    π x ∈ Q := by
  classical
  have hxb : x.val ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    rwa [wstar_starAlgebra_eq_bicommutant] at hx
  obtain ⟨a,ha⟩ := bicommutant_exists_strong_net A x.val hxb
  let b : Finset H × ℕ → M.toStarSubalgebra := fun i => ⟨(a i).val,hAM (a i).property⟩
  have hb := traceFreeHilbertVector_tendsto_of_strong hfactor hdiff hfinite hunit atTop b x ha
  apply mem_subalgebra_of_baseVector_mem σ hQR (e x)
  apply (Submodule.isClosed_topologicalClosure (vectorOrbitMap Q.toStarSubalgebra Ω).range).mem_of_tendsto hb
  exact Eventually.of_forall fun i =>
    Submodule.le_topologicalClosure _ ⟨⟨π (b i),hAQ (b i) (a i).property⟩,rfl⟩

/-- The preimage of a represented von Neumann subalgebra is genuinely WOT
closed, proved from the actual constructed representation. -/
theorem traceFreeHilbert_preimage_wotClosed
    (Q : VonNeumannAlgebra K) (hQR : Q ≤ R) :
    WOTClosed (concretePreimage (e).toStarAlgHom Q.toStarSubalgebra) := by
  let A := concretePreimage (e).toStarAlgHom Q.toStarSubalgebra
  have hAM : A ≤ M.toStarSubalgebra := concretePreimage_le _ _
  have heq : wstar (A : Set (H →L[ℂ] H)) = A := by
    refine le_antisymm ?_ (show A ≤ wstar (A : Set (H →L[ℂ] H)) from subset_wstar _)
    intro x hx
    have hxM : x ∈ M.toStarSubalgebra := wstar_le (vonNeumann_wotClosed M) hAM hx
    apply (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra ⟨x,hxM⟩).mpr
    exact traceFreeHilbert_mem_of_wstar hfactor hdiff hfinite hunit A hAM Q hQR
      (fun a ha => (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra a).mp ha)
      ⟨x,hxM⟩ hx
  change WOTClosed A
  rw [← heq]
  exact wstar_closed _

end Generator.Tracial

end

end OAI
