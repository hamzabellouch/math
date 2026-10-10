import OAI.Geometry.SurfaceImmersion.Correction.CompactModeCoefficients
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveData
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds

namespace OAI

/-! Build the actual polynomial phase solver from compact geometric data.
All coefficient profiles precede the amplitude and frequency parameters. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes

theorem compact_polynomial_solve_data {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {U : Set Base} (hU : IsOpen U) {O Q : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGQ : MapsTo (lowJet G) U Q)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {KU : Set Base} (hKUc : IsCompact KU) (hUK : U ⊆ KU)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    {ΩE ΩV KE KV : Set SmallModes.Base} (hΩE : IsOpen ΩE)
    (hKE : IsCompact KE) (hKV : IsCompact KV)
    (hEK : e.source ⊆ KE) (hVK : e.target ⊆ KV) (hKEΩ : KE ⊆ ΩE) (hKVΩ : KV ⊆ ΩV)
    (he : ContDiffOn ℝ ∞ e ΩE) (hi : ContDiffOn ℝ ∞ e.symm ΩV)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm))
    (hdom : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) ΩV) :
    ∃ C D J : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧ (∀ m, 1 ≤ J m) ∧
      ∀ (ε τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → ∃ c : PolynomialSolveData P ε G hG φ K τ s,
        c.U = U ∧ c.O = O ∧ c.e = e ∧ c.C = C ∧ c.D = D ∧ c.J = J := by
  have hforward := he.mono (hEK.trans hKEΩ)
  have hinverse := hi.mono (hVK.trans hKVΩ)
  have hdomain : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) e.target :=
    ⟨e.open_target,fun x hx => hdom.determinant x (hKVΩ (hVK hx)),
      fun x hx => hdom.good x (hKVΩ (hVK hx))⟩
  choose B hB hb using fun m => compact_local_weighted_bound hU isOpen_univ hKUc hUK
    (subset_univ KU) (lowJet_smooth hG).contDiffOn (m+tensorOrder P)
  have hφ' : ContDiff ℝ ∞ (fun x => fun v : Fin 2 => fderiv ℝ φ x (coordinateVector v)) := by
    apply contDiff_pi.mpr
    intro v
    exact (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose F hF hf using fun m => compact_local_weighted_bound hU isOpen_univ hKUc hUK
    (subset_univ KU) hφ'.contDiffOn (m+tensorOrder P)
  choose J hJ hj using fun m => compact_local_weighted_bound e.open_source hΩE hKE hEK hKEΩ he m
  choose I hI hi' using fun m => compact_local_weighted_bound e.open_target hdom.isOpen hKV hVK hKVΩ hi (m+1)
  choose C hC hc using fun m => (hdom.complexDomain hmap).compact_reconstruction_bounds
    e.open_target hKV hVK hKVΩ (m+1)
  have hJb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m) (x : SmallModes.Base) (hx : x ∈ e.source) :
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m := by
    simpa only [one_pow, one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  have hIb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m+1) (x : SmallModes.Base) (hx : x ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m := by
    simpa only [one_pow, one_mul] using hi' m 1 zero_le_one le_rfl j hjm x hx
  have hB' (s : ℝ≥0) (hs1 : s ≤ 1) (m : ℕ) := hb m s s.coe_nonneg hs1
  have hF' (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (m : ℕ) (v : Fin 2) :
      WeightedBound U s (m+tensorOrder P) (F m) (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (hf m s s.coe_nonneg hs1).component hU.uniqueDiffOn hs.le (zero_le_one.trans (hF m))
      hφ'.contDiffOn v
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds hU hO hQ hQO P hP K hKU e
    hforward hinverse hKe B F J I hB (fun m => zero_le_one.trans (hF m)) hJ hI hJb hIb
  refine ⟨C,D,J,(fun m => zero_le_one.trans (hC m)),hD,hJ,?_⟩
  intro ε τ s hτ hs hτs hs1 hε hε1
  refine ⟨{
    U := U
    O := O
    openU := hU
    openO := hO
    smoothP := hP
    mapsG := fun x hx => hQO (hGQ hx)
    supportU := hKU
    smoothPhase := hφ
    e := e
    smoothForward := hforward
    smoothInverse := hinverse
    supportChart := hKe
    phase := hphase
    smoothMap := hmap
    domain := hdomain.complexDomain hmap
    C := C
    D := D
    J := J
    nonnegC := fun m => zero_le_one.trans (hC m)
    nonnegD := hD
    oneLEJ := hJ
    coordinates := hJb
    coefficients := fun m => hc m s hs hs1
    polynomial := hd G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 (hB' s hs1) (hF' s hs hs1)
  },rfl,rfl,rfl,rfl,rfl,rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
