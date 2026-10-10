import OAI.Analysis.LipschitzHilbert.Trees.SourceCrudeMassBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceUniformDamping
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftNormalization

namespace OAI

/-! Uniformly in the finite phase count, the good-set small-imaginary
vertex estimate suffices for the actual source
family. The linear node envelope proves integrability and the large
imaginary bound, Gaussian damping covers the remaining vertex tube,
and the established analytic interpolation supplies the diagonal. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem eventually_source_diagonal_finite_phases_ae
    (q b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (nphases : ℕ), 0 < nphases →
    ∀ (μ : Measure X) [IsFiniteMeasure μ]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t, Measurable (weight t)) →
    ∀ (K : ℕ), 0 < K → ∀ (gap : ℕ → ℝ)
      (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (phaseIndex : ℕ → (Fin nphases)) (a : ℝ) (level : ℕ) (cell : ℤ)
      (n : X → ℝ) (U S alpha mu : ℝ),
      Measurable n → Integrable n μ → (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) →
      0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ mu → mu ≤ 1 →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
    let p := Real.sqrt L
    let F := g.sourceShiftFamily tops slope precision cutoff weight K gap
      packets assigned stop value phaseIndex a level cell
    (∀ i : (Fin nphases), ∀ eta, ∀ᵐ x ∂μ, ‖F (phaseTubePoint (Pi.single i mu) eta) x‖ ≤
      L^q*(1+Real.sqrt (∑ j, (eta j)^2))*n x) →
    (∀ i : (Fin nphases), ∀ eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        L^(q+1)*S^(1/p)) →
    let central := F (phaseTubePoint (fun _ => mu/(Fintype.card (Fin nphases):ℝ)) (fun _ => 0))
    Integrable (fun x => ‖(n x^(alpha/p-1)) • central x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • central x‖^p ∂μ)^(1/p) ≤ L^(q+2)*S^(1/p) := by
  filter_upwards [eventually_source_crude_mass_budget (X := X) (κ := κ) q b hb,
    eventually_source_damped_vertex_root_finite (X := X) (κ := κ) 6 (by norm_num),
    eventually_ge_atTop (max 1 (Real.exp 1))] with L hcrude hdamp hLbig
  intro nphases hnphases μ _ g tops slope precision cutoff weight hp hw hwmeas K hK gap packets assigned stop
    value hv hassigned heligible phaseIndex a level cell n U S alpha mu hn hnint hnpos hnU
    hU hS ha ha3 hmu hmu1 hlog hmass p F hnode hsmall central
  let : Nonempty (Fin nphases) := ⟨⟨0,hnphases⟩⟩
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp0 : 0 < p := Real.sqrt_pos.mpr hL0
  have hP : 0 ≤ L^(q+1)*S^(1/p) := by positivity
  have hraw (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      Integrable (fun x => ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x‖^p ∂μ)^(1/p) ≤
        (L^(q+1)*S^(1/p))*(1+Real.sqrt (∑ j, (eta j)^2))*Real.exp (6*Real.sqrt L) := by
    apply hcrude μ n (F (phaseTubePoint (Pi.single i mu) eta)) U S alpha
      (Real.sqrt (∑ j, (eta j)^2)) hnpos hnU hn hnint
    · exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas
        K gap packets assigned stop value hv _ a level cell
    · exact hU
    · exact hS
    · exact ha
    · exact ha3
    · exact Real.sqrt_nonneg _
    · exact hlog
    · exact hmass
    · exact hnode i eta
  have hvertices (i : (Fin nphases)) (eta : (Fin nphases) → ℝ) :
      (∫ x, ‖gaussianPhaseDamping (phaseTubePoint (Pi.single i mu) eta) •
        ((n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)‖^p ∂μ)^(1/p) ≤
          L^(q+2)*S^(1/p) := by
    have hsimplex := sourceShiftSimplex_vertex (ι := Fin nphases) hmu i
    have hd := hdamp nphases μ (fun x => (n x^(alpha/p-1)) • F (phaseTubePoint (Pi.single i mu) eta) x)
      (Pi.single i mu) eta mu (L^(q+1)*S^(1/p)) p
      hsimplex.1 hsimplex.2 hmu hmu1 hP hp0 (hraw i eta).2 (hsmall i eta)
    apply hd.trans
    calc
      Real.exp 1*(L^(q+1)*S^(1/p)) ≤ L*(L^(q+1)*S^(1/p)) :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hLbig) hP
      _ = L^(q+2)*S^(1/p) := by
        have he : L*L^(q+1) = L^(q+2) := by
          calc
            L*L^(q+1) = L^(1:ℝ)*L^(q+1) := by rw [Real.rpow_one]
            _ = L^(q+2) := by rw [← Real.rpow_add hL0]; congr 1; ring
        rw [← mul_assoc,he]
  exact g.sourceShiftFamily_normalized_diagonal_lp μ tops slope precision cutoff weight hp hw hwmeas
    hK gap packets assigned stop value hv hassigned heligible phaseIndex a level cell
    n hn (alpha/p-1) p (L^(q+2)*S^(1/p)) mu
    (by
      have hexp : 1 < Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      have hLgt : 1 < L := hexp.trans_le ((le_max_right _ _).trans hLbig)
      exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by simpa using hLgt))
    (by positivity) hmu
    (fun i eta => source_lp_power_smul_integrable μ _ _ p (hraw i eta).1) hvertices

end LipschitzHilbert.AngularGrid

end

end OAI
