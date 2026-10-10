import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.MarginalLimit
import OAI.MathematicalPhysics.PEPSFilters.HamiltonianEnergy

namespace OAI

/-! Regularized and exact maximizing filters with controlled excitation energy. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Filter Matrix
variable {L q m : ℕ}

theorem exists_regularized_maximizer_energy [NeZero q]
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (hsep : ∀ e : Edge L, ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    {b : ℝ} (hb : 0 < b) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (J : ℝ) (hH : IsGridHamiltonian J hv he)
    (Ω : State L q) (E Δ : ℝ) (hg : UniqueGround (Hamiltonian hv he) Ω E)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E Δ) :
    ∃ p : CoordinateFamily q X, IsRegularizedMaximizer hb.le Ω a p ∧
      (let φ := output (regularizedFilters hb.le a p) Ω
       let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
       |expectation ψ (Hamiltonian hv he) - E| ≤
         (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2) ∧
      (let φ := output (regularizedFilters hb.le a p) Ω
       let ψ := ((‖φ‖⁻¹ : ℝ):ℂ) • φ
       Δ * (1 - ‖inner ℂ Ω ψ‖^2) ≤
         (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2) := by
  have hΩ : Ω ≠ 0 := by intro h; simpa [h] using hg.1
  obtain ⟨p,hp,hc,hclip⟩ := exists_regularized_maximizer_clipped hb Ω hΩ hX ha
  obtain ⟨hH', heq, hvH, heH⟩ := hermitian_terms_of_grid hv he J hH
  have heigen : asMap (Hamiltonian (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e))) Ω = (E:ℂ) • Ω := by
    rw [heq]; exact hg.2.1
  have henergy := regularized_energy_bound X hX hsep hb a (fun j => (ha j).le) ha1 p Ω hΩ
    (fun v => hermitianPart (hv v)) (fun e => hermitianPart (he e))
    (fun v => (hH'.1 v).1) (fun e => (hH'.2.1 e).1) heH J
    (fun e => (hH'.2.1 e).2) E heigen hc hclip
  rw [heq] at henergy
  exact ⟨p,hp,henergy, by
    have hz := hgap (((‖output (regularizedFilters hb.le a p) Ω‖⁻¹:ℝ):ℂ) •
      output (regularizedFilters hb.le a p) Ω)
    rw [norm_normalized _ (regularized_output_ne_zero hb a p hΩ)] at hz
    norm_num only [one_pow, mul_one] at hz
    exact hz.trans ((le_abs_self _).trans henergy)⟩

theorem exists_maximizer_energy [NeZero q]
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (hsep : ∀ e : Edge L, ∀ j k, Crosses (X j) e → Crosses (X k) e → j = k)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (J : ℝ) (hH : IsGridHamiltonian J hv he)
    (Ω : State L q) (E Δ : ℝ) (hg : UniqueGround (Hamiltonian hv he) Ω E)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E Δ) :
    ∃ F : FilterFamily q m X, IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧
      (|expectation (normalizedOutput F Ω) (Hamiltonian hv he) - E| ≤
        (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2) ∧
      Δ * (1 - ‖inner ℂ Ω (normalizedOutput F Ω)‖^2) ≤
        (q:ℝ)^2 * J * ∑ j, (crossingCount (X j):ℝ) * (a j)^2 := by
  classical
  have hΩ : Ω ≠ 0 := by intro h; simpa [h] using hg.1
  let b (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  obtain ⟨p,hp⟩ := Classical.axiomOfChoice (fun n =>
    exists_regularized_maximizer_energy X hX hsep (hb n) a ha ha1 hv he J hH Ω E Δ hg hgap)
  let (j : Fin m) : CompactSpace (SpectralCoordinate (RegionConfiguration q (X j))) := by
    let := compact_unitary_coordinates (n := RegionConfiguration q (X j))
    let := compact_weight_coordinates (n := RegionConfiguration q (X j))
    infer_instance
  obtain ⟨s,ns,hns,hs⟩ := CompactSpace.tendsto_subseq p
  have hbs : Tendsto (fun n => b (ns n)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop
  have hpair : Tendsto (fun n => (b (ns n), p (ns n))) atTop (nhds (0,s)) := hbs.prodMk_nhds hs
  have hout := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0,s)).comp hpair
  have hmax : IsMaximizer Ω a (coordinateFilters a s) := by
    apply isMaximizer_of_coordinate_max Ω ha s
    intro t
    have ht := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0,t)).comp
      (hbs.prodMk_nhds tendsto_const_nhds)
    have hh := le_of_tendsto_of_tendsto ht.norm hout.norm
      (Filter.Eventually.of_forall (fun n => (hp (ns n)).1 t))
    simpa only [regularizedRawOutput_zero] using hh
  have hpos := maximizer_norm_pos hΩ ha hmax
  have hn : Tendsto (fun n => ((‖regularizedRawOutput (b (ns n)) a (p (ns n)) Ω‖⁻¹:ℝ):ℂ) •
      regularizedRawOutput (b (ns n)) a (p (ns n)) Ω) atTop
      (nhds (normalizedOutput (coordinateFilters a s) Ω)) := by
    have hi := hout.norm.inv₀ (by simpa only [regularizedRawOutput_zero] using hpos.ne')
    have hh := (Complex.continuous_ofReal.tendsto _ |>.comp hi).smul hout
    simpa only [Function.comp_def, regularizedRawOutput_zero, normalizedOutput] using hh
  refine ⟨coordinateFilters a s,hmax,hpos,?_,?_⟩
  · have hE := ((Complex.continuous_re.tendsto _ |>.comp (hn.inner (𝕜 := ℂ) ((asMap (Hamiltonian hv he)).continuous.tendsto _ |>.comp hn))).sub (tendsto_const_nhds (x := E))).abs
    exact le_of_tendsto hE (Filter.Eventually.of_forall (fun n => (hp (ns n)).2.1))
  · have hz := ((tendsto_const_nhds (x := (1:ℝ))).sub (((tendsto_const_nhds (x := Ω)).inner (𝕜 := ℂ) hn).norm.pow 2)).const_mul Δ
    exact le_of_tendsto hz (Filter.Eventually.of_forall (fun n => (hp (ns n)).2.2))

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
