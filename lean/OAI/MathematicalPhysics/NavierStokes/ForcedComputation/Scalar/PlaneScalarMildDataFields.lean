import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildData

namespace OAI

/-! Actual periodic or compactly supported smooth fields supply all compatible jet data. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows
open scoped Topology ContDiff BoundedContinuousFunction

private theorem exists_data_of_representatives {T : ℝ}
    (w₀ : Plane → ℝ) (h : ℝ × Plane → ℝ) (b : Fin 3 → ℝ × Plane → ℝ)
    (hJ : ∀ k, ∃ J : Jet k, ∀ x, BoundedSpatialJets.function Plane ℝ k J x = w₀ x)
    (hg : ∀ k, ∃ g : C(Icc (0 : ℝ) T, Jet k),
      ∀ t x, BoundedSpatialJets.function Plane ℝ k (g t) x = h (t.val,x))
    (hc : ∀ k i, ∃ c : C(Icc (0 : ℝ) T, Jet k),
      ∀ t x, BoundedSpatialJets.function Plane ℝ k (c t) x = b i (t.val,x)) :
    ∃ D : CompatibleData T,
      (∀ k x, BoundedSpatialJets.function Plane ℝ k (D.initial k) x = w₀ x) ∧
      (∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x)) ∧
      (∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x)) := by
  choose J hJ using hJ
  choose g hg using hg
  choose c hc using hc
  let u (k : ℕ) : WeaklySingular.Path (Jet k) T := (WeaklySingular.pathEquiv (Jet k) T).symm (g k)
  have hu : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (u k t) x = h (t.val,x) := hg
  refine ⟨CompatibleData.ofRepresentatives w₀ (fun t x => h (t.val,x))
    (fun i t x => b i (t.val,x)) J u c hJ hu hc, hJ, hu, hc⟩

/-- Smooth periodic initial data, source, and coefficients determine compatible finite jets. -/
theorem exists_periodic_data {T : ℝ} (hT : 0 ≤ T)
    {w₀ : Plane → ℝ} (hw : ContDiff ℝ ∞ w₀) (hpw : PlanePeriodic w₀)
    {h : ℝ × Plane → ℝ} (hh : ContDiff ℝ ∞ h)
    (hph : ∀ t, PlanePeriodic (fun x => h (t,x)))
    {b : Fin 3 → ℝ × Plane → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hpb : ∀ i t, PlanePeriodic (fun x => b i (t,x))) :
    ∃ D : CompatibleData T,
      (∀ k x, BoundedSpatialJets.function Plane ℝ k (D.initial k) x = w₀ x) ∧
      (∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x)) ∧
      (∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x)) := by
  apply exists_data_of_representatives w₀ h b
  · intro k
    obtain ⟨J, hJ⟩ := exists_periodic_jet_curve (hw.comp contDiff_snd)
      (fun _ => hpw) k T
    let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
    exact ⟨J t₀, hJ t₀⟩
  · intro k
    exact exists_periodic_jet_curve hh hph k T
  · intro k i
    exact exists_periodic_jet_curve (hb i) (hpb i) k T

/-- Common compact spatial support gives the whole-plane data, with zero initial value. -/
theorem exists_supported_zero_data {T : ℝ} {K : Set Plane} (hK : IsCompact K)
    {h : ℝ × Plane → ℝ} (hh : ContDiff ℝ ∞ h)
    (hsh : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, h (t,x) = 0)
    {b : Fin 3 → ℝ × Plane → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hsb : ∀ i t, t ∈ Icc (0 : ℝ) T → ∀ x ∉ K, b i (t,x) = 0) :
    ∃ D : CompatibleData T,
      (∀ k x, BoundedSpatialJets.function Plane ℝ k (D.initial k) x = 0) ∧
      (∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x)) ∧
      (∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x)) := by
  apply exists_data_of_representatives (fun _ => 0) h b
  · intro k
    refine ⟨0, fun x => ?_⟩
    exact ((BoundedContinuousFunction.evalCLM ℝ x).comp
      (BoundedSpatialJets.functionMap Plane ℝ k)).map_zero
  · intro k
    exact exists_supported_jet_curve hh hK T hsh k
  · intro k i
    exact exists_supported_jet_curve (hb i) hK T (hsb i) k

end ForcedComputation.PlaneScalarMild

end

end OAI
