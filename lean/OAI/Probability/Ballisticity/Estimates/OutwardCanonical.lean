import Mathlib
import OAI.Probability.Ballisticity.Walk.OutwardCanonicalRows

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem actual_outward_canonical_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A c B : ℝ, 0 < A ∧ 0 < c ∧ 0 < B ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      let Z := outwardCanonicalExcess e f A x
      (∀ ω, 0 ≤ Z ω) ∧
      @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _ Z ∧
      Integrable (fun ω => Real.exp (c*Z ω)) (environmentLaw ν) ∧
      (∫ ω, Real.exp (c*Z ω) ∂environmentLaw ν) ≤ B ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
        0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤ 2*A*Real.log ((t:ℝ)+2)+Z ω) := by
  obtain ⟨A,D,B,hA,hD,hB,hdata⟩ := actual_outward_log_bound ν hue e f hef htrans
  refine ⟨A,D⁻¹,Real.exp 1*B,hA,inv_pos.mpr hD,mul_pos (Real.exp_pos _) hB,?_⟩
  intro a x hx
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  let Z := outwardCanonicalExcess e f A x
  have hZm : Measurable Z := measurable_outwardCanonicalExcess e f A x
  have hZbound : ∀ᵐ ω ∂environmentLaw ν, Z ω ≤ D*(W ω+1) ∧
      ∀ n, -Real.log (outwardKernelMass e f (n+1) x ω) ≤ 2*A*Real.log ((n:ℝ)+2)+Z ω := by
    filter_upwards [hbound] with ω hω
    exact canonicalLogExcess_bounds hA.le hD.le (hW0 ω) _ ω (fun n => (hω n).2)
  have hdom : Integrable (fun ω => Real.exp 1*Real.exp (W ω)) (environmentLaw ν) := hWi.const_mul _
  have hexp : ∀ᵐ ω ∂environmentLaw ν, Real.exp (D⁻¹*Z ω) ≤ Real.exp 1*Real.exp (W ω) := by
    filter_upwards [hZbound] with ω hω
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hω.1 (inv_nonneg.mpr hD.le)
    rw [←mul_assoc,inv_mul_cancel₀ hD.ne',one_mul] at hh
    linarith
  have hZi : Integrable (fun ω => Real.exp (D⁻¹*Z ω)) (environmentLaw ν) :=
    hdom.mono_nonneg (hZm.const_mul _ |>.exp |>.aestronglyMeasurable)
      (Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hexp
  refine ⟨fun ω => canonicalLogExcess_nonneg _ _ ω,outwardCanonicalExcess_upper_rows e f A a x hx,hZi,?_,?_⟩
  · calc
      _ ≤ ∫ ω, Real.exp 1*Real.exp (W ω) ∂environmentLaw ν := integral_mono_ae hZi hdom hexp
      _ = Real.exp 1*(∫ ω, Real.exp (W ω) ∂environmentLaw ν) := integral_const_mul _ _
      _ ≤ Real.exp 1*B := mul_le_mul_of_nonneg_left hWB (Real.exp_pos _).le
  · filter_upwards [hbound,hZbound] with ω hω hZω
    exact fun n => ⟨(hω n).1,hZω.2 n⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def truncatedEndpointLaw {d : ℕ} (e : Direction d) (H N : ℕ)
    (ω : Environment d) (x : Lattice d) : Measure (Lattice d) :=
  ((quenchedKernel (ω,x)).restrict (HitThrough (Strip (realPosition (step e)) x H)
    (Upper (realPosition (step e)) x H) N)).map (prefixEndpoint (realPosition (step e)) x H)

instance truncatedEndpointLaw_finite {d : ℕ} (e : Direction d) (H N : ℕ)
    (ω : Environment d) (x : Lattice d) : IsFiniteMeasure (truncatedEndpointLaw e H N ω x) := by
  unfold truncatedEndpointLaw
  infer_instance

lemma truncatedEndpointLaw_le {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω : Environment d) (x : Lattice d) :
    truncatedEndpointLaw e H N ω x ≤
      hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) := by
  rw [hitKernel_eq_map_prefixEndpoint e x hH]
  exact Measure.map_mono (Measure.restrict_mono (hitThrough_subset_hit _ _ _) le_rfl)
    (measurable_prefixEndpoint _ _ _)

lemma truncatedEndpointLaw_apply {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω : Environment d) (x : Lattice d) (A : Set (Lattice d)) :
    truncatedEndpointLaw e H N ω x A = quenchedKernel (ω,x)
      (HitThrough (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H ∩ A) N) := by
  rw [truncatedEndpointLaw,Measure.map_apply (measurable_prefixEndpoint _ _ _) (Set.to_countable _).measurableSet,
    Measure.restrict_apply ((measurable_prefixEndpoint _ _ _) (Set.to_countable _).measurableSet)]
  apply measure_congr
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  constructor
  · rintro ⟨hA,hhit⟩
    obtain ⟨n,hn,hdet⟩ := Set.mem_iUnion₂.mp hhit
    change prefixEndpoint (realPosition (step e)) x H X ∈ A at hA
    dsimp [prefixEndpoint] at hA
    rw [coordinate_hitAt_record e x X h0 hnn hH hdet] at hA
    exact Set.mem_iUnion₂.mpr ⟨n,hn,⟨hdet.1,by simpa only [add_sub_cancel] using hA⟩,hdet.2⟩
  · intro hhit
    obtain ⟨n,hn,hdet⟩ := Set.mem_iUnion₂.mp hhit
    have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n := ⟨hdet.1.1,hdet.2⟩
    refine ⟨?_,Set.mem_iUnion₂.mpr ⟨n,hn,hh⟩⟩
    change prefixEndpoint (realPosition (step e)) x H X ∈ A
    dsimp [prefixEndpoint]
    rw [coordinate_hitAt_record e x X h0 hnn hH hh]
    simpa only [add_sub_cancel] using hdet.1.2

lemma truncatedEndpointLaw_locality {d : ℕ} (e : Direction d) {H : ℕ} (hH : 0 < H)
    (N : ℕ) (ω η : Environment d) (x : Lattice d)
    (he : Set.EqOn ω η (LatticeBall x N)) :
    truncatedEndpointLaw e H N ω x = truncatedEndpointLaw e H N η x := by
  apply Measure.ext
  intro A hA
  rw [truncatedEndpointLaw_apply e hH,truncatedEndpointLaw_apply e hH]
  exact quenched_hitThrough_locality ω η x _ _ N he
end DirectionalTransience

end

end

end OAI
