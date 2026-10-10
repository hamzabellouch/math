import Mathlib
import OAI.Probability.Ballisticity.Estimates.UniformLowerMass

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma product_small_mass_probability {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (μ : Measure Ω) (π : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (k : ℕ) (F : Ω → I → Fin k → ℝ)
    (hF : ∀ j, Measurable (fun p : Ω × I => F p.1 p.2 j))
    (hF0 : ∀ ω x j, 0 ≤ F ω x j) (hF1 : ∀ ω x j, F ω x j ≤ 1)
    {c α : ℝ} (hc : 0 < c)
    (hbad : ∀ x j, μ.real {ω | F ω x j < c} ≤ α) :
    μ.real {ω | (∫ x, ∏ j, F ω x j ∂π) < c^k/2} ≤ 2*k*α := by
  have hb (x : I) : μ.real {ω | (∏ j, F ω x j) < 2*(c^k/2)} ≤ k*α := by
    have hs : {ω | (∏ j, F ω x j) < 2*(c^k/2)} ⊆ ⋃ j, {ω | F ω x j < c} := by
      intro ω hω
      change (∏ j, F ω x j) < 2*(c^k/2) at hω
      by_contra hn
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_lt] at hn
      have hh := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin k => c)
        (g := fun j => F ω x j) (fun _ _ => hc.le) (fun j _ => hn j)
      simpa using (show c^k ≤ ∏ j, F ω x j by simpa using hh).not_gt (by linarith)
    have hh := (measureReal_mono (μ := μ) hs).trans (measureReal_iUnion_fintype_le _)
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbad x j)
    simpa using hh.trans hh'
  have hh := mixture_small_mass_probability μ π (fun ω x => ∏ j, F ω x j)
    (Finset.measurable_prod _ fun j _ => hF j)
    (fun ω x => Finset.prod_nonneg fun j _ => hF0 ω x j)
    (fun ω x => Finset.prod_le_one₀ (fun j _ => hF0 ω x j) (fun j _ => hF1 ω x j))
    (show 0 < c^k/2 by positivity) hb
  simpa only [mul_assoc] using hh

noncomputable def tupleTubeMass {d k : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, ∏ j, (quenchedKernel (ω,x j)).real (TubePrefix ℓ f (x j) θ z H) ∂π

lemma measurable_tupleTube_integrand {d k : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (j : Fin k) :
    Measurable (fun p : Environment d × (Fin k → Lattice d) =>
      (quenchedKernel (p.1,p.2 j)).real (TubePrefix ℓ f (p.2 j) θ z H)) := by
  apply Measurable.ennreal_toReal
  apply measurable_from_prod_countable_left
  intro x
  exact (Kernel.measurable_coe _ (measurableSet_tubePrefix ℓ f (x j) θ z H)).comp
    (measurable_id.prodMk measurable_const)

theorem initial_tuple_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      ∀ (H : ℕ) (π : Measure (Fin k → Lattice d)), IsProbabilityMeasure π →
      (H:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | tupleTubeMass (realPosition (step e)) f θ (η*r) H π ω < c} < ε := by
  let α := ε/(4*((k:ℝ)+1))
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨c,hc,hc1,R,hR,hh⟩ := clipping_uniform ν hue e f hef htrans hT hη hα
  have hcfin : c ≠ ∞ := ne_top_of_le_ne_top (by simp) hc1
  have hcr : 0 < c.toReal := ENNReal.toReal_pos (ne_of_gt hc) hcfin
  refine ⟨c.toReal^k/2,by positivity,R,hR,fun r hr => ?_⟩
  obtain ⟨θ,hθ⟩ := hh r hr
  refine ⟨θ,fun H π hπ hH => ?_⟩
  let := hπ
  have hb (x : Fin k → Lattice d) (j : Fin k) :
      (environmentLaw ν).real {ω | (quenchedKernel (ω,x j)).real
        (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c.toReal} ≤ α := by
    have he : {ω | (quenchedKernel (ω,x j)).real
        (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c.toReal} =
      {ω | quenchedKernel (ω,x j) (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H) < c} := by
      ext ω
      exact ENNReal.toReal_lt_toReal (measure_ne_top _ _) hcfin
    rw [he]
    exact (hθ (x j) H hH).le
  have he := product_small_mass_probability (environmentLaw ν) π k
    (fun ω x j => (quenchedKernel (ω,x j)).real (TubePrefix (realPosition (step e)) f (x j) θ (η*r) H))
    (measurable_tupleTube_integrand _ _ _ _ _)
    (fun _ _ _ => ENNReal.toReal_nonneg) (fun _ _ _ => by exact ENNReal.toReal_mono (by simp) (show _ ≤ (1:ℝ≥0∞) from prob_le_one)) hcr hb
  change (environmentLaw ν).real {ω | tupleTubeMass _ _ θ (η*r) H π ω < c.toReal^k/2} ≤ 2*k*α at he
  apply lt_of_le_of_lt he
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  dsimp [α]
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity)]
  nlinarith
end DirectionalTransience

end

end

end OAI
