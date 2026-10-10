import OAI.Analysis.IrrationalRotation.Model.CircleCoupling
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingParameters
import OAI.Analysis.IrrationalRotation.Rotation.CircleRawTagEvent

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

def rawCurrentBlockEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  {ω | (∃ i ∈ p.block j, label i ω = some (4 : Fin 5)) ∧
    ∀ i ∈ p.block j, (ω i).2.1 < 1 - 3 / (p.m j : ℝ) ∧
      3 / (p.m j : ℝ) < (ω i).2.2}

lemma measurableSet_rawCurrentBlockEvent (p : CircleParameterData) (j : ℕ) :
    MeasurableSet (rawCurrentBlockEvent p j) := by
  classical
  unfold rawCurrentBlockEvent label
  measurability

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

private lemma coordinate_probability_for_tag (j i : ℕ) :
    IsProbabilityMeasure (coordinateLaw p j i) := by
  by_cases hi : i = 0
  · simp only [coordinateLaw, ite_eq_left hi, initialLaw]
    infer_instance
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have ht : 0 ≤ tag j (p.blockIndex i) ∧ tag j (p.blockIndex i) ≤ 1 := by
    unfold tag
    split_ifs <;> norm_num
  simpa only [coordinateLaw, ite_eq_right hi] using rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2 ht.1 ht.2

lemma coordinateLaw_currentBlock {j i : ℕ} (hi : i ∈ p.block j) :
    coordinateLaw p j i = rawLaw (kappa j) (p.m j) (p.a j) (p.b j) 1 := by
  have hi0 : i ≠ 0 := by
    have h := (p.mem_block_iff j i).mp hi
    omega
  simp only [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi,
    tag, ite_true]

theorem rawCurrentBlockEvent_mass_lower (j : ℕ) (hj : 1 ≤ j) :
    Real.exp (-90) ≤ (law p j).real (rawCurrentBlockEvent p j) := by
  classical
  let := coordinate_probability_for_tag hp j
  let μ₀ := rawLaw (kappa j) (p.m j) (p.a j) (p.b j) 1
  have : IsProbabilityMeasure μ₀ := rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds j hj).1
    (CircleParameterLaws.coupling_kappa_bounds j hj).2
    (by exact_mod_cast (show 100 ≤ p.m j by have := hp.m_ge_200 j hj; omega))
    (hp.coupling_a_bounds j hj).1 (hp.coupling_a_bounds j hj).2
    (hp.coupling_b_bounds j hj).1 (hp.coupling_b_bounds j hj).2
    (by norm_num) (by norm_num)
  let e : Fin (p.m j) ≃ (p.block j) := Fintype.equivOfCardEq (by simp [p.card_block j hj])
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (p.m j) => CoordinateSample) e.symm
  let f : Sample → Fin (p.m j) → CoordinateSample := fun ω i => ω (e i)
  have hf : Measurable f := by unfold f; fun_prop
  have hcomp : f = E ∘ (p.block j).restrict := by
    funext ω i
    simp [E, f, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hmap : (law p j).map f = Measure.pi (fun _ : Fin (p.m j) => μ₀) := by
    rw [hcomp, ← Measure.map_map E.measurable (Finset.measurable_restrict _)]
    change ((Measure.infinitePi (coordinateLaw p j)).map (p.block j).restrict).map E = _
    rw [Measure.infinitePi_map_restrict]
    have hcoord : (fun i : p.block j => coordinateLaw p j i) = fun _ => μ₀ := by
      funext i
      exact coordinateLaw_currentBlock hp i.property
    rw [hcoord]
    exact Measure.pi_map_piCongrLeft e.symm (fun _ : Fin (p.m j) => μ₀)
  let A : Set (Fin (p.m j) → CoordinateSample) :=
    {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
      ∀ i, (z i).2.1 < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < (z i).2.2}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hpre : f ⁻¹' A = rawCurrentBlockEvent p j := by
    ext ω
    constructor
    · rintro ⟨⟨i, hi⟩, hω⟩
      refine ⟨⟨e i, (e i).property, hi⟩, ?_⟩
      intro k hk
      obtain ⟨i, he⟩ := e.surjective ⟨k, hk⟩
      simpa only [f, he] using hω i
    · rintro ⟨⟨k, hk, htag⟩, hω⟩
      obtain ⟨i, he⟩ := e.surjective ⟨k, hk⟩
      refine ⟨⟨i, ?_⟩, ?_⟩
      · simpa only [f, he, label] using htag
      · intro i
        exact hω (e i) (e i).property
  have hmass : (law p j).real (rawCurrentBlockEvent p j) =
      (Measure.pi (fun _ : Fin (p.m j) => μ₀)).real A := by
    rw [← hmap]
    simp only [measureReal_def, Measure.map_apply hf hA, hpre]
  rw [hmass]
  exact concrete_circle_currentBlock_mass (p.m j) (hp.m_ge_200 j hj) (kappa j)
    (CircleParameterLaws.coupling_kappa_bounds j hj).1
    (CircleParameterLaws.coupling_kappa_bounds j hj).2
    (fun _ => p.a j) (fun _ => p.b j)
    (fun _ => (hp.coupling_a_bounds j hj).1) (fun _ => (hp.coupling_a_bounds j hj).2)
    (fun _ => (hp.coupling_b_bounds j hj).1) (fun _ => (hp.coupling_b_bounds j hj).2)

end Invariant233.CircleCoupling

end

end OAI
