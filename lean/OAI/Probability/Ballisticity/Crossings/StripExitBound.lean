import Mathlib
import OAI.Probability.Ballisticity.Crossings.CrossingGap
import OAI.Probability.Ballisticity.Crossings.FiniteBoxExit

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def StripUntil {d : ℕ} (e : Direction d) (H T : ℕ) : Set (Path d) :=
  ConfinedUntil 0 {y | 0 ≤ signedHeight e y ∧ signedHeight e y < (H:ℤ)} T

lemma measurableSet_stripUntil {d : ℕ} (e : Direction d) (H T : ℕ) :
    MeasurableSet (StripUntil e H T) := measurableSet_confinedUntil _ _ _

lemma stripUntil_confined {d : ℕ} (e : Direction d) (H T : ℕ) (R : ℝ) (M : ℕ)
    (hM : R ≤ M) : StripUntil e H T \ StripExcursion (realPosition (step e)) H R ⊆
      ConfinedUntil 0 {y | y∈latticeBox M ∧ 0 ≤ signedHeight e y ∧ signedHeight e y < (H:ℤ)} T := by
  intro X hX
  refine ⟨hX.1.1,fun j hj => ⟨?_,hX.1.2 j hj⟩⟩
  rw [mem_latticeBox]
  have hbound (u : Direction d) : signedCoordinate u (X j) ≤ R := by
    by_contra hh
    apply hX.2
    refine ⟨j,?_,u,lt_of_not_ge hh⟩
    intro i hi
    have hz := hX.1.2 i (hi.trans hj)
    rw [signedHeight_projection]
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2.le
  intro i
  have hp := (hbound (i,true)).trans hM
  have hn := (hbound (i,false)).trans hM
  simp only [signedCoordinate,Bool.false_eq_true,ite_true,ite_false] at hp hn
  constructor
  · have hh : -(M:ℝ) ≤ (X j i:ℝ) := by linarith
    exact_mod_cast hh
  · exact_mod_cast hp

lemma annealed_bound_bad_real {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : Set (Path d)) (hA : MeasurableSet A) (E : Set (Environment d)) (hE : MeasurableSet E)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ᵐ ω ∂environmentLaw ν, ω∉E → (quenchedKernel (ω,0)).real A ≤ c) :
    (annealedLaw ν).real A ≤ (environmentLaw ν).real E+c := by
  have hh := annealed_bound_bad_environment ν A hA E hE (ENNReal.ofReal c) (by
    filter_upwards [hc] with ω hω hE
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc0).mpr (hω hE))
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,ENNReal.ofReal_ne_top⟩) hh
  simpa only [measureReal_def,ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hc0] using hr

lemma annealed_stripUntil_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (H T K M : ℕ) (hH : 0 < H) (R : ℝ) (hM : R ≤ M)
    (hT : (latticeBox (d := d) M).card*K ≤ T)
    (κ : ℝ≥0) (hκ1 : κ ≤ 1)
    (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ y f, κ ≤ (ω y).1 f) :
    (annealedLaw ν).real (StripUntil e H T) ≤
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) H R)+
      (latticeBox (d := d) M).card*(environmentLaw ν).real (badCrossingEvent e H (1/2))+
      (latticeBox (d := d) M).card*(1-(κ:ℝ)*(H:ℝ)^(-(1/2:ℝ)))^K := by
  let B := latticeBox (d := d) M
  let E := badBoxEvent e H (1/2) (B.image (fun y => y+step e))
  let A := StripUntil e H T \ StripExcursion (realPosition (step e)) H R
  let a := (H:ℝ)^(-(1/2:ℝ))
  have ha0 : 0 ≤ a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hH) (by norm_num)
  have hd : (κ:ℝ)*a ≤ 1 :=
    (mul_le_of_le_one_left ha0 (by exact_mod_cast hκ1)).trans ha1
  have hh := annealed_bound_bad_real ν A ((measurableSet_stripUntil _ _ _).diff (measurableSet_stripExcursion _ _ _))
    E (measurableSet_badBoxEvent _ _ _ _) (B.card*(1-(κ:ℝ)*a)^K) (by positivity) (by
      filter_upwards [hκ] with ω hω hE
      apply (measureReal_mono (stripUntil_confined e H T R M hM) (measure_ne_top _ _)).trans
        (quenched_stripBox_exit_bound ω e H B T K hT κ hω a ha0 hd ?_)
      intro y hy
      by_contra hh
      exact hE (Set.mem_iUnion.mpr ⟨y+step e,Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩,lt_of_not_ge hh⟩⟩))
  have hb := badBox_bound ν e H (1/2) (B.image (fun y => y+step e))
  have hb' : (environmentLaw ν).real E ≤ B.card*(environmentLaw ν).real (badCrossingEvent e H (1/2)) :=
    hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) measureReal_nonneg)
  have hscover : StripUntil e H T ⊆ StripExcursion (realPosition (step e)) H R ∪ A := by
    intro X hX
    by_cases hh : X ∈ StripExcursion (realPosition (step e)) H R
    · exact Or.inl hh
    · exact Or.inr ⟨hX,hh⟩
  have hs : (annealedLaw ν).real (StripUntil e H T) ≤
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) H R)+(annealedLaw ν).real A :=
    (measureReal_mono hscover (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  change _ ≤ _+B.card*(_)+B.card*(1-(κ:ℝ)*a)^K
  linarith

end DirectionalTransience

end

end OAI
