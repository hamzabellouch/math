import OAI.Probability.FirstPassage.BKBitLaw
import OAI.Probability.FirstPassage.BKLimit

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

def StrictPathEvent (S : Finset Edge) (F : Set StrictPathWitness) (w : Edge → ℝ) : Prop :=
  ∃ p ∈ F, p.edges ⊆ S ∧ p.Good w

lemma dyadicPathFamily_subset (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    dyadicPathFamily S t F ⊆ (S ×ˢ Finset.univ).powerset := by
  intro x hx
  exact mem_powerset.mpr ((mem_dyadicPathFamily ..).mp hx).1

lemma dyadicDisjointPathFamily_subset (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    dyadicDisjointPathFamily S t Fs ⊆ (S ×ˢ Finset.univ).powerset := by
  classical
  exact Finset.filter_subset _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

omit [MeasurableSpace Ω] in
lemma dyadic_single_cell_original {S : Finset Edge} {t : ℕ} {F : Set StrictPathWitness}
    {x : Finset (Edge × Fin t)} {ω : Ω}
    (hx : x ∈ dyadicPathFamily S t F) (hcell : ω ∈ dyadicRankCell τ S t x) :
    StrictPathEvent S F (fun e => τ e ω) := by
  obtain ⟨_,p,hp,he,hgood⟩ := (mem_dyadicPathFamily ..).mp hx
  exact ⟨p,hp,he,((dyadicRankCell_path_iff hcell p he).mpr hgood).original⟩

lemma ExponentialEnvironment.dyadic_single_mass_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    fairFamilyMass (S ×ˢ Finset.univ) (dyadicPathFamily S t F) ≤
      P.real {ω | StrictPathEvent S F (fun e => τ e ω)} := by
  let _ := h.probability
  rw [← h.dyadicRankCells_real S t _ (dyadicPathFamily_subset S t F)]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  exact dyadic_single_cell_original hx hcell

omit [MeasurableSpace Ω] in
lemma rounded_disjoint_cell_mem {S : Finset Edge} {t : ℕ} {Fs : List (Set StrictPathWitness)}
    {x : Finset (Edge × Fin t)} {ω : Ω} (hx : x ⊆ S ×ˢ Finset.univ)
    (hcell : ω ∈ dyadicRankCell τ S t x)
    (hd : RoundedDisjointPaths S Fs t (fun e => τ e ω)) :
    x ∈ dyadicDisjointPathFamily S t Fs := by
  classical
  obtain ⟨ps,hps,hdis⟩ := hd
  apply Finset.mem_filter.mpr
  refine ⟨mem_powerset.mpr hx,ps,?_,hdis⟩
  exact hps.imp (fun p _ hp => ⟨hp.1,hp.2.1,(dyadicRankCell_path_iff hcell p hp.2.1).mp hp.2.2⟩)

lemma ExponentialEnvironment.rounded_disjoint_mass_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤
      fairFamilyMass (S ×ˢ Finset.univ) (dyadicDisjointPathFamily S t Fs) := by
  let _ := h.probability
  rw [← h.dyadicRankCells_real S t _ (dyadicDisjointPathFamily_subset S t Fs)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_dyadicRankCell S t] with ω hω
  intro hd
  obtain ⟨x,hx,hcell⟩ := hω
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr
    ⟨rounded_disjoint_cell_mem (mem_powerset.mp hx) hcell hd,hcell⟩⟩

lemma strict_path_probabilities_nonneg (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    0 ≤ (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => exact mul_nonneg measureReal_nonneg ih

lemma ExponentialEnvironment.dyadic_factors_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    (Fs.map (fun F => fairFamilyMass (S ×ˢ Finset.univ) (dyadicPathFamily S t F))).prod ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (mul_le_mul_of_nonneg_left ih (fairFamilyMass_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (h.dyadic_single_mass_le S t F)
        (strict_path_probabilities_nonneg P τ S Fs))

theorem ExponentialEnvironment.rounded_strict_path_BK (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod :=
  (h.rounded_disjoint_mass_le S t Fs).trans
    ((dyadic_strict_path_BK S t Fs).trans (h.dyadic_factors_le S t Fs))

theorem exponential_strict_path_BK (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  let _ := h.probability
  let C : ℝ := (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod
  have hC : 0 ≤ C := strict_path_probabilities_nonneg P τ S Fs
  have hh := strict_disjoint_measure_le_of_rounded P τ S Fs (ENNReal.ofReal C) (fun t => by
    calc
      P {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} =
          ENNReal.ofReal (P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (h.rounded_strict_path_BK S t Fs))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hC)

end PlanarFPP

end OAI
