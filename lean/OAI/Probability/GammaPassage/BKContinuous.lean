import OAI.Probability.GammaPassage.BKLimit

namespace OAI

namespace GammaFPP.BK
open MeasureTheory ProbabilityTheory Set Finset Filter PlanarFPP
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

lemma bitFamily_subset (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) : bitFamily D S t F ⊆ (S.product (Finset.univ : Finset (Fin t))).powerset := by
  intro x hx
  exact Finset.mem_powerset.mpr ((mem_bitFamily ..).mp hx).1

lemma bitDisjointFamily_subset (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    bitDisjointFamily D S t Fs ⊆ (S.product (Finset.univ : Finset (Fin t))).powerset := by
  classical
  exact Finset.filter_subset _ _

lemma single_mass_le (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitFamily (gammaSurvivalQuantile hs hr) S t F) ≤
      P.real {ω | StrictPathEvent S F (fun e => τ e ω)} := by
  let _ := h.probability
  have hmass : P.real (⋃ x ∈ bitFamily (gammaSurvivalQuantile hs hr) S t F,
      gammaDyadicRankCell shape rate τ S t x) =
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitFamily (gammaSurvivalQuantile hs hr) S t F) := by
    simpa only [Finset.product_eq_sprod] using
      h.gammaDyadicRankCells_real hs hr S t
        (bitFamily (gammaSurvivalQuantile hs hr) S t F)
        (bitFamily_subset (gammaSurvivalQuantile hs hr) S t F)
  rw [← hmass]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_positive] with ω hpos
  intro hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_,p,hp,he,hgood⟩ := (mem_bitFamily ..).mp hx
  exact ⟨p,hp,he,rounded_original hs hr (fun e => (hpos e).le)
    ((cell_path_iff hs hr hcell p he).mpr hgood)⟩

lemma rounded_disjoint_mass_le (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} ≤
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t))) (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) := by
  classical
  let _ := h.probability
  have hmass : P.real (⋃ x ∈ bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs,
      gammaDyadicRankCell shape rate τ S t x) =
      fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
        (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs) := by
    simpa only [Finset.product_eq_sprod] using
      h.gammaDyadicRankCells_real hs hr S t
        (bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs)
        (bitDisjointFamily_subset (gammaSurvivalQuantile hs hr) S t Fs)
  rw [← hmass]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_gammaDyadicRankCell hs hr S t] with ω hω
  intro hd
  obtain ⟨x,hx,hcell⟩ := hω
  obtain ⟨ps,hps,hdis⟩ := hd
  have hmem : x ∈ bitDisjointFamily (gammaSurvivalQuantile hs hr) S t Fs := by
    apply Finset.mem_filter.mpr
    refine ⟨hx,ps,?_,hdis⟩
    exact hps.imp (fun p _ hp =>
      ⟨hp.1,hp.2.1,(cell_path_iff hs hr hcell p hp.2.1).mp hp.2.2⟩)
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hmem,hcell⟩⟩

lemma probabilities_nonneg (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    0 ≤ (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => exact mul_nonneg measureReal_nonneg ih

lemma factors_le (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    (Fs.map (fun F => fairFamilyMass (S.product (Finset.univ : Finset (Fin t)))
      (bitFamily (gammaSurvivalQuantile hs hr) S t F))).prod ≤
    (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (mul_le_mul_of_nonneg_left ih (fairFamilyMass_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (single_mass_le h hs hr S t F)
        (probabilities_nonneg (P := P) (τ := τ) S Fs))

theorem gamma_rounded_strict_path_BK (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod :=
  (rounded_disjoint_mass_le h hs hr S t Fs).trans
    ((gamma_decoder_finite_path_BK hs hr S t Fs).trans (factors_le h hs hr S t Fs))

/-- Finite-path repeated BK in the actual Gamma environment, for every
positive real shape and rate. Fs may repeat and regions may overlap; only the
chosen paths' undirected edge sets must be pairwise disjoint. -/
theorem gamma_strict_path_BK (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge)
    (Fs : List (Set StrictPathWitness)) :
    P.real {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  let _ := h.probability
  let C : ℝ := (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod
  have hC : 0 ≤ C := probabilities_nonneg (P := P) (τ := τ) S Fs
  have hh := ae_eventual_measure_le P
    {ω | StrictDisjointPaths S Fs (fun e => τ e ω)}
    (fun t => {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)})
    (ENNReal.ofReal C) (by
      filter_upwards [h.ae_positive] with ω hpos
      intro hω
      exact disjoint_eventually_rounded hs hr (fun e => (hpos e).le) hω) (fun t => by
        calc
          P {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)} =
              ENNReal.ofReal (P.real {ω | RoundedDisjoint hs hr S Fs t (fun e => τ e ω)}) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal
            (gamma_rounded_strict_path_BK h hs hr S t Fs))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hC)
end GammaFPP.BK

end OAI
