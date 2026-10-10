import OAI.Geometry.NodalSets.Coefficients.FiniteResidualBound
import OAI.Geometry.NodalSets.Coefficients.LocalResidualRegularity
import OAI.Geometry.NodalSets.Waves.LatticeFieldBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
  {D U : Set Coord} {m J K k0 : ℕ}

theorem LocalCompactWaveData.lattice_residual_derivative_bound
    (a : LocalCompactWaveData g w S D m J K k0)
    (hw : ∀ x ∈ a.E, w x ≠ 0) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
        let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
        ContDiff ℝ ∞ residual ∧ ∀ x : Coord,
          DerivativeBound k0 residual x (C*(n:ℝ)^(3-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hUb
  have hCr := a.beams.Cr_pos
  refine ⟨C*a.beams.Cr,mul_pos hC a.beams.Cr_pos,?_⟩
  filter_upwards [a.estimates,a.wave_residual_regular hw,eventually_gt_atTop (0:ℕ)]
    with n hn hreg hnpos
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  let lam : ℝ := 4*(n:ℝ)^2+6*(n:ℝ)
  have hlam : (lam:ℂ) = (4:ℂ)*(n:ℂ)^2+6*(n:ℂ) := by dsimp [lam]; push_cast; rfl
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  have hf (i : SourceGrid U n × Fin 3) (j : Fin 4) :
      ContDiff ℝ ∞ (sourceFlux g w (V i) j) :=
    (hreg (latticeFrame a.cover hUD n i.1,i.2)).1 j
  have hr (i : SourceGrid U n × Fin 3) :
      ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (V i) x+(lam:ℂ)*V i x) := by
    rw [hlam]
    exact (hreg (latticeFrame a.cover hUD n i.1,i.2)).2
  intro coeff hc
  change ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w
      (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x+_*(gaussianWaveField V coeff x:ℂ)) ∧ _
  constructor
  · rw [← hlam,gaussianWaveField_source_residual g w V hV hf coeff lam]
    exact Complex.ofRealCLM.contDiff.comp (gaussianWaveField_contDiff _ coeff hr)
  · intro x k hk
    have hb (i : SourceGrid U n × Fin 3) :
        ‖iteratedFDeriv ℝ k (fun x ↦ sourceWeightedOperator g w (V i) x+(lam:ℂ)*V i x) x‖ ≤
          a.beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x) := by
      rw [hlam]
      exact ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).2 k hk
    have hh := gaussianWaveField_source_residual_bound g w V hV hf lam hr coeff
      hnR.le hc k x hb
    rw [hlam] at hh
    refine hh.trans ?_
    have hcardR : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
      simpa only [Nat.card_eq_fintype_card] using hcard n hnpos
    calc
      _ ≤ (C*(n:ℝ)^2)*(n:ℝ)*(a.beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
        gcongr
      _ = (C*a.beams.Cr)*((n:ℝ)^3*(n:ℝ)^(-(K:ℝ)))*Real.exp ((n:ℝ)*S x) := by ring
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_add hnR]; rfl

theorem LocalCompactWaveData.lattice_residual_accuracy
    (K' : ℕ) (a : LocalCompactWaveData g w S D m J (K'+3) k0)
    (hw : ∀ x ∈ a.E, w x ≠ 0) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
        let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
        ContDiff ℝ ∞ residual ∧ ∀ x : Coord,
          DerivativeBound k0 residual x (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*S x)) := by
  have he : (3:ℝ)-((K'+3:ℕ):ℝ) = -(K':ℝ) := by push_cast; ring
  simpa only [he] using a.lattice_residual_derivative_bound hw hUD hUb

end
end Yau.Geometry

end OAI
