import OAI.MeasureTheory.Falconer.Angular.TwoProjectionIntegerCaps
import OAI.MeasureTheory.Falconer.Radial.CoarsePlatePreparation
import OAI.MeasureTheory.Falconer.Radial.ThinTubeUpgrade
import OAI.MeasureTheory.Falconer.Measures.SupportPairFilter

namespace OAI

/-! # Half-integer cap availability in the first auxiliary space

All geometric hypotheses of the coarse-filter and thin-tube theorems are
verified for the selected, normalized original restrictions.
-/
namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ} {μ : ProbabilityMeasure (Space d)} {α ε : ℝ}
  {f : TwoProjectionFrame μ (h+3) (h+2) α}

namespace TwoProjectionPieces

theorem odd_auxiliary_caps_grid (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space (h+3) × Space (h+3)),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < (((p.left.map f.first : ProbabilityMeasure (Space (h+3))) : Measure (Space (h+3))).prod
        (p.right.map f.first : Measure (Space (h+3)))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair (p.left.map f.first) (p.right.map f.first)) ∧
      CapAvailable (p.left.map f.first) (p.right.map f.first) Γ ((h:ℝ)+3/2) ∧
      (∀ N : ℕ, ∃ T : Finset (List (Fin (h+3) → Bool) × List (Fin (h+3) → Bool)),
        T ⊆ (cubePaths (h+3) ⌊ω*(N:ℝ)⌋₊).product (cubePaths (h+3) ⌊ω*(N:ℝ)⌋₊) ∧
        Γ N = (⋃ pq ∈ T,
          ((centeredUnitCube (h+3)).descendant pq.1).carrier ×ˢ
          ((centeredUnitCube (h+3)).descendant pq.2).carrier) ∩
            supportPair (p.left.map f.first) (p.right.map f.first)) := by
  let ν₁ := p.left.map f.first
  let ν₂ := p.right.map f.first
  let Q := centeredUnitCube (h+3)
  have hroot₁ : (ν₁ : Measure (Space (h+3))) Q.carrier = 1 := by
    apply (mem_ae_iff_prob_eq_one Q.measurable).mp
    filter_upwards [Measure.support_mem_ae (μ := (ν₁ : Measure (Space (h+3))))] with x hx
    exact p.first_support_left hx
  have hroot₂ : (ν₂ : Measure (Space (h+3))) Q.carrier = 1 := by
    apply (mem_ae_iff_prob_eq_one Q.measurable).mp
    filter_upwards [Measure.support_mem_ae (μ := (ν₂ : Measure (Space (h+3))))] with x hx
    exact p.first_support_right hx
  have hbounded₁ : ∀ᵐ x ∂(ν₁ : Measure (Space (h+3))), ‖x‖ ≤ Real.sqrt (h+3:ℕ) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν₁ : Measure (Space (h+3))))] with x hx
    exact centeredUnitCube_norm_bound (p.first_support_left hx)
  have hbounded₂ : ∀ᵐ x ∂(ν₂ : Measure (Space (h+3))), ‖x‖ ≤ Real.sqrt (h+3:ℕ) := by
    filter_upwards [Measure.support_mem_ae (μ := (ν₂ : Measure (Space (h+3))))] with x hx
    exact centeredUnitCube_norm_bound (p.first_support_right hx)
  have hfrost := p.projected_frostman f.first f.first_frostman
  have hnat : h+3-2 = h+1 := by omega
  have hs : 1/2 < α-((h+3-2:ℕ):ℝ) := by rw [hnat]; push_cast; linarith
  have hs' : α-((h+3-2:ℕ):ℝ) < 1 := by rw [hnat]; push_cast; linarith
  obtain ⟨Γ₀,K,ζ,hK,hζ,hΓ₀,hanti,hpos,hpartition,hslabs⟩ :=
    coarse_plate_preparation hH (by omega : 3 ≤ h+3) ν₁ ν₂ Q
      (by norm_num [Q,centeredUnitCube]) (Real.sqrt_nonneg _)
      (fun _ hx => centeredUnitCube_norm_bound hx) hs hs' p.constant_pos.le
      hbounded₁ hbounded₂ hfrost.1 hfrost.2 hroot₁ hroot₂ p.first_noncharging hω hω1
  let Γ := fun N => Γ₀ N ∩ supportPair ν₁ ν₂
  have hΓ : ∀ N, MeasurableSet (Γ N) := fun N => (hΓ₀ N).inter (supportPair_measurable ν₁ ν₂)
  have hΓsub : ∀ N, Γ N ⊆ supportPair ν₁ ν₂ := fun _ => inter_subset_right
  have hstart : CapAvailable ν₁ ν₂ Γ ((h:ℝ)+1) := by
    have heq : α = ((h+1:ℕ):ℝ)+(α-((h+1:ℕ):ℝ)) := by ring
    have hδ : 0 < α-((h+1:ℕ):ℝ) := by push_cast; linarith
    have hδ1 : α-((h+1:ℕ):ℝ) < 1 := by push_cast; linarith
    have hcaps := p.first_integer_caps hR (by omega : 1 ≤ h+1) hδ hδ1 heq Γ hΓ hΓsub
    simpa only [Nat.cast_add,Nat.cast_one] using hcaps
  have hsep : 0 < p.lower*(p.radius/2) := mul_pos p.lower_pos (by linarith [p.radius_pos])
  have hpin : ∀ y ∈ Q.carrier, ∀ x ∈
      (ν₁ : Measure (Space (h+3))).support ∪ (ν₂ : Measure (Space (h+3))).support,
      ‖y-x‖ ≤ max 1 (Real.sqrt (h+3:ℕ)) := by
    intro y hy x hx
    have hxQ : x ∈ Q.carrier := hx.elim
      (fun hx' => p.first_support_left hx') (fun hx' => p.first_support_right hx')
    have hd := Q.dist_le (by norm_num [Q,centeredUnitCube]) hy hxQ
    have hd' : ‖y-x‖ ≤ Real.sqrt (h+3:ℕ) := by
      simpa only [dist_eq_norm,Q,centeredUnitCube,mul_one] using hd
    exact hd'.trans (le_max_right _ _)
  have hup := thin_tube_upgrade (Cplate := K) hF hLW hα hα' hζ p.constant_pos.le Q rfl
    (le_max_left _ _) (le_max_right _ _) hsep ν₁ ν₂
    ((prob_compl_eq_zero_iff Q.measurable).mpr hroot₁)
    ((prob_compl_eq_zero_iff Q.measurable).mpr hroot₂) hfrost.1 hfrost.2
    (ν₁ : Measure (Space (h+3))).support (ν₂ : Measure (Space (h+3))).support
    Measure.isClosed_support.measurableSet Measure.isClosed_support.measurableSet
    Measure.measure_compl_support Measure.measure_compl_support
    (fun z hz x hx => by simpa only [dist_eq_norm] using p.first_pair_separation z hz x hx)
    hpin Γ hΓ ?_ ?_ hstart
  · refine ⟨Γ,hΓ,?_,?_,hΓsub,hup,?_⟩
    · intro N N' hNN z hz
      exact ⟨hanti hNN hz.1,hz.2⟩
    · change 0 < ((ν₁ : Measure (Space (h+3))).prod (ν₂ : Measure (Space (h+3))))
        (⋂ N, Γ₀ N ∩ supportPair ν₁ ν₂)
      rw [supportPair_iInter_mass]
      exact hpos
    · intro N
      obtain ⟨T,hT,hTeq⟩ := hpartition N
      exact ⟨T,hT,congrArg (fun S => S ∩ supportPair ν₁ ν₂) hTeq⟩
  · intro N
    exact Filter.Eventually.of_forall (fun z w hw r hr hr1 =>
      (measure_mono (by intro x hx; exact ⟨hx.1.1,hx.2⟩)).trans ((hslabs N z w hw r hr hr1).1))
  · intro N
    exact Filter.Eventually.of_forall (fun x w hw r hr hr1 =>
      (measure_mono (by intro z hz; exact ⟨hz.1.1,hz.2⟩)).trans ((hslabs N x w hw r hr hr1).2))

theorem odd_auxiliary_caps (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space (h+3) × Space (h+3)),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < (((p.left.map f.first : ProbabilityMeasure (Space (h+3))) : Measure (Space (h+3))).prod
        (p.right.map f.first : Measure (Space (h+3)))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair (p.left.map f.first) (p.right.map f.first)) ∧
      CapAvailable (p.left.map f.first) (p.right.map f.first) Γ ((h:ℝ)+3/2) := by
  obtain ⟨Γ,hΓ,hanti,hpos,hsub,hcap,_⟩ :=
    p.odd_auxiliary_caps_grid hR hH hF hLW hα hα' hω hω1
  exact ⟨Γ,hΓ,hanti,hpos,hsub,hcap⟩

end TwoProjectionPieces
end Falconer

end OAI
