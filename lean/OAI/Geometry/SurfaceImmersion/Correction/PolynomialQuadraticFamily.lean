import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseSupport
import OAI.Geometry.Immersion.ClosedSurface.QuadraticSupport

namespace OAI

/-! Index the polynomial quadratic remainder by the same doubled and
mixed labels used for the metric quadratic remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open ModulatedJets

def quadraticFamilyPhase {ι : Type*} (φ : ι → Base → ℝ) :
    RealModes.QuadraticLabel ι → Base → ℝ
  | .inl i => fun p => 2 * φ i p
  | .inr ⟨i, j, b⟩ => if b then (fun p => φ i p - φ j p) else (fun p => φ i p + φ j p)

def quadraticFamilyCoefficient {n : ℕ} {ι : Type*}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    RealModes.QuadraticLabel ι → Base → ℂ
  | .inl i => quadraticPhaseCoefficient P ε G (φ i) (φ i) (H i) (H i) τ t
  | .inr ⟨i, j, b⟩ => if b then
      quadraticPhaseCoefficient P ε G (φ i) (fun p => -φ j p) (H i) (starField (H j)) τ t
    else quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t

def quadraticFamilySupport {ι : Type*} (S : ι → Set Base) :
    RealModes.QuadraticLabel ι → Set Base
  | .inl i => S i
  | .inr ⟨i, j, _⟩ => S i ∩ S j

lemma starField_tsupport (H : Base → Fin 4 → ℂ) : tsupport (starField H) ⊆ tsupport H := by
  apply closure_minimal _ (isClosed_tsupport H)
  intro p hp
  by_contra hn
  apply hp
  funext a
  simp only [starField, image_eq_zero_of_notMem_tsupport hn, Pi.zero_apply, star_zero]

lemma quadraticFamilyCoefficient_tsupport {n : ℕ} {ι : Type*}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    {S : ι → Set Base} (hH : ∀ i, tsupport (H i) ⊆ S i) :
    ∀ l, tsupport (quadraticFamilyCoefficient P ε G φ H τ t l) ⊆ quadraticFamilySupport S l := by
  intro l
  rcases l with i | ⟨i,j,b⟩
  · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (φ i) (H i) (H i) τ t).trans
      (fun _ hp => hH i hp.1)
  · cases b
    · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (φ j) (H i) (H j) τ t).trans
        (Set.inter_subset_inter (hH i) (hH j))
    · exact (quadraticPhaseCoefficient_tsupport P ε G (φ i) (fun p => -φ j p)
        (H i) (starField (H j)) τ t).trans
        (Set.inter_subset_inter (hH i) ((starField_tsupport (H j)).trans (hH j)))

theorem quadraticOscillation_eq_family {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticOscillation P ε G φ H τ t p =
      ∑ l : RealModes.QuadraticLabel ι,
        (phase τ (quadraticFamilyPhase φ l) p * quadraticFamilyCoefficient P ε G φ H τ t l p).re := by
  have hsplit (i : ι) :
      (∑ j, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) =
      (phase τ (fun x => 2 * φ i x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ i) (H i) (H i) τ t p).re +
      ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    have hh : (fun x => φ i x + φ i x) = (fun x => 2 * φ i x) := by funext x; ring
    rw [hh, add_comm]
  rw [quadraticOscillation, Fintype.sum_sum_type]
  simp only [hsplit, Finset.sum_add_distrib]
  change _ = _ + ∑ l : Σ i : ι, {j : ι // j ≠ i} × Bool, _
  rw [Fintype.sum_sigma]
  have hcross :
      (∑ i, ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) +
      (∑ i, ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x) (H i) (starField (H j)) τ t p).re) =
      ∑ i, ∑ l : {j : ι // j ≠ i} × Bool,
        (phase τ (quadraticFamilyPhase φ (.inr ⟨i,l⟩)) p *
          quadraticFamilyCoefficient P ε G φ H τ t (.inr ⟨i,l⟩) p).re := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    trans ∑ j : {j : ι // j ≠ i},
      ((phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re +
       (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re)
    · exact Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
    apply Finset.sum_congr rfl
    intro j hj
    rw [Fintype.sum_bool]
    simp only [quadraticFamilyPhase, quadraticFamilyCoefficient, Bool.false_eq_true, ↓reduceIte]
    ring
  change (_ + _) + _ = _ + _
  rw [add_assoc, hcross]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
