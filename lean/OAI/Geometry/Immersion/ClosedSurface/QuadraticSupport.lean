import OAI.Geometry.Immersion.ClosedSurface.CrossModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate displacement sumDisplacement)



abbrev QuadraticLabel (ι : Type*) := ι ⊕ (Σ i : ι, {j : ι // j ≠ i} × Bool)

def quadraticPhase {ι : Type*} (φ : ι → Base → ℝ) : QuadraticLabel ι → Base → ℝ
  | .inl i => fun p => 2 * φ i p
  | .inr ⟨i, j, b⟩ => if b then (fun p => φ i p - φ j p) else (fun p => φ i p + φ j p)

def quadraticAmplitude {n : ℕ} {ι : Type*} (τ : ℝ) (φ : ι → Base → ℝ)
    (Z : ι → Field n) : QuadraticLabel ι → SmallModes.Tensor
  | .inl i => phaseDoubleTensor τ (φ i) (Z i)
  | .inr ⟨i, j, b⟩ => if b then phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)
    else phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)

def quadraticSupport {ι : Type*} (S : ι → Set Base) : QuadraticLabel ι → Set Base
  | .inl i => S i
  | .inr ⟨i, j, _⟩ => S i ∩ S j

lemma nonzeroPhaseSum_eq_quadraticFamily {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Field n) :
    nonzeroPhaseSum τ φ Z = fun p => ∑ l : QuadraticLabel ι,
      displacement τ (quadraticPhase φ l) (quadraticAmplitude τ φ Z l) p := by
  funext p
  unfold nonzeroPhaseSum
  rw [Fintype.sum_sum_type]
  dsimp only [quadraticPhase, quadraticAmplitude]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ j : {j : ι // j ≠ i},
        (displacement τ (fun q => φ i q - φ j q) (phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)) p +
        displacement τ (fun q => φ i q + φ j q) (phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)) p) :=
      Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_bool]
      rfl

lemma derivativeAmplitude_zero_of_notMem {n : ℕ} {Z : Field n} {p : Base}
    (hp : p ∉ tsupport Z) (τ : ℝ) (φ : Base → ℝ) (v : Base) :
    derivativeAmplitude τ φ Z v p = 0 := by
  simp [derivativeAmplitude, fderiv_of_notMem_tsupport ℝ hp, image_eq_zero_of_notMem_tsupport hp]

lemma phasePlusTensor_tsupport {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : Field n) :
    tsupport (phasePlusTensor τ φ ψ Z W) ⊆ tsupport Z ∩ tsupport W := by
  apply closure_minimal _ ((isClosed_tsupport Z).inter (isClosed_tsupport W))
  intro p hp
  constructor
  · by_contra hn
    exact hp (by ext i; simp [phasePlusTensor, derivativeAmplitude_zero_of_notMem hn])
  · by_contra hn
    exact hp (by ext i; simp [phasePlusTensor, derivativeAmplitude_zero_of_notMem hn])

lemma phaseMinusTensor_tsupport {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : Field n) :
    tsupport (phaseMinusTensor τ φ ψ Z W) ⊆ tsupport Z ∩ tsupport W := by
  apply closure_minimal _ ((isClosed_tsupport Z).inter (isClosed_tsupport W))
  intro p hp
  constructor
  · by_contra hn
    exact hp (by ext i; simp [phaseMinusTensor, derivativeAmplitude_zero_of_notMem hn])
  · by_contra hn
    exact hp (by ext i; simp [phaseMinusTensor, derivativeAmplitude_zero_of_notMem hn,
      conjugate, dotProduct])

lemma quadraticAmplitude_tsupport {n : ℕ} {ι : Type*} (τ : ℝ) (φ : ι → Base → ℝ)
    (Z : ι → Field n) {S : ι → Set Base} (hZ : ∀ i, tsupport (Z i) ⊆ S i) :
    ∀ l : QuadraticLabel ι, tsupport (quadraticAmplitude τ φ Z l) ⊆ quadraticSupport S l := by
  intro l
  rcases l with i | ⟨i, j, b⟩
  · change tsupport (phasePlusTensor τ (φ i) (φ i) (Z i) (Z i)) ⊆ S i
    exact (phasePlusTensor_tsupport τ (φ i) (φ i) (Z i) (Z i)).trans
      (fun _ hh => hZ i hh.1)
  · cases b
    · exact (phasePlusTensor_tsupport τ (φ i) (φ j) (Z i) (Z j)).trans
        (inter_subset_inter (hZ i) (hZ j))
    · exact (phaseMinusTensor_tsupport τ (φ i) (φ j) (Z i) (Z j)).trans
        (inter_subset_inter (hZ i) (hZ j))

lemma quadraticAmplitude_smooth {n : ℕ} {ι : Type*} {φ : ι → Base → ℝ}
    {Z : ι → Field n} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hZ : ∀ i, ContDiff ℝ ∞ (Z i))
    (τ : ℝ) : ∀ l : QuadraticLabel ι, ContDiff ℝ ∞ (quadraticAmplitude τ φ Z l) := by
  intro l
  apply contDiffOn_univ.mp
  rcases l with i | ⟨i, j, b⟩
  · exact contDiffOn_phasePlusTensor isOpen_univ (hφ i).contDiffOn (hφ i).contDiffOn
      (hZ i).contDiffOn (hZ i).contDiffOn τ
  · cases b
    · exact contDiffOn_phasePlusTensor isOpen_univ (hφ i).contDiffOn (hφ j).contDiffOn
        (hZ i).contDiffOn (hZ j).contDiffOn τ
    · exact contDiffOn_phaseMinusTensor isOpen_univ (hφ i).contDiffOn (hφ j).contDiffOn
        (hZ i).contDiffOn (hZ j).contDiffOn τ

end ClosedSurfaceR4.RealModes

end

end OAI
