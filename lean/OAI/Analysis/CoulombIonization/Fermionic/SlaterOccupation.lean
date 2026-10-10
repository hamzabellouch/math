import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BlockEnergy
import OAI.Analysis.CoulombIonization.Variational.OrbitalPole

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

abbrev Occupied {n : ℕ} (m : Fin n → Bool) := {i : Fin n // m i = true}

def occupationIndex {n : ℕ} (m : Fin n → Bool) : Fin (Fintype.card (Occupied m)) ↪ Fin n :=
  (Fintype.equivFin (Occupied m)).symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

def occupationOrbitals {n : ℕ} {α : Type*} (φ : Fin n → α → ℂ) (m : Fin n → Bool) :
    Fin (Fintype.card (Occupied m)) → α → ℂ := fun j => φ (occupationIndex m j)

lemma occupationIndex_sum {n : ℕ} {R : Type*} [AddCommMonoid R]
    (m : Fin n → Bool) (f : Fin n → R) :
    (∑ j : Fin (Fintype.card (Occupied m)), f (occupationIndex m j)) =
      ∑ i : Fin n, if m i then f i else 0 := by
  calc
    _ = ∑ i : Occupied m, f i.1 :=
      Equiv.sum_comp (Fintype.equivFin (Occupied m)).symm (fun i : Occupied m => f i.1)
    _ = _ := by
      simpa only [Finset.subtype_univ,Finset.sum_filter] using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun i : Fin n => m i = true) f)

lemma occupationIndex_pair_sum {n : ℕ} {R : Type*} [AddCommMonoid R]
    (m : Fin n → Bool) (f : Fin n → Fin n → R) :
    (∑ j : Fin (Fintype.card (Occupied m)), ∑ k : Fin (Fintype.card (Occupied m)),
      f (occupationIndex m j) (occupationIndex m k)) =
      ∑ i : Fin n, ∑ l : Fin n, if m i && m l then f i l else 0 := by
  calc
    _ = ∑ j : Fin (Fintype.card (Occupied m)), ∑ l : Fin n,
        if m l then f (occupationIndex m j) l else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact occupationIndex_sum m (f (occupationIndex m j))
    _ = ∑ i : Fin n, if m i then (∑ l : Fin n, if m l then f i l else 0) else 0 :=
      occupationIndex_sum m (fun i => ∑ l : Fin n, if m l then f i l else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      cases m i <;> simp

lemma occupationOrbitals_sum {n : ℕ} {α R : Type*} [AddCommMonoid R]
    (φ : Fin n → α → ℂ) (m : Fin n → Bool) (f : (α → ℂ) → R) :
    (∑ j, f (occupationOrbitals φ m j)) = ∑ i, if m i then f (φ i) else 0 :=
  occupationIndex_sum m (fun i => f (φ i))

lemma occupationOrbitals_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (m : Fin n → Bool) :
    ∀ j s, ContDiff ℝ ∞ (fun x : Space => occupationOrbitals φ m j (s,x)) :=
  fun j s => hφ (occupationIndex m j) s

lemma occupationOrbitals_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (m : Fin n → Bool) :
    ∀ j s, HasCompactSupport (fun x : Space => occupationOrbitals φ m j (s,x)) :=
  fun j s => hc (occupationIndex m j) s

lemma occupationOrbitals_orthonormal {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {φ : Fin n → α → ℂ}
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂μ) = if i=k then 1 else 0)
    (m : Fin n → Bool) :
    ∀ j k, (∫ z, conj (occupationOrbitals φ m j z)*occupationOrbitals φ m k z ∂μ) =
      if j=k then 1 else 0 := by
  intro j k
  rw [occupationOrbitals,occupationOrbitals,ho]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem occupationSlater_admissible {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (m : Fin n → Bool) : FormAdmissible (slaterForm (occupationOrbitals φ m)) :=
  slaterForm_admissible (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

def orbitalCoreInteraction {N : ℕ} (ψ : FormVector N) (φ : SlaterParticle → ℂ) : ℝ :=
  ∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * orbitalPole φ (x j)

lemma core_orbital_integrable {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (s : Spins N) (j : Fin N) (i : Fin n) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * orbitalPole (φ i) (x j)) := by
  have hi := blockCross_inner_integrable hψ (slaterForm_sobolevFermion hφ hc).sobolevVector s j
  simp_rw [slaterForm_pole_trace hφ hc ho] at hi
  change Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) at hi
  apply hi.mono' (((hψ.1 s).aestronglyMeasurable.norm.pow 2).mul
    ((orbitalPole_continuous (hφ i) (hc i)).comp (continuous_apply j)).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖ψ.value s x‖^2 * orbitalPole (φ i) (x j)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (orbitalPole_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun k _ => orbitalPole_nonneg (φ k) (x j))
    (Finset.mem_univ i)) (sq_nonneg _)

lemma blockTensorCross_slater {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    blockTensorCross ψ (slaterForm φ) = ∑ k : Fin n, orbitalCoreInteraction ψ (φ k) := by
  rw [blockTensorCross_fubini hψ (slaterForm_sobolevFermion hφ hc).sobolevVector]
  simp_rw [slaterForm_pole_trace hφ hc ho]
  change (∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) = _
  have he (s : Spins N) (j : Fin N) :
      (∫ x : Configuration N, ‖ψ.value s x‖^2 * ∑ k : Fin n, orbitalPole (φ k) (x j)) =
      ∑ k : Fin n, ∫ x : Configuration N, ‖ψ.value s x‖^2 * orbitalPole (φ k) (x j) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun k _ => core_orbital_integrable hψ hφ hc ho s j k)
  simp_rw [he]
  calc
    _ = ∑ s : Spins N, ∑ k : Fin n, ∑ j : Fin N, ∫ x : Configuration N,
        ‖ψ.value s x‖^2 * orbitalPole (φ k) (x j) := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma occupationSlater_cross {N n : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * blockTensorCross ψ (slaterForm (occupationOrbitals φ m))) =
      ∑ i : Fin n, p i * orbitalCoreInteraction ψ (φ i) := by
  have he (m : Fin n → Bool) : blockTensorCross ψ (slaterForm (occupationOrbitals φ m)) =
      ∑ i : Fin n, if m i then orbitalCoreInteraction ψ (φ i) else 0 := by
    rw [blockTensorCross_slater hψ (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    exact occupationIndex_sum m (fun i => orbitalCoreInteraction ψ (φ i))
  simp_rw [he,occupation_sum]

end CoulombAtom

end

end OAI
