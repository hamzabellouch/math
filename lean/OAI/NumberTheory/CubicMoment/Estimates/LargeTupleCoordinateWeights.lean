import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleWeights
import OAI.NumberTheory.CubicMoment.Estimates.LargeTuplePartition

namespace OAI

/-! The actual independently smoothed prime coordinates of a large row
belong to one uniform family, for every norm partition and roughness scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

def largeTupleNormScale {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : ℝ := (4/3:ℝ)^(k a)/2

lemma largeTupleNormScale_pos {i j : ℕ} (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : 0 < largeTupleNormScale k a := by
  unfold largeTupleNormScale
  positivity

def largeTupleCoordinateWeight {i j : ℕ} (ξ X : ℝ) (k : (Fin i ⊕ Fin j) → ℕ)
    (a : Fin i ⊕ Fin j) : ℝ → ℂ :=
  match a with
  | .inl _ => distinguishedSmoothWeight
      (largeTupleNormScale k a/(X^ξ),largeTupleNormScale k a/(X^(2/5:ℝ)))
  | .inr _ => semiprimeSmoothWeight (largeTupleNormScale k a/(X^ξ))

def largeTupleCoordinateWeights (i j : ℕ) (ξ : ℝ) : UniformLogWeights
    (fun z : ({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j) =>
      largeTupleCoordinateWeight ξ z.1.1 z.1.2 z.2) := by
  let f : (({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j)) →
      (Ici (0:ℝ) × Ici (0:ℝ)) × Bool := fun z =>
    ((⟨largeTupleNormScale z.1.2 z.2/((z.1.1:ℝ)^ξ),
        div_nonneg (largeTupleNormScale_pos _ _).le (Real.rpow_nonneg z.1.1.property.le _)⟩,
      ⟨largeTupleNormScale z.1.2 z.2/((z.1.1:ℝ)^(2/5:ℝ)),
        div_nonneg (largeTupleNormScale_pos _ _).le (Real.rpow_nonneg z.1.1.property.le _)⟩),
      match z.2 with | .inl _ => true | .inr _ => false)
  have he : (fun z => largePrimeSmoothWeight (f z).1 (f z).2) =
      (fun z : ({X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ)) × (Fin i ⊕ Fin j) =>
        largeTupleCoordinateWeight ξ z.1.1 z.1.2 z.2) := by
    funext z x
    rcases z with ⟨r,a | b⟩ <;> rfl
  rw [←he]
  exact largePrimeSmoothWeights.reindex f

lemma roughSmoothWeight_at_prime {A : ℝ} (hA : 0 < A) (w : ℝ) (p : Eisenstein) :
    semiprimeSmoothWeight (A/w) (norm p/A) =
      normPartitionWeight (norm p/A)*(1-(primeDetectorCutoff (norm p/w):ℂ)) := by
  have he : (A/w)*(norm p/A) = norm p/w := by
    simp only [div_eq_mul_inv]
    calc
      A*w⁻¹*(norm p*A⁻¹) = (A*A⁻¹)*(norm p*w⁻¹) := by ring
      _ = norm p*w⁻¹ := by rw [mul_inv_cancel₀ hA.ne',one_mul]
  rw [semiprimeSmoothWeight,he]

lemma largeTupleCoordinateWeight_distinguished {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i) (p : Eisenstein) :
    largeTupleCoordinateWeight ξ X k (.inl a)
        (norm p/largeTupleNormScale k (.inl a)) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k (.inl a)))*
        distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) p := by
  rw [largeTupleCoordinateWeight,distinguishedSmoothWeight_at_prime (largeTupleNormScale_pos _ _)]
  rw [normPartitionWeight_scale]
  rfl

lemma largeTupleCoordinateWeight_rough {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (b : Fin j) (p : Eisenstein) :
    largeTupleCoordinateWeight ξ X k (.inr b)
        (norm p/largeTupleNormScale k (.inr b)) =
      normPartitionWeight (2*norm p/(4/3:ℝ)^(k (.inr b)))*
        (1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)) := by
  rw [largeTupleCoordinateWeight,roughSmoothWeight_at_prime (largeTupleNormScale_pos _ _)]
  rw [normPartitionWeight_scale]
  rfl

lemma largeTupleCoordinateWeight_norm {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) (x : ℝ) :
    ‖largeTupleCoordinateWeight ξ X k a x‖ ≤ 1 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_norm _ x
  · exact semiprimeSmoothWeight_norm _ x

lemma largeTupleCoordinateWeight_low {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : x < 1) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_low _ hx
  · exact semiprimeSmoothWeight_low _ hx

lemma largeTupleCoordinateWeight_high {i j : ℕ} (ξ X : ℝ)
    (k : (Fin i ⊕ Fin j) → ℕ) (a : Fin i ⊕ Fin j) {x : ℝ} (hx : 2 < x) :
    largeTupleCoordinateWeight ξ X k a x = 0 := by
  rcases a with a | b
  · exact distinguishedSmoothWeight_high _ hx
  · exact semiprimeSmoothWeight_high _ hx

end CubicFirstMoment

end

end OAI
