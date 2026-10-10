import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.MixedSlater
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HalfFilledSector
import Mathlib.Order.Hom.PowersetCard

namespace OAI

/-! The actual normalized Slater waves for the sorted occupied subsets of
finitely many orthonormal spin orbitals form an orthonormal family. Their
finite linear combination map is a genuine L2 isometry. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb.SlaterOccupation
open Coulomb

abbrev Occupied (Q n : ℕ) := Set.powersetCard (Fin (Q + 1)) n

def selection {Q n : ℕ} (S : Occupied Q n) : Fin n ↪o Fin (Q + 1) :=
  Set.powersetCard.ofFinEmbEquiv.symm S

lemma selection_mem {Q n : ℕ} (S : Occupied Q n) (j : Fin (Q + 1)) :
    j ∈ Set.range (selection S) ↔ j ∈ S.val :=
  Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S j

lemma selection_coincidence {Q n : ℕ} (S T : Occupied Q n) (p q : Equiv.Perm (Fin n)) :
    (∀ i, selection S (p i) = selection T (q i)) ↔ S = T ∧ p = q := by
  constructor
  · intro h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.ext
      intro j
      constructor
      · intro hj
        obtain ⟨i, hi⟩ := (selection_mem S j).mpr hj
        obtain ⟨k, hk⟩ := p.surjective i
        exact (selection_mem T j).mp ⟨q k, by rw [← h k, hk, hi]⟩
      · intro hj
        obtain ⟨i, hi⟩ := (selection_mem T j).mpr hj
        obtain ⟨k, hk⟩ := q.surjective i
        exact (selection_mem S j).mp ⟨p k, by rw [h k, hk, hi]⟩
    subst T
    refine ⟨rfl, ?_⟩
    apply Equiv.ext
    intro i
    exact (selection S).injective (h i)
  · rintro ⟨rfl, rfl⟩ i
    rfl

lemma selection_delta_product {Q n : ℕ} (S T : Occupied Q n) (p q : Equiv.Perm (Fin n)) :
    (∏ i, if selection S (p i) = selection T (q i) then (1 : ℂ) else 0) =
      if S = T ∧ p = q then 1 else 0 := by
  classical
  by_cases h : S = T ∧ p = q
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left ((selection_coincidence S T p q).mpr h i)
  · rw [ite_eq_right h]
    have hn : ¬∀ i, selection S (p i) = selection T (q i) :=
      fun hc => h ((selection_coincidence S T p q).mp hc)
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] {Q n : ℕ}

def selectedOrbitals (v : Fin (Q + 1) → A → ℂ) (S : Occupied Q n) : Fin n → A → ℂ :=
  fun i => v (selection S i)

def wave (v : Fin (Q + 1) → A → ℂ) (S : Occupied Q n) : (Fin n → A) → ℂ :=
  slaterWave (selectedOrbitals v S)

lemma wave_memLp (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ) (S : Occupied Q n) :
    MemLp (wave v S) 2 (Measure.pi fun _ => μ) :=
  slaterWave_memLp _ (fun i => hv (selection S i))

lemma determinant_overlap (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (S T : Occupied Q n) :
    (∫ x : Fin n → A, star (determinantWave (selectedOrbitals v S) x) *
      determinantWave (selectedOrbitals v T) x ∂(Measure.pi fun _ => μ)) =
      if S = T then (n.factorial : ℂ) else 0 := by
  classical
  unfold selectedOrbitals
  rw [MixedSlater.determinant_overlap_integral _ _
    (fun i => hv (selection S i)) (fun i => hv (selection T i))]
  simp only [ho, selection_delta_product]
  by_cases hST : S = T
  · subst T
    simp only [true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [sign_star_mul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · simp only [hST, false_and, ite_false, mul_zero, Finset.sum_const_zero]

lemma wave_overlap (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (S T : Occupied Q n) :
    (∫ x : Fin n → A, star (wave v S x) * wave v T x ∂(Measure.pi fun _ => μ)) =
      if S = T then (1 : ℂ) else 0 := by
  classical
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ) * Real.sqrt (n.factorial : ℝ) =
      (n.factorial : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt hn.le, Complex.ofReal_natCast]
  have hc : star (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) = (n.factorial : ℂ)⁻¹ := by
    simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
    rw [← mul_inv, hs]
  have heq (x : Fin n → A) : star (wave v S x) * wave v T x =
      (n.factorial : ℂ)⁻¹ * (star (determinantWave (selectedOrbitals v S) x) *
        determinantWave (selectedOrbitals v T) x) := by
    unfold wave slaterWave
    rw [star_mul]
    rw [← hc]
    ring
  simp_rw [heq]
  rw [integral_const_mul, determinant_overlap v hv ho]
  by_cases hST : S = T
  · have hnc : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simp only [hST, ite_true, inv_mul_cancel₀ hnc]
  · simp only [hST, ite_false, mul_zero]

def orbitalL2 (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ) (S : Occupied Q n) :
    Lp ℂ 2 (Measure.pi fun _ : Fin n => μ) := (wave_memLp v hv S).toLp (wave v S)

lemma orbitalL2_inner (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (S T : Occupied Q n) :
    inner ℂ (orbitalL2 v hv S) (orbitalL2 v hv T) = if S = T then 1 else 0 := by
  rw [L2.inner_def, ← wave_overlap v hv ho S T]
  apply integral_congr_ae
  filter_upwards [(wave_memLp v hv S).coeFn_toLp, (wave_memLp v hv T).coeFn_toLp] with x hx hy
  change inner ℂ ((wave_memLp v hv S).toLp (wave v S) x)
    ((wave_memLp v hv T).toLp (wave v T) x) = _
  rw [hx, hy, RCLike.inner_apply]
  exact mul_comm _ _

lemma orbitalL2_orthonormal (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    Orthonormal ℂ (orbitalL2 (n := n) v hv) := by
  classical
  rw [orthonormal_iff_ite]
  exact orbitalL2_inner v hv ho

def synthesis (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ) :
    EuclideanSpace ℂ (Occupied Q n) →ₗ[ℂ] Lp ℂ 2 (Measure.pi fun _ : Fin n => μ) where
  toFun x := ∑ S, x S • orbitalL2 v hv S
  map_add' x y := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp only [PiLp.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def synthesisIsometry (v : Fin (Q + 1) → A → ℂ) (hv : ∀ j, MemLp (v j) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    EuclideanSpace ℂ (Occupied Q n) →ₗᵢ[ℂ] Lp ℂ 2 (Measure.pi fun _ : Fin n => μ) :=
  (synthesis v hv).isometryOfInner (by
    intro x y
    change inner ℂ (∑ S, x S • orbitalL2 v hv S) (∑ S, y S • orbitalL2 v hv S) = _
    rw [(orbitalL2_orthonormal v hv ho).inner_sum x y Finset.univ]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro S _
    exact mul_comm _ _)

end ContinuumCoulomb.SlaterOccupation

end

end OAI
