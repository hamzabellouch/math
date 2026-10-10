import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice

namespace OAI


noncomputable section

namespace Problem355.PlaneRowTransport

open Matrix IntegralPlaneLattice

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

abbrev PlaneMatrices (x : Fin 3 → ℤ) := {A : IntMatrix // A *ᵥ x = 0}

def rows (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3) : lattice x :=
  ⟨⟨castVec (A.val i), by
    change realDot x (castVec (A.val i)) = 0
    rw [realDot_castVec]
    have hi : A.val i ⬝ᵥ x = 0 := congrFun A.property i
    rw [dotProduct_comm] at hi
    exact_mod_cast hi⟩, castVec_mem _⟩

@[simp] theorem rows_coordinate (x : Fin 3 → ℤ) (A : PlaneMatrices x)
    (i j : Fin 3) : (((rows x A i : lattice x) : plane x) : Ambient) j =
      (A.val i j : ℝ) := rfl

theorem rows_injective (x : Fin 3 → ℤ) : Function.Injective (rows x) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have hc := congrArg (fun f : Fin 3 → lattice x =>
    (((f i : lattice x) : plane x) : Ambient) j) h
  change (A.val i j : ℝ) = (B.val i j : ℝ) at hc
  exact_mod_cast hc

theorem linearIndependent_of_minor_ne_zero (u v : Ambient) (s t : Fin 3)
    (hminor : u s * v t - u t * v s ≠ 0) :
    LinearIndependent ℝ ![u, v] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hv
    have hv' : v = 0 := hv
    apply hminor
    simp [hv']
  · intro a ha
    have ha' : a • v = u := ha
    have hs := congrArg (fun w : Ambient => w s) ha'
    have ht := congrArg (fun w : Ambient => w t) ha'
    change a * v s = u s at hs
    change a * v t = u t at ht
    apply hminor
    rw [← hs, ← ht]
    ring

theorem rows_pair_linearIndependent_of_minor
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i j s t : Fin 3)
    (hminor : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
    LinearIndependent ℝ ![(rows x A i : plane x), (rows x A j : plane x)] := by
  have hm : castVec (A.val i) s * castVec (A.val j) t -
      castVec (A.val i) t * castVec (A.val j) s ≠ 0 := by
    simp only [castVec_apply]
    exact_mod_cast hminor
  apply LinearIndependent.of_comp (plane x).subtype
  convert linearIndependent_of_minor_ne_zero (castVec (A.val i))
    (castVec (A.val j)) s t hm using 1
  ext a
  fin_cases a <;> rfl

theorem rows_span_eq_top_of_minor
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (A : PlaneMatrices x) (i j s t : Fin 3)
    (hminor : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
    Submodule.span ℝ (Set.range (fun a => (rows x A a : plane x))) = ⊤ := by
  have hlin := rows_pair_linearIndependent_of_minor x A i j s t hminor
  have hspan := hlin.span_eq_top_of_card_eq_finrank
    (by simpa using (plane_finrank x z hz).symm)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro v ⟨a, rfl⟩
  fin_cases a
  · exact ⟨i, rfl⟩
  · exact ⟨j, rfl⟩

@[simp] theorem norm_rows (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3) :
    ‖rows x A i‖ = ‖castVec (A.val i)‖ := rfl

theorem norm_rows_le_of_coordinate_bounds
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3)
    {R : ℝ} (hR : 0 ≤ R) (hA : ∀ j, |(A.val i j : ℝ)| ≤ R) :
    ‖rows x A i‖ ≤ Real.sqrt 3 * R := by
  rw [norm_rows]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ j, ‖(castVec (A.val i)).ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, R ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq₀ (norm_nonneg _) hR).mpr
      simpa only [Real.norm_eq_abs, castVec, WithLp.ofLp_toLp] using hA j
    _ = 3 * R ^ 2 := by simp

theorem card_rows_image (x : Fin 3 → ℤ) (S : Finset (PlaneMatrices x)) :
    (S.image (rows x)).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (rows_injective x)

def projectedColumn (A : IntMatrix) (j : Fin 3) : ℝ × ℝ :=
  ((A 0 j : ℝ) / (A 2 j : ℝ), (A 1 j : ℝ) / (A 2 j : ℝ))

theorem exists_minor_of_projected_columns_ne
    (A : IntMatrix) (s t : Fin 3)
    (hs : A 2 s ≠ 0) (ht : A 2 t ≠ 0)
    (hne : projectedColumn A s ≠ projectedColumn A t) :
    ∃ i : Fin 3, i ≠ 2 ∧ A i s * A 2 t - A i t * A 2 s ≠ 0 := by
  by_contra h
  push Not at h
  have h₀ := sub_eq_zero.mp (h 0 (by decide))
  have h₁ := sub_eq_zero.mp (h 1 (by decide))
  have hsR : (A 2 s : ℝ) ≠ 0 := by exact_mod_cast hs
  have htR : (A 2 t : ℝ) ≠ 0 := by exact_mod_cast ht
  apply hne
  apply Prod.ext
  · apply (div_eq_div_iff hsR htR).mpr
    exact_mod_cast h₀
  · apply (div_eq_div_iff hsR htR).mpr
    exact_mod_cast h₁

theorem rows_span_eq_top_of_projected_columns_ne
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1)
    (A : PlaneMatrices x) (s t : Fin 3)
    (hs : A.val 2 s ≠ 0) (ht : A.val 2 t ≠ 0)
    (hne : projectedColumn A.val s ≠ projectedColumn A.val t) :
    Submodule.span ℝ (Set.range (fun a => (rows x A a : plane x))) = ⊤ := by
  obtain ⟨i, _, hi⟩ := exists_minor_of_projected_columns_ne A.val s t hs ht hne
  exact rows_span_eq_top_of_minor x z hz A i 2 s t hi

theorem norm_rows_le_four_mul
    (x : Fin 3 → ℤ) (A : PlaneMatrices x) (i : Fin 3)
    {N : ℝ} (hN : 0 ≤ N) (hA : ∀ j, |(A.val i j : ℝ)| ≤ 2 * N) :
    ‖rows x A i‖ ≤ 4 * N := by
  have hrow := norm_rows_le_of_coordinate_bounds x A i (by positivity) hA
  have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hm := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ 2 * N by positivity)
  exact hrow.trans (by nlinarith)

abbrev MatricesIn (x : Fin 3 → ℤ) (Γ : Submodule ℤ (plane x)) :=
  {A : PlaneMatrices x // ∀ i, (rows x A i : plane x) ∈ Γ}

def rowsIn (x : Fin 3 → ℤ) (Γ : Submodule ℤ (plane x))
    (A : MatricesIn x Γ) (i : Fin 3) : Γ :=
  ⟨(rows x A.val i : plane x), A.property i⟩

@[simp] theorem rowsIn_coe (x : Fin 3 → ℤ) (Γ : Submodule ℤ (plane x))
    (A : MatricesIn x Γ) (i : Fin 3) :
    (rowsIn x Γ A i : plane x) = (rows x A.val i : plane x) := rfl

theorem rowsIn_injective (x : Fin 3 → ℤ) (Γ : Submodule ℤ (plane x)) :
    Function.Injective (rowsIn x Γ) := by
  intro A B h
  apply Subtype.ext
  apply rows_injective x
  funext i
  apply Subtype.ext
  exact congrArg (fun f : Fin 3 → Γ => (f i : plane x)) h

theorem card_rowsIn_image (x : Fin 3 → ℤ) (Γ : Submodule ℤ (plane x))
    (S : Finset (MatricesIn x Γ)) :
    (S.image (rowsIn x Γ)).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (rowsIn_injective x Γ)

end Problem355.PlaneRowTransport

end

end OAI
