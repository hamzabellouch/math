import OAI.Analysis.MarkovType.HomogeneousRows
import OAI.Analysis.MarkovType.TriangularPrefix
import OAI.Analysis.MarkovType.C00FiniteCoordinates

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure SelectedRow (d : ℝ) (k : ℕ) where
  M : ℕ
  le_M : k ≤ M
  cubic_le_M : k ^ 3 ≤ M
  A : TriangularArray Y d (M : ℝ)⁻¹ M
  e : Fin k ↪o Fin M
  homogeneous : ∀ (m : ℕ) (_hm : m ≤ k) (a : Fin m → ℝ),
    (∀ i, |a i| ≤ 1) → ∀ s t : Fin m ↪o Fin k,
      |‖∑ i, a i • A.y (Fin.rev (e (s i)))‖ -
        ‖∑ i, a i • A.y (Fin.rev (e (t i)))‖| ≤ 3 / (k : ℝ)

variable {Y}

theorem exists_selectedRow (d : ℝ)
    (hrows : ∀ M : ℕ, 0 < M → Nonempty (TriangularArray Y d (M : ℝ)⁻¹ M))
    (k : ℕ) (hk : 0 < k) : Nonempty (SelectedRow Y d k) := by
  obtain ⟨M, hkM, hcubic, hselect⟩ := exists_homogeneous_rows (Y := Y) k hk
  obtain ⟨A⟩ := hrows M (hk.trans_le hkM)
  obtain ⟨e, he⟩ := hselect (fun i => A.y (Fin.rev i))
    (fun i => A.y_norm_le (Fin.rev i))
  exact ⟨⟨M, hkM, hcubic, A, e, he⟩⟩

namespace SelectedRow

variable {d : ℝ} {k : ℕ}

def vector (R : SelectedRow Y d k) (i : Fin k) : Y := R.A.y (Fin.rev (R.e i))

theorem norm_vector_le (R : SelectedRow Y d k) (i : Fin k) : ‖R.vector i‖ ≤ 1 :=
  R.A.y_norm_le _

def synthesis (R : SelectedRow Y d k) : C00 →ₗ[ℝ] Y :=
  Finsupp.linearCombination ℝ (fun j => if h : j < k then R.vector ⟨j, h⟩ else 0)

theorem synthesis_basis (R : SelectedRow Y d k) (j : ℕ) :
    R.synthesis (C00.basis j) = if h : j < k then R.vector ⟨j, h⟩ else 0 := by
  simp only [synthesis, C00.basis, Finsupp.linearCombination_single, one_smul]

theorem norm_synthesis_basis_le (R : SelectedRow Y d k) (j : ℕ) :
    ‖R.synthesis (C00.basis j)‖ ≤ 1 := by
  rw [synthesis_basis]
  split_ifs with h
  · exact R.norm_vector_le ⟨j, h⟩
  · simp

theorem synthesis_place (R : SelectedRow Y d k) {m : ℕ}
    (ι : Fin m → ℕ) (hι : ∀ i, ι i < k) (a : Fin m → ℝ) :
    R.synthesis (C00.place ι a) = ∑ i, a i • R.vector ⟨ι i, hι i⟩ := by
  simp only [C00.place, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [synthesis, Finsupp.linearCombination_single, dite_eq_left (hι i)]

theorem synthesis_ofArray (R : SelectedRow Y d k) {m : ℕ}
    (hm : m ≤ k) (a : Fin m → ℝ) :
    R.synthesis (C00.ofArray a) =
      ∑ i, a i • R.vector ⟨i.val, lt_of_lt_of_le i.isLt hm⟩ :=
  R.synthesis_place Fin.val (fun i => lt_of_lt_of_le i.isLt hm) a

theorem synthesis_prefix_lower (R : SelectedRow Y d k) (hd : 0 ≤ d)
    {m : ℕ} (hm : m ≤ k) (a : Fin m → ℝ) (r : ℕ) :
    d * |prefixCut (C00.ofArray a) r| - (R.M : ℝ)⁻¹ * coefficientL1 a ≤
      ‖R.synthesis (C00.ofArray a)‖ := by
  rw [R.synthesis_ofArray hm a]
  apply reversed_triangular_prefixCut_lower R.A hd
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun i => R.e ⟨i.val, lt_of_lt_of_le i.isLt hm⟩) _ a r
  intro i j hij
  exact R.e.strictMono hij

theorem synthesis_oscillation (R : SelectedRow Y d k) {m : ℕ} (hm : m ≤ k)
    (ι κ : Fin m → ℕ) (hι : StrictMono ι) (hκ : StrictMono κ)
    (hιk : ∀ i, ι i < k) (hκk : ∀ i, κ i < k)
    (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |‖R.synthesis (C00.place ι a)‖ - ‖R.synthesis (C00.place κ a)‖| ≤
      3 / (k : ℝ) := by
  let s : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨ι i, hιk i⟩) (fun i j hij => hι hij)
  let t : Fin m ↪o Fin k := OrderEmbedding.ofStrictMono
    (fun i => ⟨κ i, hκk i⟩) (fun i j hij => hκ hij)
  rw [R.synthesis_place ι hιk a, R.synthesis_place κ hκk a]
  exact R.homogeneous m hm a ha s t

end SelectedRow

end MarkovSuperreflexivity

end

end OAI
