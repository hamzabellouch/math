import OAI.Analysis.KadisonKastler.CornerCuntzFamily

namespace OAI

/-! # A concrete infinite amplification

The amplification of a corner algebra is the commutant of its diagonally
represented commutant. Its matrix entries are exactly the operators in the
corner algebra. This construction uses the actual countable matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem norm_partialDiagonal_apply_le (s : Finset ℕ) (x : H) :
    ‖F.partialDiagonal s x‖ ≤ ‖x‖ := by
  rw [← F.coordinates.norm_map, ← F.coordinates.norm_map x]
  apply lp.norm_mono (by norm_num)
  intro i
  have he : F.coordinates (F.partialDiagonal s x) i =
      if i ∈ s then F.coordinates x i else 0 := by
    have hv : F.coordinates (F.partialDiagonal s x) =
        ∑ k ∈ s, lp.single 2 k (F.coordinates x k) := by
      simp only [partialDiagonal, sum_apply, map_sum, F.diagonal_apply,
        F.coordinates_column, ← F.coordinates_apply]
    rw [hv]
    change (⇑(∑ k ∈ s, lp.single 2 k (F.coordinates x k))) i = _
    rw [lp.coeFn_sum]
    simp [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [he]
  split_ifs <;> simp

theorem norm_partialDiagonal_le (s : Finset ℕ) : ‖F.partialDiagonal s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using F.norm_partialDiagonal_apply_le s x

theorem entry_column (i j k : ℕ) (x : E) :
    F.entry i j (F.column k x) = if j = k then F.column i x else 0 := by
  change (F.entry i j * F.entry k 0) x = _
  rw [F.mul_entry]
  split_ifs <;> rfl

theorem inflateHom_commute_entry (T : E →L[ℂ] E) (i j : ℕ) :
    Commute (F.inflateHom T) (F.entry i j) := by
  apply F.ext_on_columns
  intro k x
  simp only [mul_apply_eq_comp, F.entry_column, F.inflateHom_column]
  split_ifs
  · exact F.inflateHom_column T i x
  · simp

theorem inner_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) (x y : E) :
    inner ℂ y (F.matrixEntry T i j x) = inner ℂ (F.column i y) (T (F.column j x)) := by
  exact ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y _

theorem matrixEntry_inflate_mul (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (F.inflateHom S * T) i j = S * F.matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (F.inflateHom S (T (F.column j x))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateHom S) (F.column i y)) (T (F.column j x)) = _
  rw [← map_star, F.inflateHom_column, ← F.inner_matrixEntry]
  exact ContinuousLinearMap.adjoint_inner_left S (F.matrixEntry T i j x) y

theorem matrixEntry_mul_inflate (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (T * F.inflateHom S) i j = F.matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (T (F.inflateHom S (F.column j x))) = _
  rw [F.inflateHom_column, ← F.inner_matrixEntry]
  rfl

theorem ext_matrixEntry {T U : H →L[ℂ] H}
    (h : ∀ i j, F.matrixEntry T i j = F.matrixEntry U i j) : T = U := by
  apply F.ext_on_columns
  intro j x
  apply F.eq_of_inner_columns
  intro i y
  rw [← F.inner_matrixEntry, ← F.inner_matrixEntry, h]

/-- The concrete amplification in the coordinates supplied by `F`. -/
def amplifiedAlgebra (M : VonNeumannAlgebra E) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (F.inflateHom '' (M.commutant : Set (E →L[ℂ] E)))
  centralizer_centralizer' := by
    let S := F.inflateHom '' (M.commutant : Set (E →L[ℂ] E))
    change (S ∪ star S).centralizer.centralizer.centralizer = (S ∪ star S).centralizer
    exact Set.centralizer_centralizer_centralizer _

theorem mem_amplifiedAlgebra_iff_commute (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔
      ∀ S ∈ M.commutant, Commute (F.inflateHom S) T := by
  change T ∈ StarSubalgebra.centralizer ℂ _ ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h S hS
    exact (h (F.inflateHom S) ⟨S, hS, rfl⟩).1
  · intro h _ hS
    obtain ⟨S, hS, rfl⟩ := hS
    refine ⟨(h S hS).eq, ?_⟩
    rw [← map_star]
    exact (h (star S) (star_mem hS)).eq

/-- Matrix-entry membership characterizes the concrete amplification. -/
theorem mem_amplifiedAlgebra_iff (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔ ∀ i j, F.matrixEntry T i j ∈ M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  constructor
  · intro h i j
    rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
    intro S hS
    have hh := congrArg (fun R => F.matrixEntry R i j) (h S hS).eq
    simpa only [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate] using hh
  · intro h S hS
    apply F.ext_matrixEntry
    intro i j
    rw [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate]
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hS _ (h i j)).symm

theorem entry_mem_amplifiedAlgebra (M : VonNeumannAlgebra E) (i j : ℕ) :
    F.entry i j ∈ F.amplifiedAlgebra M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  intro S _
  exact F.inflateHom_commute_entry S i j

theorem inflate_mem_amplifiedAlgebra (M : VonNeumannAlgebra E) {T : E →L[ℂ] E}
    (hT : T ∈ M) : F.inflateHom T ∈ F.amplifiedAlgebra M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  intro S hS
  change F.inflateHom S * F.inflateHom T = F.inflateHom T * F.inflateHom S
  rw [← map_mul, ← map_mul]
  exact congrArg F.inflateHom (VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm

end FullMatrixCorner

end

end KadisonKastler

end OAI
