import OAI.Analysis.CStarAlgebra.PureInfiniteness.Stabilization

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance matrixEntryOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance matrixEntryStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance algebraicTopology' : TopologicalSpace (Algebraic A) :=
  (inferInstance : PseudoMetricSpace (Algebraic A)).toUniformSpace.toTopologicalSpace

def paddedEntry (i j n : ℕ) (x : Mat A n) : A :=
  if hi : i < n then if hj : j < n then x ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

lemma paddedEntry_pad (i j : ℕ) {n m : ℕ} (h : n ≤ m) (x : Mat A n) :
    paddedEntry i j m (pad h x) = paddedEntry i j n x := by
  by_cases hi : i < n <;> by_cases hj : j < n
  · have hi' := lt_of_lt_of_le hi h
    have hj' := lt_of_lt_of_le hj h
    simp [paddedEntry, hi, hj, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hj, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hi', hj', pad_entry]
  · by_cases hi' : i < m <;> by_cases hj' : j < m <;>
      simp [paddedEntry, hi, hi', hj', pad_entry]

def entryAlgLinear (i j : ℕ) : Algebraic A →ₗ[ℂ] A where
  toFun := DirectLimit.lift _ (paddedEntry i j) (fun _ _ h x => (paddedEntry_pad i j h x).symm)
  map_add' := DirectLimit.induction₂ _ fun n x y => by
    rw [DirectLimit.add_def]
    change paddedEntry i j n (x+y) = paddedEntry i j n x + paddedEntry i j n y
    by_cases hi : i < n <;> by_cases hj : j < n <;> simp [paddedEntry, hi, hj]
  map_smul' c := DirectLimit.induction _ fun n x => by
    rw [DirectLimit.smul_def]
    change paddedEntry i j n (c • x) = c • paddedEntry i j n x
    by_cases hi : i < n <;> by_cases hj : j < n <;> simp [paddedEntry, hi, hj]

@[simp] lemma entryAlgLinear_corner (i j n : ℕ) (x : Mat A n) :
    entryAlgLinear i j (cornerAlg n x) = paddedEntry i j n x := rfl

lemma norm_entryAlgLinear_le (i j : ℕ) (x : Algebraic A) :
    ‖entryAlgLinear i j x‖ ≤ ‖x‖ := by
  induction x using DirectLimit.induction with
  | ih n x =>
    change ‖paddedEntry i j n x‖ ≤ ‖x‖
    by_cases hi : i < n <;> by_cases hj : j < n
    · simpa [paddedEntry, hi, hj] using
        (CStarMatrix.norm_entry_le_norm (M := x) (i := ⟨i,hi⟩) (j := ⟨j,hj⟩))
    all_goals simp [paddedEntry, hi, hj]

def entryAlg (i j : ℕ) : Algebraic A →L[ℂ] A :=
  (entryAlgLinear i j).mkContinuous 1 (fun x => by simpa using norm_entryAlgLinear_le i j x)

def entry (i j : ℕ) : Stabilization A → A :=
  UniformSpace.Completion.extension (entryAlg (A := A) i j)

lemma continuous_entry (i j : ℕ) : Continuous (entry (A := A) i j) :=
  UniformSpace.Completion.continuous_extension

@[simp] lemma entry_coe (i j : ℕ) (x : Algebraic A) :
    entry i j (x : Stabilization A) = entryAlg (A := A) i j x := by
  unfold entry
  exact UniformSpace.Completion.extension_coe (f := (entryAlg (A := A) i j))
    (ContinuousLinearMap.uniformContinuous (entryAlg (A := A) i j)) x

@[simp] lemma entry_corner (i j n : ℕ) (x : Mat A n) :
    entry i j (corner n x) = paddedEntry i j n x := by
  rw [corner_apply, entry_coe]
  rfl

def block (m n : ℕ) (x : Stabilization A) : CStarMatrix (Fin m) (Fin n) A :=
  CStarMatrix.ofMatrix fun i j => entry i.val j.val x

@[simp] lemma block_apply (m n : ℕ) (x : Stabilization A) (i : Fin m) (j : Fin n) :
    block m n x i j = entry i.val j.val x := rfl

lemma continuous_block (m n : ℕ) : Continuous (block (A := A) m n) := by
  exact continuous_pi fun i => continuous_pi fun j => (continuous_entry i.val j.val)

@[simp] lemma block_corner_self (n : ℕ) (x : Mat A n) : block n n (corner n x) = x := by
  ext i j
  simp only [block_apply, entry_corner, paddedEntry, dite_eq_left i.isLt, dite_eq_left j.isLt]

end MainGap.Stable

namespace MainGap.Stable
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance blockConjugateOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance blockConjugateStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance algebraicTopology'' : TopologicalSpace (Algebraic A) :=
  (inferInstance : PseudoMetricSpace (Algebraic A)).toUniformSpace.toTopologicalSpace

lemma paddedEntry_star (i j n : ℕ) (x : Mat A n) :
    paddedEntry i j n (star x) = star (paddedEntry j i n x) := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [paddedEntry, hi, hj, CStarMatrix.star_apply]

lemma paddedEntry_mul (i j n : ℕ) (x y : Mat A n) :
    paddedEntry i j n (x*y) =
      ∑ k : Fin n, paddedEntry i k.val n x * paddedEntry k.val j n y := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [paddedEntry, hi, hj, CStarMatrix.mul_apply]

lemma paddedEntry_conjugate (i j : ℕ) {m N : ℕ} (h : m ≤ N)
    (z : Mat A N) (v : Mat A m) :
    paddedEntry i j N (star z * pad h v * z) =
      ∑ q : Fin m, ∑ p : Fin m,
        star (paddedEntry p.val i N z) * v p q * paddedEntry q.val j N z := by
  classical
  simp only [paddedEntry_mul, paddedEntry_star, paddedEntry_pad]
  rw [← sum_pad h (fun q : Fin m => ∑ p : Fin m,
      star (paddedEntry p.val i N z) * v p q * paddedEntry q.val j N z)]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.val < m
  · rw [dite_eq_left hq, Finset.sum_mul]
    rw [← sum_pad h (fun p : Fin m =>
      star (paddedEntry p.val i N z) * v p ⟨q,hq⟩ * paddedEntry q.val j N z)]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.val < m <;> simp [paddedEntry, hp, hq]
  · simp [paddedEntry, hq]

lemma block_conjugate_corner {m N : ℕ} (h : m ≤ N) (n : ℕ)
    (v : Mat A m) (z : Mat A N) :
    block n n (star (corner N z) * corner m v * corner N z) =
      (block m n (corner N z)).conjTranspose * v * block m n (corner N z) := by
  rw [← corner_pad h v]
  have he : star (corner N z) * corner N (pad h v) * corner N z =
      corner N (star z * pad h v * z) := by rw [map_mul, map_mul, map_star]
  rw [he]
  ext i j
  simp only [block_apply, entry_corner, CStarMatrix.mul_apply,
    CStarMatrix.conjTranspose_apply, Finset.sum_mul]
  exact paddedEntry_conjugate i.val j.val h z v

lemma block_conjugate (m n : ℕ) (v : Mat A m) (x : Stabilization A) :
    block n n (star x * corner m v * x) =
      (block m n x).conjTranspose * v * block m n x := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (continuous_block n n).comp ((continuous_star.mul continuous_const).mul continuous_id)
    · have hc : Continuous (fun x : Stabilization A => (block m n x).conjTranspose) := by
        change Continuous (fun x : Stabilization A =>
          fun i j => star (block m n x j i))
        exact continuous_pi fun i => continuous_pi fun j =>
          continuous_star.comp (continuous_entry j.val i.val)
      exact (hc.matrix_mul continuous_const).matrix_mul (continuous_block m n)
  · intro z
    induction z using DirectLimit.induction with
    | ih k z =>
      change block n n (star (corner k z) * corner m v * corner k z) =
        (block m n (corner k z)).conjTranspose * v * block m n (corner k z)
      rw [← corner_pad (le_max_right m k) z]
      exact block_conjugate_corner (le_max_left m k) n v _

end MainGap.Stable

end

end OAI
