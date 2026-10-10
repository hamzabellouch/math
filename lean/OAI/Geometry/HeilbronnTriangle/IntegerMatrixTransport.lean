import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice

namespace OAI


noncomputable section

namespace Problem355.IntegerMatrixTransport

open IntegerSampling OrbitSampling

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ
abbrev Triple (N : ℕ) (shift : Fin 3 → ℤ) := Fin 3 → Box N 3 shift

theorem integralMatrix_injective {N : ℕ} {shift : Fin 3 → ℤ} :
    Function.Injective (integralMatrix : Triple N shift → IntMatrix) := by
  intro x y h
  funext j i
  apply Subtype.ext
  exact congrArg (fun A : IntMatrix => A i j) h

def matrixFamily {N : ℕ} {shift : Fin 3 → ℤ} (E : Finset (Triple N shift)) :
    Finset IntMatrix := by
  classical
  exact E.image integralMatrix

@[simp] theorem mem_matrixFamily {N : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (A : IntMatrix) :
    A ∈ matrixFamily E ↔ ∃ x ∈ E, integralMatrix x = A := by
  classical
  simp [matrixFamily]

@[simp] theorem card_matrixFamily {N : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) : (matrixFamily E).card = E.card := by
  classical
  exact Finset.card_image_of_injective E integralMatrix_injective

theorem sum_matrixFamily {N : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (W : IntMatrix → ℝ) :
    ∑ A ∈ matrixFamily E, W A = ∑ x ∈ E, W (integralMatrix x) := by
  classical
  exact Finset.sum_image (fun x hx y hy h => integralMatrix_injective h)

theorem matrixFamily_filter {N : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (P : IntMatrix → Prop) [DecidablePred P] :
    matrixFamily (E.filter (fun x => P (integralMatrix x))) =
      (matrixFamily E).filter P := by
  classical
  ext A
  simp only [mem_matrixFamily, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hp⟩
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩
    exact ⟨x, ⟨hx, hp⟩, rfl⟩

theorem sum_matrixFamily_filter {N : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (P : IntMatrix → Prop) [DecidablePred P]
    (W : IntMatrix → ℝ) :
    ∑ A ∈ (matrixFamily E).filter P, W A =
      ∑ x ∈ E.filter (fun x => P (integralMatrix x)), W (integralMatrix x) := by
  rw [← matrixFamily_filter]
  exact sum_matrixFamily _ W

theorem entry_bounds {N : ℕ} (x : Triple N (samplingShift N)) (i j : Fin 3) :
    0 ≤ integralMatrix x i j ∧ integralMatrix x i j < 2 * (N : ℤ) := by
  have h := (x j i).property
  change samplingShift N i ≤ integralMatrix x i j ∧
    integralMatrix x i j < samplingShift N i + (N : ℤ) at h
  fin_cases i <;> simp [samplingShift] at h ⊢ <;> omega

theorem height_bounds {N : ℕ} (x : Triple N (samplingShift N)) (j : Fin 3) :
    (N : ℤ) ≤ integralMatrix x 2 j ∧ integralMatrix x 2 j < 2 * (N : ℤ) := by
  have h := (x j 2).property
  change (N : ℤ) ≤ integralMatrix x 2 j ∧
    integralMatrix x 2 j < (N : ℤ) + N at h
  omega

theorem height_ne_zero {N : ℕ} (hN : 0 < N)
    (x : Triple N (samplingShift N)) (j : Fin 3) : integralMatrix x 2 j ≠ 0 := by
  have h := (height_bounds x j).1
  omega

theorem abs_entry_le {N : ℕ} (x : Triple N (samplingShift N)) (i j : Fin 3) :
    |integralMatrix x i j| ≤ 2 * (N : ℤ) := by
  rw [abs_of_nonneg (entry_bounds x i j).1]
  exact (entry_bounds x i j).2.le

theorem abs_real_entry_le {N : ℕ} (x : Triple N (samplingShift N)) (i j : Fin 3) :
    |(integralMatrix x i j : ℝ)| ≤ 2 * (N : ℝ) := by
  exact_mod_cast abs_entry_le x i j

theorem projectedColumn_eq {N : ℕ} (x : Triple N (samplingShift N)) (j : Fin 3) :
    (((integralMatrix x 0 j : ℝ) / integralMatrix x 2 j,
      (integralMatrix x 1 j : ℝ) / integralMatrix x 2 j) : Point) = project (x j) := rfl

theorem reduction_transpose {N h : ℕ} {shift : Fin 3 → ℤ}
    (x : Triple N shift) :
    (integralMatrix x).map (Int.castRingHom (ZMod h)) =
      Matrix.transpose (fun j => residue h (x j)) := rfl

theorem mem_orbit_iff_reduction_mem_slOrbit {N h : ℕ} [NeZero h]
    {shift : Fin 3 → ℤ} (C : Fin 3 → Fin 3 → ZMod h) (x : Triple N shift) :
    (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C ↔
      (integralMatrix x).map (Int.castRingHom (ZMod h)) ∈
        Section04Orbit.slOrbit (Matrix.transpose C) := by
  constructor
  · intro hx
    obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hx
    refine ⟨G, ?_⟩
    rw [reduction_transpose, ← hG, sl_action_transpose]
  · rintro ⟨G, hG⟩
    apply (mem_orbitFinset C _).mpr
    refine ⟨G, ?_⟩
    apply Matrix.transpose_injective
    rw [sl_action_transpose]
    exact hG

theorem rows_mem_integerRowLattice {N h : ℕ} [NeZero h]
    {shift : Fin 3 → ℤ} (C : Fin 3 → Fin 3 → ZMod h) (x : Triple N shift)
    (hx : (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C) (i : Fin 3) :
    integralMatrix x i ∈ RowLattice.integerRowLattice h (Matrix.transpose C) := by
  exact OrbitRowLattice.row_mem_integerRowLattice_of_reduction_mem_slOrbit h
    (Matrix.transpose C) (integralMatrix x)
    ((mem_orbit_iff_reduction_mem_slOrbit C x).mp hx) i

theorem determinant_residue {N h : ℕ} [NeZero h]
    {shift : Fin 3 → ℤ} (C : Fin 3 → Fin 3 → ZMod h) (x : Triple N shift)
    (hx : (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C) :
    ((integralMatrix x).det : ZMod h) = (Matrix.transpose C).det := by
  exact OrbitRowLattice.det_cast_eq_of_reduction_mem_slOrbit h
    (Matrix.transpose C) (integralMatrix x)
    ((mem_orbit_iff_reduction_mem_slOrbit C x).mp hx)

theorem auxiliaryWeight_integralMatrix {Ω : Type*} [Fintype Ω]
    {N q : ℕ} {shift : Fin 3 → ℤ} (s : ℕ) (w : Ω → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (x : Triple N shift) :
    LiftingProbability.auxiliaryWeight q s w V
      (fun j i => (integralMatrix x i j : ZMod q)) =
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j)) := rfl

def samplingMatrices (N : ℕ) : Finset IntMatrix :=
  matrixFamily (Finset.univ : Finset (Triple N (samplingShift N)))

theorem mem_matrixFamily_univ_iff {N : ℕ} {shift : Fin 3 → ℤ} (A : IntMatrix) :
    A ∈ matrixFamily (Finset.univ : Finset (Triple N shift)) ↔
      ∀ i j, shift i ≤ A i j ∧ A i j < shift i + (N : ℤ) := by
  classical
  rw [mem_matrixFamily]
  constructor
  · rintro ⟨x, _, rfl⟩ i j
    exact (x j i).property
  · intro h
    exact ⟨fun j i => ⟨A i j, h i j⟩, Finset.mem_univ _, rfl⟩

theorem mem_samplingMatrices_iff (N : ℕ) (A : IntMatrix) :
    A ∈ samplingMatrices N ↔ ∀ j,
      (0 ≤ A 0 j ∧ A 0 j < (N : ℤ)) ∧
      (0 ≤ A 1 j ∧ A 1 j < (N : ℤ)) ∧
      ((N : ℤ) ≤ A 2 j ∧ A 2 j < 2 * (N : ℤ)) := by
  rw [samplingMatrices, mem_matrixFamily_univ_iff]
  constructor
  · intro h j
    have h0 := h 0 j
    have h1 := h 1 j
    have h2 := h 2 j
    simpa [samplingShift, two_mul] using And.intro h0 (And.intro h1 h2)
  · intro h i j
    obtain ⟨h0, h1, h2⟩ := h j
    fin_cases i <;> simp [samplingShift] at * <;> omega

theorem matrixFamily_subset_samplingMatrices {N : ℕ}
    (E : Finset (Triple N (samplingShift N))) : matrixFamily E ⊆ samplingMatrices N := by
  classical
  intro A hA
  obtain ⟨x, hx, rfl⟩ := (mem_matrixFamily E A).mp hA
  exact (mem_matrixFamily _ _).mpr ⟨x, Finset.mem_univ _, rfl⟩

def matrixFiber {N h : ℕ} {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) :
    Finset IntMatrix := by
  classical
  exact (matrixFamily E).filter (fun A =>
    A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit (Matrix.transpose C) ∧ A.det = t)

theorem mem_matrixFiber {N h : ℕ} [NeZero h] {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (A : IntMatrix) : A ∈ matrixFiber E C t ↔
      ∃ x ∈ E, (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C ∧
        (integralMatrix x).det = t ∧ integralMatrix x = A := by
  classical
  simp only [matrixFiber, Finset.mem_filter, mem_matrixFamily]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ho, ht⟩
    exact ⟨x, hx, (mem_orbit_iff_reduction_mem_slOrbit C x).mpr ho, ht, rfl⟩
  · rintro ⟨x, hx, ho, ht, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (mem_orbit_iff_reduction_mem_slOrbit C x).mp ho, ht⟩

theorem matrixFiber_properties {N h : ℕ} [NeZero h]
    (E : Finset (Triple N (samplingShift N)))
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) (A : IntMatrix)
    (hA : A ∈ matrixFiber E C t) :
    A ∈ samplingMatrices N ∧
      (∀ i, A i ∈ RowLattice.integerRowLattice h (Matrix.transpose C)) ∧ A.det = t := by
  obtain ⟨x, hx, ho, ht, rfl⟩ := (mem_matrixFiber E C t A).mp hA
  exact ⟨(mem_matrixFamily _ _).mpr ⟨x, Finset.mem_univ _, rfl⟩,
    rows_mem_integerRowLattice C x ho, ht⟩

theorem sum_matrixFiber {N h : ℕ} [NeZero h] {shift : Fin 3 → ℤ}
    (E : Finset (Triple N shift)) (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (W : IntMatrix → ℝ) :
    ∑ A ∈ matrixFiber E C t, W A =
      ∑ x ∈ (E.filter (fun x =>
        (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C)).filter
        (fun x => (integralMatrix x).det = t), W (integralMatrix x) := by
  classical
  unfold matrixFiber
  rw [sum_matrixFamily_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, mem_orbit_iff_reduction_mem_slOrbit]
  tauto

theorem projected_pairwise_of_three {N : ℕ} (x : Triple N (samplingShift N))
    (h01 : project (x 0) ≠ project (x 1))
    (h02 : project (x 0) ≠ project (x 2))
    (h12 : project (x 1) ≠ project (x 2)) :
    ∀ i j : Fin 3, i ≠ j →
      (((integralMatrix x 0 i : ℝ) / integralMatrix x 2 i,
        (integralMatrix x 1 i : ℝ) / integralMatrix x 2 i) : Point) ≠
      (((integralMatrix x 0 j : ℝ) / integralMatrix x 2 j,
        (integralMatrix x 1 j : ℝ) / integralMatrix x 2 j) : Point) := by
  intro i j hij
  rw [projectedColumn_eq, projectedColumn_eq]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals first | exact Ne.symm h01 | exact Ne.symm h02 | exact Ne.symm h12

theorem matrixFiber_projected_pairwise {N h : ℕ} [NeZero h]
    (E : Finset (Triple N (samplingShift N)))
    (hE : ∀ x ∈ E, project (x 0) ≠ project (x 1) ∧
      project (x 0) ≠ project (x 2) ∧ project (x 1) ≠ project (x 2))
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) (A : IntMatrix)
    (hA : A ∈ matrixFiber E C t) :
    ∀ i j : Fin 3, i ≠ j →
      (((A 0 i : ℝ) / A 2 i, (A 1 i : ℝ) / A 2 i) : Point) ≠
      (((A 0 j : ℝ) / A 2 j, (A 1 j : ℝ) / A 2 j) : Point) := by
  obtain ⟨x, hx, _, _, rfl⟩ := (mem_matrixFiber E C t A).mp hA
  exact projected_pairwise_of_three x (hE x hx).1 (hE x hx).2.1 (hE x hx).2.2

end Problem355.IntegerMatrixTransport

end

end OAI
