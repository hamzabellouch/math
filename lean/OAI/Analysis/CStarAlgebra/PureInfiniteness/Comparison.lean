import OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

local instance positivityOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance positivityStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def FiniteCuntzLE {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) : Prop :=
  ∃ r : ℕ → CStarMatrix (Fin m) (Fin n) A,
    Tendsto (fun j => (r j).conjTranspose * v * r j) atTop (𝓝 d)

def scalarCorner (h : A) : CStarMatrix (Fin 1) (Fin 1) A :=
  CStarMatrix.ofMatrix (fun _ _ => h)

def doubleCorner (h : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => h))

def ProperlyInfinite (h : A) : Prop :=
  FiniteCuntzLE (doubleCorner h) (scalarCorner h)

def PropertyP (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ h : A, 0 ≤ h → ProperlyInfinite h

def Diagonalization (a b c : A) (ε : ℝ) : Prop :=
  ∃ s t : A,
    ‖star s * a * s - a‖ < ε ∧
    ‖star t * b * t - b‖ < ε ∧
    ‖star s * c * t‖ < ε

def UnrestrictedDiagonalization (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε →
    Diagonalization a b c ε

def StronglyPurelyInfinite (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ x y : A, 0 ≤ x → 0 ≤ y → ∀ ε : ℝ, 0 < ε →
    Diagonalization (x * x) (y * y) (x * y) ε

lemma matrix_mul_assoc {l m n k : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) (z : CStarMatrix (Fin n) (Fin k) A) :
    (x * y) * z = x * (y * z) := Matrix.mul_assoc x y z

lemma matrix_star_mul {l m n : ℕ} (x : CStarMatrix (Fin l) (Fin m) A)
    (y : CStarMatrix (Fin m) (Fin n) A) :
    (x * y).conjTranspose = y.conjTranspose * x.conjTranspose :=
  Matrix.conjTranspose_mul x y

lemma continuous_matrix_mul {X : Type*} [TopologicalSpace X] {l m n : ℕ}
    {x : X → CStarMatrix (Fin l) (Fin m) A} {y : X → CStarMatrix (Fin m) (Fin n) A}
    (hx : Continuous x) (hy : Continuous y) : Continuous (fun t => x t * y t) :=
  hx.matrix_mul hy

lemma continuous_matrix_star {X : Type*} [TopologicalSpace X] {l m : ℕ}
    {x : X → CStarMatrix (Fin l) (Fin m) A} (hx : Continuous x) :
    Continuous (fun t => (x t).conjTranspose) := by
  change Continuous (fun t => Matrix.conjTranspose (x t))
  fun_prop

lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

lemma FiniteCuntzLE.exists_approx {m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} (h : FiniteCuntzLE d v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : CStarMatrix (Fin m) (Fin n) A, ‖d - r.conjTranspose * v * r‖ < ε := by
  rw [finiteCuntzLE_iff_closure, Metric.mem_closure_iff] at h
  obtain ⟨x, ⟨r, rfl⟩, hr⟩ := h ε hε
  exact ⟨r, by simpa only [dist_eq_norm] using hr⟩

lemma finiteCuntzLE_of_forall_approx {m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A}
    (h : ∀ ε > 0, ∃ r : CStarMatrix (Fin m) (Fin n) A,
      ‖d - r.conjTranspose * v * r‖ < ε) : FiniteCuntzLE d v := by
  rw [finiteCuntzLE_iff_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := h ε hε
  exact ⟨_, ⟨r, rfl⟩, by simpa only [dist_eq_norm] using hr⟩

lemma FiniteCuntzLE.conjugate {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} (hdv : FiniteCuntzLE d v)
    (x : CStarMatrix (Fin n) (Fin l) A) :
    FiniteCuntzLE (x.conjTranspose * d * x) v := by
  obtain ⟨r, hr⟩ := hdv
  refine ⟨fun j => r j * x, ?_⟩
  have hc : Continuous (fun d : CStarMatrix (Fin n) (Fin n) A =>
      x.conjTranspose * d * x) :=
    continuous_matrix_mul (continuous_matrix_mul continuous_const continuous_id) continuous_const
  convert hc.continuousAt.tendsto.comp hr using 1
  ext j
  rw [matrix_star_mul]
  simp only [Function.comp_apply, matrix_mul_assoc]

lemma FiniteCuntzLE.trans {l m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} {w : CStarMatrix (Fin l) (Fin l) A}
    (hdv : FiniteCuntzLE d v) (hvw : FiniteCuntzLE v w) : FiniteCuntzLE d w := by
  rw [finiteCuntzLE_iff_closure] at hdv ⊢
  apply closure_minimal _ isClosed_closure hdv
  rintro _ ⟨x, rfl⟩
  exact (finiteCuntzLE_iff_closure _ _).mp (hvw.conjugate x)

lemma isClosed_finiteCuntzLE {m n : ℕ} (v : CStarMatrix (Fin m) (Fin m) A) :
    IsClosed {d : CStarMatrix (Fin n) (Fin n) A | FiniteCuntzLE d v} := by
  simp_rw [finiteCuntzLE_iff_closure]
  exact isClosed_closure

lemma FiniteCuntzLE.of_tendsto {m n : ℕ} {v : CStarMatrix (Fin m) (Fin m) A}
    {d : ℕ → CStarMatrix (Fin n) (Fin n) A} {u : CStarMatrix (Fin n) (Fin n) A}
    (hd : ∀ j, FiniteCuntzLE (d j) v) (ht : Tendsto d atTop (𝓝 u)) :
    FiniteCuntzLE u v := (isClosed_finiteCuntzLE v).mem_of_tendsto ht (Eventually.of_forall hd)

lemma FiniteCuntzLE.refl {n : ℕ} (v : CStarMatrix (Fin n) (Fin n) A) :
    FiniteCuntzLE v v := by
  let M := CStarMatrix (Fin n) (Fin n) A
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  have hu := CStarAlgebra.increasingApproximateUnit M
  apply finiteCuntzLE_of_forall_approx
  intro ε hε
  have hl : ∀ᶠ e : M in CStarAlgebra.approximateUnit M, ‖v - v * e‖ < ε / 2 := by
    have ht := ((tendsto_const_nhds (x := v)).sub (hu.tendsto_mul_left v)).norm
    simpa only [sub_self, norm_zero] using ht.eventually (Iio_mem_nhds (by simpa only [sub_self, norm_zero] using half_pos hε))
  have hr : ∀ᶠ e : M in CStarAlgebra.approximateUnit M, ‖v - e * v‖ < ε / 2 := by
    have ht := ((tendsto_const_nhds (x := v)).sub (hu.tendsto_mul_right v)).norm
    simpa only [sub_self, norm_zero] using ht.eventually (Iio_mem_nhds (by simpa only [sub_self, norm_zero] using half_pos hε))
  obtain ⟨e, hesa, hen, hel, her⟩ :=
    (hu.eventually_star_eq.and (hu.eventually_norm.and (hl.and hr))).exists
  refine ⟨e, ?_⟩
  change ‖v - star e * v * e‖ < ε
  rw [hesa]
  calc
    ‖v - e * v * e‖ = ‖(v - e * v) + e * (v - v * e)‖ := by rw [mul_sub, ← mul_assoc]; congr 1; abel
    _ ≤ ‖v - e * v‖ + ‖e‖ * ‖v - v * e‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_mul_le _ _) _)
    _ ≤ ‖v - e * v‖ + ‖v - v * e‖ := by nlinarith [norm_nonneg (v - v * e)]
    _ < ε := by linarith

def matrixBlock {m n p q : ℕ} (x : CStarMatrix (Fin m) (Fin n) A)
    (y : CStarMatrix (Fin p) (Fin q) A) : CStarMatrix (Fin (m+p)) (Fin (n+q)) A :=
  CStarMatrix.ofMatrix ((Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm)

lemma matrixBlock_mul {m n p q r s : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) (y : CStarMatrix (Fin p) (Fin q) A)
    (u : CStarMatrix (Fin n) (Fin r) A) (v : CStarMatrix (Fin q) (Fin s) A) :
    matrixBlock x y * matrixBlock u v = matrixBlock (x * u) (y * v) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm *
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm u) 0 0 (CStarMatrix.ofMatrix.symm v)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm =
    (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x * CStarMatrix.ofMatrix.symm u) 0 0
      (CStarMatrix.ofMatrix.symm y * CStarMatrix.ofMatrix.symm v)).submatrix _ _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

lemma matrixBlock_star {m n p q : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) (y : CStarMatrix (Fin p) (Fin q) A) :
    (matrixBlock x y).conjTranspose = matrixBlock x.conjTranspose y.conjTranspose := by
  apply CStarMatrix.ext
  intro i j
  change star (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm x) 0 0 (CStarMatrix.ofMatrix.symm y) (finSumFinEquiv.symm j) (finSumFinEquiv.symm i)) = _
  generalize hi : finSumFinEquiv.symm i = i'
  generalize hj : finSumFinEquiv.symm j = j'
  cases i' <;> cases j' <;> simp [matrixBlock, Matrix.fromBlocks, Matrix.submatrix, hi, hj]

lemma continuous_matrixBlock {X : Type*} [TopologicalSpace X] {m n p q : ℕ}
    {x : X → CStarMatrix (Fin m) (Fin n) A} {y : X → CStarMatrix (Fin p) (Fin q) A}
    (hx : Continuous x) (hy : Continuous y) : Continuous (fun t => matrixBlock (x t) (y t)) := by
  change Continuous (fun t => (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (x t)) 0 0
      (CStarMatrix.ofMatrix.symm (y t))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t => Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (x t)) 0 0
      (CStarMatrix.ofMatrix.symm (y t)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
  cases finSumFinEquiv.symm i with
  | inl i' =>
    cases finSumFinEquiv.symm j with
    | inl j' =>
      change Continuous (fun t => CStarMatrix.ofMatrix.symm (x t) i' j')
      exact (continuous_apply j').comp ((continuous_apply i').comp hx)
    | inr j' => exact continuous_const
  | inr i' =>
    cases finSumFinEquiv.symm j with
    | inl j' => exact continuous_const
    | inr j' =>
      change Continuous (fun t => CStarMatrix.ofMatrix.symm (y t) i' j')
      exact (continuous_apply j').comp ((continuous_apply i').comp hy)

lemma tendsto_matrixBlock {X : Type*} {f : Filter X} {m n p q : ℕ}
    {x : X → CStarMatrix (Fin m) (Fin n) A} {y : X → CStarMatrix (Fin p) (Fin q) A}
    {u : CStarMatrix (Fin m) (Fin n) A} {v : CStarMatrix (Fin p) (Fin q) A}
    (hx : Tendsto x f (𝓝 u)) (hy : Tendsto y f (𝓝 v)) :
    Tendsto (fun t => matrixBlock (x t) (y t)) f (𝓝 (matrixBlock u v)) := by
  change Tendsto (fun t => CStarMatrix.ofMatrix.symm (matrixBlock (x t) (y t))) f
    (𝓝 (CStarMatrix.ofMatrix.symm (matrixBlock u v)))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun t => Matrix.fromBlocks (CStarMatrix.ofMatrix.symm (x t)) 0 0
      (CStarMatrix.ofMatrix.symm (y t)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) f
    (𝓝 (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm u) 0 0
      (CStarMatrix.ofMatrix.symm v) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)))
  cases finSumFinEquiv.symm i with
  | inl i' =>
    cases finSumFinEquiv.symm j with
    | inl j' => exact (hx.apply_nhds i').apply_nhds j'
    | inr j' => exact tendsto_const_nhds
  | inr i' =>
    cases finSumFinEquiv.symm j with
    | inl j' => exact tendsto_const_nhds
    | inr j' => exact (hy.apply_nhds i').apply_nhds j'

lemma matrixBlock_conjugate {m n p q : ℕ}
    (r : CStarMatrix (Fin m) (Fin n) A) (s : CStarMatrix (Fin p) (Fin q) A)
    (v : CStarMatrix (Fin m) (Fin m) A) (w : CStarMatrix (Fin p) (Fin p) A) :
    (matrixBlock r s).conjTranspose * matrixBlock v w * matrixBlock r s =
      matrixBlock (r.conjTranspose * v * r) (s.conjTranspose * w * s) := by
  rw [matrixBlock_star, matrixBlock_mul, matrixBlock_mul]

lemma FiniteCuntzLE.block {m n p q : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    {d' : CStarMatrix (Fin q) (Fin q) A} {v' : CStarMatrix (Fin p) (Fin p) A}
    (h : FiniteCuntzLE d v) (h' : FiniteCuntzLE d' v') :
    FiniteCuntzLE (matrixBlock d d') (matrixBlock v v') := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨s, hs⟩ := h'
  refine ⟨fun j => matrixBlock (r j) (s j), ?_⟩
  have heq : (fun j => (matrixBlock (r j) (s j)).conjTranspose *
      matrixBlock v v' * matrixBlock (r j) (s j)) =
      (fun j => matrixBlock ((r j).conjTranspose * v * r j)
        ((s j).conjTranspose * v' * s j)) := by
    funext j
    exact matrixBlock_conjugate (r j) (s j) v v'
  rw [heq]
  exact tendsto_matrixBlock hr hs

def diagonalCorner (n : ℕ) (h : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => h))

lemma matrixBlock_diagonal (n m : ℕ) (h : A) :
    matrixBlock (diagonalCorner n h) (diagonalCorner m h) = diagonalCorner (n+m) h := by
  apply CStarMatrix.ext
  intro i j
  change (Matrix.fromBlocks (Matrix.diagonal (fun _ => h)) 0 0
    (Matrix.diagonal (fun _ => h))).submatrix _ _ i j = _
  rw [Matrix.fromBlocks_diagonal]
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, diagonalCorner,
    CStarMatrix.ofMatrix_apply, Equiv.apply_eq_iff_eq]
  split_ifs with hij
  · cases finSumFinEquiv.symm i <;> rfl
  · rfl

lemma diagonalCorner_one (h : A) : diagonalCorner 1 h = scalarCorner h := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  change Matrix.diagonal (fun _ => h) i j = h
  simp [Matrix.diagonal, hij]

lemma ProperlyInfinite.finite_copies {h : A} (hh : ProperlyInfinite h) (n : ℕ) :
    FiniteCuntzLE (diagonalCorner n h) (scalarCorner h) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    have heq : (fun _ : ℕ => (0 : CStarMatrix (Fin 1) (Fin 0) A).conjTranspose *
        scalarCorner h * (0 : CStarMatrix (Fin 1) (Fin 0) A)) = fun _ => diagonalCorner 0 h := by
      funext j
      apply CStarMatrix.ext
      intro i
      exact Fin.elim0 i
    rw [heq]
    exact tendsto_const_nhds
  | succ n hn =>
    have hblock := hn.block (FiniteCuntzLE.refl (scalarCorner h))
    rw [← diagonalCorner_one h, matrixBlock_diagonal, matrixBlock_diagonal] at hblock
    exact hblock.trans hh

end MainGap

end

end OAI
