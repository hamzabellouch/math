import OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
local instance orthogonalSlotsPartialOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance orthogonalSlotsStarOrderedRing : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance orthogonalSlotsMatrixIsScalarTower (n : ℕ) :
    IsScalarTower ℝ (CStarMatrix (Fin n) (Fin n) A)
    (CStarMatrix (Fin n) (Fin n) A) where
  smul_assoc r x y := CStarMatrix.smul_mul r x y
local instance orthogonalSlotsMatrixSMulCommClass (n : ℕ) :
    SMulCommClass ℝ (CStarMatrix (Fin n) (Fin n) A)
    (CStarMatrix (Fin n) (Fin n) A) where
  smul_comm r x y := (CStarMatrix.mul_smul x r y).symm

lemma cut_map {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (f a) ε = f (cut a ε) :=
  (f.map_cfcₙ (q := IsSelfAdjoint) (fun t : ℝ => max (t-ε) 0) a
    (hf₀ := by simp [hε]) (ha := ha)).symm

def entry {n : ℕ} (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

@[simp] lemma entry_apply {n : ℕ} (i j k l : Fin n) (a : A) :
    entry i j a k l = if i = k ∧ j = l then a else 0 := rfl

@[simp] lemma entry_mul {n : ℕ} (i j k : Fin n) (a b : A) :
    entry i j a * entry j k b = entry i k (a * b) :=
  Matrix.single_mul_single_same a i j k b

lemma entry_mul_of_ne {n : ℕ} (i j k l : Fin n) (a b : A) (h : j ≠ k) :
    entry i j a * entry k l b = 0 :=
  Matrix.single_mul_single_of_ne a i j k h b

@[simp] lemma star_entry {n : ℕ} (i j : Fin n) (a : A) :
    star (entry i j a) = entry j i (star a) := by
  apply CStarMatrix.ext
  intro k l
  change star (Matrix.single i j a l k) = Matrix.single j i (star a) k l
  simp only [Matrix.single_apply]
  split_ifs <;> simp_all

@[simp] lemma entry_add {n : ℕ} (i j : Fin n) (a b : A) :
    entry i j (a+b) = entry i j a + entry i j b := Matrix.single_add _ _ _ _

@[simp] lemma entry_smul {n : ℕ} (i j : Fin n) (c : ℂ) (a : A) :
    entry i j (c • a) = c • entry i j a := (Matrix.smul_single _ _ _ _).symm

@[simp] lemma entry_zero {n : ℕ} (i j : Fin n) : entry i j (0 : A) = 0 :=
  Matrix.single_zero _ _

def cornerHom {n : ℕ} (i : Fin n) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := entry i i
  map_zero' := entry_zero i i
  map_add' := entry_add i i
  map_mul' := fun a b => (entry_mul i i i a b).symm
  map_smul' := entry_smul i i
  map_star' := fun a => (star_entry i i a).symm

lemma diagonalCorner_mul {n : ℕ} (a b : A) :
    diagonalCorner n (a*b) = diagonalCorner n a * diagonalCorner n b := by
  exact congrArg CStarMatrix.ofMatrix (Matrix.diagonal_mul_diagonal (fun _ => a) (fun _ => b)).symm

lemma star_diagonalCorner {n : ℕ} (a : A) :
    star (diagonalCorner n a) = diagonalCorner n (star a) := by
  apply CStarMatrix.ext
  intro i j
  change star (Matrix.diagonal (fun _ => a) j i) = Matrix.diagonal (fun _ => star a) i j
  simp only [Matrix.diagonal_apply]
  split_ifs <;> simp_all

def diagonalHom (n : ℕ) : A →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun := diagonalCorner n
  map_zero' := by ext i j; simp [diagonalCorner]
  map_add' a b := by ext i j; simp [diagonalCorner, Matrix.diagonal_apply]; split_ifs <;> simp
  map_mul' := diagonalCorner_mul
  map_smul' c a := by ext i j; simp [diagonalCorner, Matrix.diagonal_apply]
  map_star' := fun a => star_diagonalCorner a |>.symm

lemma corner_cut {n : ℕ} (i : Fin n) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (entry i i a) ε = entry i i (cut a ε) := by
  exact cut_map (cornerHom i) a ε ha hε

lemma diagonal_cut (n : ℕ) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (diagonalCorner n a) ε = diagonalCorner n (cut a ε) := by
  exact cut_map (diagonalHom n) a ε ha hε

lemma continuous_entry {n : ℕ} (i j : Fin n) : Continuous (entry (A := A) i j) := by
  change Continuous (fun a : A => (Matrix.single i j a : Matrix (Fin n) (Fin n) A))
  apply continuous_pi; intro k
  apply continuous_pi; intro l
  change Continuous (fun a : A => if i = k ∧ j = l then a else 0)
  split_ifs
  · exact continuous_id
  · exact continuous_const

lemma entry_mem_diagonalHer {n : ℕ} (i j : Fin n) {h a : A} (ha : a ∈ Her h) :
    entry i j a ∈ Her (diagonalCorner n h) := by
  refine closure_minimal (s := Set.range (fun b : A => h*b*star h))
    (t := {b | entry i j b ∈ Her (diagonalCorner n h)}) ?_ ?_ ha
  · rintro _ ⟨b, rfl⟩
    have heq : entry i j (h*b*star h) =
        diagonalCorner n h * entry i j b * star (diagonalCorner n h) := by
      rw [star_diagonalCorner]
      apply CStarMatrix.ext
      intro k l
      change Matrix.single i j (h*b*star h) k l =
        ((Matrix.diagonal (fun _ : Fin n => h) * Matrix.single i j b *
          Matrix.diagonal (fun _ : Fin n => star h)) : Matrix (Fin n) (Fin n) A) k l
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
      split_ifs <;> simp
    change entry i j (h*b*star h) ∈ Her _
    rw [heq]
    exact sandwich_mem_Her _ _
  · exact (isClosed_Her _).preimage (continuous_entry i j)

lemma cornerHer_entries {n : ℕ} (i : Fin n) {h : A}
    {a : CStarMatrix (Fin n) (Fin n) A} (ha : a ∈ Her (entry i i h))
    (j k : Fin n) : a j k ∈ Her h ∧ (j ≠ i ∨ k ≠ i → a j k = 0) := by
  refine closure_minimal (s := Set.range (fun b => entry i i h * b * star (entry i i h)))
    (t := {b | b j k ∈ Her h ∧ (j ≠ i ∨ k ≠ i → b j k = 0)}) ?_ ?_ ha
  · rintro _ ⟨b, rfl⟩
    have heq : entry i i h * b * star (entry i i h) = entry i i (h*b i i*star h) := by
      rw [star_entry]
      exact Matrix.single_mul_mul_single i i i i h (CStarMatrix.ofMatrix.symm b) (star h)
    change (entry i i h * b * star (entry i i h)) j k ∈ Her h ∧
      (j ≠ i ∨ k ≠ i → (entry i i h * b * star (entry i i h)) j k = 0)
    rw [heq, entry_apply]
    split_ifs with heq
    · refine ⟨sandwich_mem_Her h _, ?_⟩
      intro hjk
      rcases hjk with hj | hk
      · exact (hj heq.1.symm).elim
      · exact (hk heq.2.symm).elim
    · exact ⟨(Her h).zero_mem, by simp⟩
  · apply IsClosed.inter
    · exact (isClosed_Her _).preimage (by fun_prop)
    · by_cases hjk : j ≠ i ∨ k ≠ i
      · change IsClosed {b : CStarMatrix (Fin n) (Fin n) A | j ≠ i ∨ k ≠ i → b j k = 0}
        simpa only [hjk, true_implies] using
          (isClosed_eq (show Continuous (fun a : CStarMatrix (Fin n) (Fin n) A => a j k) by fun_prop)
          continuous_const)
      · simp only [hjk, false_implies]
        exact isClosed_univ

def rowMatrix {n : ℕ} (i : Fin n) (r : CStarMatrix (Fin 1) (Fin n) A) :
    CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (fun j k => if j = i then r 0 k else 0)

lemma rowMatrix_conjugate {n : ℕ} (i : Fin n)
    (r : CStarMatrix (Fin 1) (Fin n) A) (v : A) :
    star (rowMatrix i r) * entry i i v * rowMatrix i r =
      r.conjTranspose * scalarCorner v * r := by
  apply CStarMatrix.ext
  intro j k
  change (∑ l : Fin n, (∑ p : Fin n,
      star (if p = i then r 0 j else 0) * (if i = p ∧ i = l then v else 0)) *
      (if l = i then r 0 k else 0)) =
    ∑ l : Fin 1, (∑ p : Fin 1, star (r p j) * v) * r l k
  simp [mul_ite]

lemma finiteCuntzLE_corner_approx {n : ℕ} (i : Fin n) {d : CStarMatrix (Fin n) (Fin n) A}
    {v : A} (hdv : FiniteCuntzLE d (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : CStarMatrix (Fin n) (Fin n) A, ‖d - star s * entry i i v * s‖ < ε := by
  obtain ⟨r, hr⟩ := hdv.exists_approx hε
  exact ⟨rowMatrix i r, by rwa [rowMatrix_conjugate]⟩

lemma regularTransport_diagonal {n : ℕ} (i : Fin n) {d v : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner n d) (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (RegularTransport (diagonalCorner n (cut d ε)) (entry i i v)) := by
  obtain ⟨s, hs⟩ := finiteCuntzLE_corner_approx i hdv hε
  have hd' : 0 ≤ diagonalCorner n d := map_nonneg (diagonalHom n) hd
  have hv' : 0 ≤ entry i i v := map_nonneg (cornerHom i) hv
  have ht := regularTransport_of_approx hd' hv' hε hs
  rwa [diagonal_cut n d ε (.of_nonneg hd) hε.le] at ht

lemma row_zero_of_self_star {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) A) (i : Fin n)
    (hi : (M * star M) i i = 0) (j : Fin n) : M i j = 0 := by
  have hs : ∑ k : Fin n, M i k * star (M i k) = 0 := hi
  have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ M i k * star (M i k) :=
    fun k _ => mul_star_self_nonneg _
  have hzero := ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs) j (Finset.mem_univ j)
  apply norm_eq_zero.mp
  have hn : ‖M i j‖ * ‖M i j‖ = 0 := by rw [← CStarRing.norm_self_mul_star, hzero, norm_zero]
  nlinarith [norm_nonneg (M i j)]

lemma col_zero_of_star_self {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) A) (i : Fin n)
    (hi : (star M * M) i i = 0) (j : Fin n) : M j i = 0 := by
  have h := row_zero_of_self_star (star M) i (by simpa only [star_star] using hi) j
  change star (M j i) = 0 at h
  exact star_eq_zero.mp h

def entryHer {n : ℕ} {h : A} (i j : Fin n) (k : Her h) : Her (diagonalCorner n h) :=
  ⟨entry i j (k : A), entry_mem_diagonalHer i j k.property⟩

@[simp] lemma entryHer_val {n : ℕ} {h : A} (i j : Fin n) (k : Her h) :
    (entryHer i j k : CStarMatrix (Fin n) (Fin n) A) = entry i j (k : A) := rfl

namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

lemma carrier_entryHer (i : Fin n) (k : Her h) :
    T.carrier (entryHer i i₀ k) =
      entry i₀ i₀ ((T.carrier (entryHer i i₀ k)) i₀ i₀) := by
  let M := T.carrier (entryHer i i₀ k)
  have hrow (j : Fin n) (hj : j ≠ i₀) : ∀ l, M j l = 0 := by
    apply row_zero_of_self_star
    have hout := T.outer (entryHer i i₀ k) (entryHer i i₀ k)
    have hm := T.image (entryHer i i₀ k * star (entryHer i i₀ k))
    rw [← hout] at hm
    exact (cornerHer_entries i₀ hm j j).2 (Or.inl hj)
  have hcol (j : Fin n) (hj : j ≠ i₀) : ∀ l, M l j = 0 := by
    apply col_zero_of_star_self
    have hin := T.inner (entryHer i i₀ k) (entryHer i i₀ k)
    simp only [entryHer_val, star_entry, entry_mul] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a j j) hin
    simpa only [entry_apply, ne_comm.mp hj, false_and, ite_false] using he
  apply CStarMatrix.ext
  intro j l
  change M j l = (entry i₀ i₀ (M i₀ i₀)) j l
  rw [entry_apply]
  by_cases hj : j = i₀
  · subst j
    by_cases hl : l = i₀
    · subst l; simp
    · simp only [true_and, ne_comm.mp hl, ite_false]
      exact hcol l hl i₀
  · simp only [ne_comm.mp hj, false_and, ite_false]
    exact hrow j hj l

def slot (i : Fin n) (k : Her h) : A := T.carrier (entryHer i i₀ k) i₀ i₀

lemma slot_inner (i j : Fin n) (k l : Her h) :
    star (T.slot i₀ i k) * T.slot i₀ j l =
      if i = j then star (k : A) * (l : A) else 0 := by
  have hin := T.inner (entryHer i i₀ k) (entryHer j i₀ l)
  rw [T.carrier_entryHer i₀ i k, T.carrier_entryHer i₀ j l] at hin
  simp only [entryHer_val, star_entry, entry_mul] at hin
  change entry i₀ i₀ (star (T.slot i₀ i k) * T.slot i₀ j l) = _ at hin
  by_cases hij : i = j
  · subst j
    rw [entry_mul] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) hin
    simpa only [entry_apply, and_self, ite_true] using he
  · rw [entry_mul_of_ne _ _ _ _ _ _ hij] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) hin
    simpa only [entry_apply, and_self, ite_true, hij, ite_false, CStarMatrix.zero_apply] using he

lemma slot_outer_mem (i j : Fin n) (k l : Her h) :
    T.slot i₀ i k * star (T.slot i₀ j l) ∈ Her v := by
  have hout := T.outer (entryHer i i₀ k) (entryHer j i₀ l)
  have hm := T.image (entryHer i i₀ k * star (entryHer j i₀ l))
  rw [← hout, T.carrier_entryHer i₀ i k, T.carrier_entryHer i₀ j l,
    star_entry, entry_mul] at hm
  simpa only [slot, entry_apply, and_self, ite_true] using (cornerHer_entries i₀ hm i₀ i₀).1

lemma slot_mul (i : Fin n) (k l : Her h) :
    T.slot i₀ i (k*l) = T.slot i₀ i k * (l : A) := by
  have heq : entryHer i i₀ (k*l) = entryHer i i₀ k * entryHer i₀ i₀ l := by
    apply Subtype.ext
    exact (entry_mul i i₀ i₀ (k : A) (l : A)).symm
  have ht := T.mul (entryHer i i₀ k) (entryHer i₀ i₀ l)
  rw [← heq, T.carrier_entryHer i₀ i (k*l), T.carrier_entryHer i₀ i k, entryHer_val,
    entry_mul] at ht
  simpa only [slot, entry_apply, and_self, ite_true] using
    congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) ht

lemma slot_add (i : Fin n) (k l : Her h) :
    T.slot i₀ i (k+l) = T.slot i₀ i k + T.slot i₀ i l := by
  have heq : entryHer i i₀ (k+l) = entryHer i i₀ k + entryHer i i₀ l := by
    apply Subtype.ext
    exact entry_add i i₀ (k : A) (l : A)
  simp only [slot, heq, map_add, CStarMatrix.add_apply]

lemma slot_smul (i : Fin n) (c : ℂ) (k : Her h) :
    T.slot i₀ i (c • k) = c • T.slot i₀ i k := by
  have heq : entryHer i i₀ (c • k) = c • entryHer i i₀ k := by
    apply Subtype.ext
    exact entry_smul i i₀ c (k : A)
  simp only [slot, heq, map_smul, CStarMatrix.smul_apply]

lemma continuous_slot (i : Fin n) : Continuous (T.slot i₀ i) := by
  have he : Continuous (fun k : Her h => entryHer i i₀ k) := by
    apply Continuous.subtype_mk
    exact (continuous_entry i i₀).comp continuous_subtype_val
  change Continuous (fun k : Her h => T.carrier (entryHer i i₀ k) i₀ i₀)
  exact (continuous_apply i₀).comp ((continuous_apply i₀).comp (T.carrier.continuous.comp he))

def slotCLM (i : Fin n) : Her h →L[ℂ] A where
  toFun := T.slot i₀ i
  map_add' := T.slot_add i₀ i
  map_smul' := T.slot_smul i₀ i
  cont := T.continuous_slot i₀ i

end RegularTransport

structure OrthogonalSlots (n : ℕ) (h v : A) where
  carrier : Fin n → Her h →L[ℂ] A
  inner : ∀ i j k l, star (carrier i k) * carrier j l =
    if i = j then star (k : A) * (l : A) else 0
  outer : ∀ i j k l, carrier i k * star (carrier j l) ∈ Her v
  mul : ∀ i k l, carrier i (k*l) = carrier i k * (l : A)

theorem orthogonalSlots_of_comparison {n : ℕ} {d v : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner n d) (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (OrthogonalSlots n (cut d ε) v) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨{
      carrier := fun i => Fin.elim0 i
      inner := fun i => Fin.elim0 i
      outer := fun i => Fin.elim0 i
      mul := fun i => Fin.elim0 i }⟩
  · let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨T⟩ := regularTransport_diagonal i₀ hd hv hdv hε
    exact ⟨{
      carrier := T.slotCLM i₀
      inner := T.slot_inner i₀
      outer := T.slot_outer_mem i₀
      mul := T.slot_mul i₀ }⟩

theorem ProperlyInfinite.orthogonalSlots {d : A} (hd : 0 ≤ d) (hp : ProperlyInfinite d)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Nonempty (OrthogonalSlots n (cut d ε) d) :=
  orthogonalSlots_of_comparison hd hd (hp.finite_copies n) hε

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

lemma represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) (i : Fin n) (k : Her h) :
    ‖π (S.carrier i k)‖ = ‖π (k : A)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul,
    S.inner, ite_true]

lemma norm_carrier (i : Fin n) (k : Her h) : ‖S.carrier i k‖ = ‖(k : A)‖ :=
  S.represented_norm (NonUnitalStarAlgHom.id ℂ A) i k

end OrthogonalSlots

section FiniteSum

lemma FiniteCuntzLE.double {d v : A}
    (hdv : FiniteCuntzLE (scalarCorner d) (scalarCorner v)) :
    FiniteCuntzLE (doubleCorner d) (doubleCorner v) := by
  have hh := hdv.block hdv
  rw [← diagonalCorner_one d, ← diagonalCorner_one v, matrixBlock_diagonal,
    matrixBlock_diagonal] at hh
  exact hh

lemma finiteSum_cuntzLE {v : A} (hv : ProperlyInfinite v) {n : ℕ} (r : Fin n → A) :
    FiniteCuntzLE (scalarCorner (∑ i, star (r i) * v * r i)) (scalarCorner v) := by
  let x : CStarMatrix (Fin n) (Fin 1) A := CStarMatrix.ofMatrix (fun i _ => r i)
  have hcomp : x.conjTranspose * diagonalCorner n v * x =
      scalarCorner (∑ i, star (r i) * v * r i) := by
    ext i j
    change (∑ k : Fin n, (∑ l : Fin n, star (r l) *
      (if l = k then v else 0)) * r k) = _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  rw [← hcomp]
  exact (hv.finite_copies n).conjugate x

lemma finiteSum_two_cuntzLE {v : A} (hv : ProperlyInfinite v) {n : ℕ} (r : Fin n → A) :
    FiniteCuntzLE (diagonalCorner 2 (∑ i, star (r i) * v * r i)) (scalarCorner v) :=
  (finiteSum_cuntzLE hv r).double.trans hv

lemma finsetSum_cuntzLE {v : A} (hv : ProperlyInfinite v) {ι : Type*}
    (E : Finset ι) (r : ι → A) :
    FiniteCuntzLE (diagonalCorner 2 (∑ i ∈ E, star (r i) * v * r i)) (scalarCorner v) := by
  classical
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  have hsum : (∑ i : Fin (Fintype.card E), star (r (e i)) * v * r (e i)) =
      ∑ i ∈ E, star (r i) * v * r i := by
    calc
      _ = ∑ i : E, star (r i) * v * r i := Equiv.sum_comp e _
      _ = _ := by simpa using (Finset.sum_attach E (fun i => star (r i) * v * r i))
  rw [← hsum]
  exact finiteSum_two_cuntzLE hv _

end FiniteSum
end MainGap

end

end OAI
