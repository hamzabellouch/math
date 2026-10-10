import OAI.Algebra.Determinantal.AdjugateNormalForm

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowNormalForm
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def rowMultiplier (v : ι → R) : Matrix ι ι R := fun i _ => v i

noncomputable def rowPair (A : Matrix ι ι R) (v : ι → R) : R[X] :=
  adjTrace A (rowMultiplier v)

noncomputable def rowEntry (A : Matrix ι ι R) (i : ι) : R[X] :=
  ∑ j, (pencilMatrix A).adjugate j i

noncomputable def rowIdeal (A : Matrix ι ι R) : Ideal R[X] :=
  Ideal.span (Set.range (rowEntry A))

theorem rowPair_eq_sum (A : Matrix ι ι R) (v : ι → R) :
    rowPair A v = ∑ i, C (v i) * rowEntry A i := by
  simp only [rowPair, adjTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, rowMultiplier, rowEntry, Finset.mul_sum]

theorem rowPair_add (A : Matrix ι ι R) (v w : ι → R) :
    rowPair A (v+w) = rowPair A v + rowPair A w := by
  exact adjTrace_add _ _ _

theorem rowPair_smul (A : Matrix ι ι R) (a : R) (v : ι → R) :
    rowPair A (a • v) = C a * rowPair A v := by
  exact adjTrace_smul _ _ _

theorem rowPair_zero (A : Matrix ι ι R) : rowPair A 0 = 0 := adjTrace_zero _

theorem adjTrace_mul_comm (A Y : Matrix ι ι R) :
    adjTrace A (Y*A) = adjTrace A (A*Y) := by
  have h := trace_commutator_adjugate_scalar (A.map C) (Y.map C) (X : R[X])
  simp only [sub_mul, Matrix.trace_sub, ← Matrix.map_mul] at h
  exact (sub_eq_zero.mp h).symm

theorem X_mul_rowPair (A : Matrix ι ι R) (v : ι → R) :
    X * rowPair A v = rowPair A (-(A.mulVec v)) +
      C (∑ i, v i) * (pencilMatrix A).det := by
  rw [rowPair, X_mul_adjTrace, adjTrace_neg, adjTrace_mul_comm]
  have h : A * rowMultiplier v = rowMultiplier (A.mulVec v) := by
    ext i j
    rfl
  rw [h]
  change -adjTrace A (rowMultiplier (A.mulVec v)) + _ = _
  rw [← adjTrace_neg]
  rfl

def HasRowNormalForm (A : Matrix ι ι R) (P : R[X]) : Prop :=
  ∃ v : ι → R, ∃ H : R[X], P = rowPair A v + H * (pencilMatrix A).det

namespace HasRowNormalForm
variable {A : Matrix ι ι R} {P Q : R[X]}
theorem zero : HasRowNormalForm A 0 := ⟨0, 0, by simp [rowPair_zero]⟩
theorem add (hP : HasRowNormalForm A P) (hQ : HasRowNormalForm A Q) :
    HasRowNormalForm A (P+Q) := by
  obtain ⟨v,H,rfl⟩ := hP
  obtain ⟨w,J,rfl⟩ := hQ
  exact ⟨v+w,H+J, by rw [rowPair_add]; ring⟩
theorem C_mul (hP : HasRowNormalForm A P) (a : R) :
    HasRowNormalForm A (C a * P) := by
  obtain ⟨v,H,rfl⟩ := hP
  exact ⟨a • v,C a * H, by rw [rowPair_smul]; ring⟩
theorem X_mul (hP : HasRowNormalForm A P) : HasRowNormalForm A (X*P) := by
  obtain ⟨v,H,rfl⟩ := hP
  refine ⟨-(A.mulVec v),C (∑ i, v i) + X*H, ?_⟩
  rw [mul_add, X_mul_rowPair]
  ring
theorem mul (hP : HasRowNormalForm A P) (f : R[X]) : HasRowNormalForm A (f*P) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [add_mul] using hf.add hg
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_assoc]
    apply HasRowNormalForm.C_mul
    induction n with
    | zero => simpa using hP
    | succ n ih => simpa only [pow_succ', mul_assoc] using ih.X_mul
end HasRowNormalForm

theorem normalForm_of_mem_rowIdeal (A : Matrix ι ι R) (P : R[X])
    (hP : P ∈ rowIdeal A) : HasRowNormalForm A P := by
  let J : Ideal R[X] :=
    { carrier := {P | HasRowNormalForm A P}
      zero_mem' := HasRowNormalForm.zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun f _ h => h.mul f }
  have hle : rowIdeal A ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change HasRowNormalForm A (rowEntry A i)
    refine ⟨Pi.single i 1,0, ?_⟩
    simp [rowPair_eq_sum, Pi.single_apply]
  exact hle hP
end RowNormalForm

section RowDegree
variable {K : Type*} [Field K] {k : ℕ}

theorem rowPair_degree_le (A : Matrix (Fin (k+1)) (Fin (k+1)) K[X])
    (v : Fin (k+1) → K[X]) : (rowPair A v).natDegree ≤ k :=
  natDegree_adjTrace_le _ _

theorem exists_row_multiplier (A : Matrix (Fin (k+1)) (Fin (k+1)) K[X])
    (P : K[X][X]) (hP : P ∈ rowIdeal A) (hdeg : P.natDegree ≤ k) :
    ∃ v : Fin (k+1) → K[X], P = rowPair A v := by
  obtain ⟨v,H,h⟩ := normalForm_of_mem_rowIdeal A P hP
  have hH : H = 0 := by
    by_contra hn
    have hF : (pencilMatrix A).det ≠ 0 := by
      intro hz
      have := natDegree_det_pencilMatrix A
      simp only [hz, natDegree_zero] at this
      omega
    have hd : (H*(pencilMatrix A).det).natDegree ≤ k := by
      have he : H*(pencilMatrix A).det = P - rowPair A v := by rw [h]; ring
      rw [he]
      exact (natDegree_sub_le _ _).trans (max_le hdeg (rowPair_degree_le A v))
    rw [natDegree_mul hn hF, natDegree_det_pencilMatrix] at hd
    omega
  exact ⟨v, by simpa only [hH,zero_mul,add_zero] using h⟩

theorem row_multiplier_is_constant (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K[X]) (d : ℕ)
    (hv : ∀ i, (v i).natDegree ≤ d)
    (hdeg : (scaleHom (rowPair (pencilBase θ A) v)).natDegree ≤ k) :
    ∀ i, v i = C ((v i).coeff 0) := by
  have hs : (scaledTrace θ A (rowMultiplier v)).natDegree ≤ k := by
    simpa only [rowPair, scaleHom_adjTrace] using hdeg
  induction d with
  | zero =>
    intro i
    have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hv i))
    simpa using he
  | succ d ih =>
    apply ih
    intro i
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n = d+1
    · subst n
      exact diagonal_top_zero θ hθ A (rowMultiplier v) (d+1) (by omega)
        (fun i _ => hv i) hs i
    · exact coeff_eq_zero_of_natDegree_lt ((hv i).trans_lt (by omega))

theorem exists_constant_row_multiplier (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ rowIdeal (pencilBase θ A)) (ho : P.natDegree ≤ k)
    (ht : (scaleHom P).natDegree ≤ k) :
    ∃ v : Fin (k+1) → K, P = rowPair (pencilBase θ A) (fun i => C (v i)) := by
  obtain ⟨v,hv⟩ := exists_row_multiplier _ P hP ho
  obtain ⟨d,hd⟩ := (Set.finite_range (fun i => (v i).natDegree)).bddAbove
  have hc := row_multiplier_is_constant θ hθ A v d (fun i => hd ⟨i,rfl⟩) (hv ▸ ht)
  exact ⟨fun i => (v i).coeff 0, hv.trans (by congr 1; funext i; exact hc i)⟩
end RowDegree
end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowLength
variable {K : Type*} [Field K] {k : ℕ}
noncomputable def rowContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) : K[X][X] :=
  rowPair (pencilBase θ A) (fun i => C (v i))

theorem rowContraction_mem (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    rowContraction θ A v ∈ rowIdeal (pencilBase θ A) := by
  rw [rowContraction, rowPair_eq_sum]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)

theorem totalDegreeLE_rowEntry (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    TotalDegreeLE (rowEntry (pencilBase θ A) i) k := by
  exact TotalDegreeLE.sum _ _ (fun j _ => totalDegreeLE_cofactor θ A j i)

theorem totalDegreeLE_rowContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    TotalDegreeLE (rowContraction θ A v) k := by
  rw [rowContraction, rowPair_eq_sum]
  apply TotalDegreeLE.sum
  intro i _
  simpa only [zero_add, monomial_zero_left] using
    (totalDegreeLE_monomial 0 0 (v i)).mul (totalDegreeLE_rowEntry θ A i)

theorem rowContraction_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    (scaleHom (rowContraction θ A v)).coeff k = slopeTrace θ v := by
  have ht := coeff_scaledTrace_top θ A (rowMultiplier (fun i => C (v i))) 0
    (fun _ _ => by simp [rowMultiplier])
  simp only [zero_add] at ht
  rw [rowContraction, rowPair, scaleHom_adjTrace, ht]
  simp [slopeTrace, spectralSlope, Matrix.adjugate_diagonal, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_diagonal, Matrix.map_apply, rowMultiplier]

theorem exists_rowContraction_top (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (a : ℕ) (ha : a ≤ k) :
    ∃ v : Fin (k+1) → K,
      (scaleHom (rowContraction θ A v)).coeff k = monomial a 1 := by
  obtain ⟨v,hv⟩ := exists_diagonalContraction_top θ hθ A a ha
  refine ⟨v, ?_⟩
  rw [rowContraction_top]
  have ht := coeff_scaledTrace_top θ A ((Matrix.diagonal v).map C) 0 (by simp)
  simp only [zero_add] at ht
  rw [diagonalContraction, scaleHom_adjTrace, ht] at hv
  convert hv using 1
  simp [slopeTrace]

theorem exists_lower_row_representative
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (a b : ℕ) (hab : a+b = k) :
    ∃ R : K[X][X], TotalDegreeLE R (k-1) ∧
      monomial a (monomial b 1) - R ∈ rowIdeal (pencilBase θ A) := by
  obtain ⟨v,hv⟩ := exists_rowContraction_top θ hθ A a (by omega)
  let R := monomial a (monomial b (1 : K)) - rowContraction θ A v
  refine ⟨R, ?_, ?_⟩
  · apply TotalDegreeLE.pred_of_top_zero hk
    · exact ((totalDegreeLE_monomial a b (1 : K)).mono hab.le).sub
        (totalDegreeLE_rowContraction θ A v)
    · simp only [R, map_sub, coeff_sub, scaleHom_monomial_monomial, hab,
        coeff_monomial_same, hv, sub_self]
  · simpa only [R, sub_sub_cancel] using rowContraction_mem θ A v

theorem rowIdeal_low_degree_zero (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    {P : K[X][X]} (hP : P ∈ rowIdeal (pencilBase θ A))
    (hd : TotalDegreeLE P (k-1)) : P = 0 := by
  obtain ⟨v,hv⟩ := exists_constant_row_multiplier θ hθ A P hP
    (hd.outer.trans (by omega))
    (hd.scaled.trans (by omega))
  change P = rowContraction θ A v at hv
  have ht : slopeTrace θ v = 0 := by
    rw [← rowContraction_top θ A v, ← hv]
    exact coeff_eq_zero_of_natDegree_lt
      (hd.scaled.trans_lt (by omega))
  have hv0 := diagonal_zero_of_trace_slope θ hθ (Matrix.diagonal v) ht
  have he : v = 0 := funext fun i => by simpa using hv0 i
  rw [hv, he]
  change rowPair (pencilBase θ A) (fun i => C ((0 : Fin (k+1) → K) i)) = 0
  convert rowPair_zero (pencilBase θ A) using 1
  congr 1
  funext i
  exact map_zero C

theorem row_quotient_spanned
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
      (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
        (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1)))) = ⊤ := by
  classical
  let I := rowIdeal (pencilBase θ A)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap
  let W := Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
    f (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))))
  have hmon : ∀ d a b : ℕ, a+b = d → ∀ c : K, f (monomial a (monomial b c)) ∈ W := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b hab c
      have hscalar : monomial a (monomial b c) = c • monomial a (monomial b (1 : K)) := by
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [hscalar, map_smul]
      apply W.smul_mem
      by_cases hd : d < k
      · let i : PlaneIndex (k-1) := ⟨(⟨a, by omega⟩, ⟨a+b+1, by omega⟩), by
          change a < a+b+1
          omega⟩
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        change f (monomial a (monomial (a+b+1-a-1) (1 : K))) = _
        rw [show a+b+1-a-1 = b by omega]
      · let α := min a k
        let β := k-α
        have hα : α ≤ a := Nat.min_le_left _ _
        have hβ : β ≤ b := by dsimp [β, α]; omega
        have hsum : α+β = k := by dsimp [β, α]; omega
        obtain ⟨R, hR, hmem⟩ := exists_lower_row_representative θ hθ A hk α β hsum
        let Q : K[X][X] := monomial (a-α) (monomial (b-β) 1)
        have heq : f (monomial a (monomial b 1)) = f (Q*R) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          have hh := I.mul_mem_left Q hmem
          convert hh using 1
          rw [mul_sub]
          congr 1
          simp only [Q, monomial_mul_monomial, one_mul]
          rw [Nat.sub_add_cancel hα, Nat.sub_add_cancel hβ]
        rw [heq]
        apply map_mem_of_monomials f W (Q*R)
        intro u v huv
        have hde : TotalDegreeLE (Q*R) ((a-α)+(b-β)+(k-1)) :=
          (totalDegreeLE_monomial (a-α) (b-β) (1 : K)).mul hR
        have hle : u+v ≤ (a-α)+(b-β)+(k-1) := by
          by_contra hn
          exact huv (hde u v (by omega))
        exact ih (u+v) (by omega) u v rfl _
  apply top_unique
  intro x _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply map_mem_of_monomials f W P
  intro a b _
  exact hmon (a+b) a b rfl _

theorem finite_row_quotient
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Module.Finite K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) := by
  classical
  let g := fun i : PlaneIndex (k-1) =>
    (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
      (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))
  have hg := row_quotient_spanned θ hθ A hk
  change Submodule.span K (Set.range g) = ⊤ at hg
  exact Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨Set.range g, Set.finite_range g, hg⟩)

theorem row_quotient_finrank (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Module.finrank K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) = (k+1).choose 2 := by
  classical
  let I := rowIdeal (pencilBase θ A)
  let f : (PlaneIndex (k-1) → K) →ₗ[K] (K[X][X] ⧸ I) :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (planeMap (k-1))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hmem : planeMap (k-1) v ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hv
    have hz := rowIdeal_low_degree_zero θ hθ A hk hmem (totalDegreeLE_planeMap (k-1) v)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  have := finite_row_quotient θ hθ A hk
  apply le_antisymm
  · have h := finrank_le_of_span_eq_top (row_quotient_spanned θ hθ A hk)
    simpa only [card_planeIndex, show k-1+2 = k+1 by omega] using h
  · have h := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_fintype_fun_eq_card, card_planeIndex] at h
    simpa only [show k-1+2 = k+1 by omega] using h
end RowLength
end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowRecovery
variable {K : Type*} [Field K] {k : ℕ}

theorem rowContraction_single (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    rowContraction θ A (Pi.single i 1) = rowEntry (pencilBase θ A) i := by
  classical
  simp [rowContraction, rowPair_eq_sum, Pi.single_apply]

theorem rowEntry_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    (scaleHom (rowEntry (pencilBase θ A) i)).coeff k =
      slopeTrace θ (Pi.single i 1) := by
  rw [← rowContraction_single, rowContraction_top]

theorem rowEntry_eq_of_rowIdeal_eq (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (hI : rowIdeal (pencilBase θ A) = rowIdeal (pencilBase θ B)) :
    rowEntry (pencilBase θ A) = rowEntry (pencilBase θ B) := by
  funext i
  apply sub_eq_zero.mp
  apply rowIdeal_low_degree_zero θ hθ A hk
  · apply Ideal.sub_mem
    · exact Ideal.subset_span ⟨i,rfl⟩
    · rw [hI]
      exact Ideal.subset_span ⟨i,rfl⟩
  · apply TotalDegreeLE.pred_of_top_zero hk
    · exact (totalDegreeLE_rowEntry θ A i).sub (totalDegreeLE_rowEntry θ B i)
    · rw [map_sub, coeff_sub, rowEntry_top, rowEntry_top, sub_self]

theorem rowContraction_eq_zero_iff (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    rowContraction θ A v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have ht : slopeTrace θ v = 0 := by rw [← rowContraction_top θ A v, h, map_zero, coeff_zero]
    have hv := diagonal_zero_of_trace_slope θ hθ (Matrix.diagonal v) ht
    funext i
    simpa using hv i
  · rintro rfl
    unfold rowContraction
    have h : (fun i => C ((0 : Fin (k+1) → K) i)) = (0 : Fin (k+1) → K[X]) := by
      funext i
      exact map_zero C
    rw [h, rowPair_zero]

theorem rowPair_sub {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (v w : ι → R) :
    rowPair A (v-w) = rowPair A v - rowPair A w := by
  simp only [rowPair_eq_sum, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem rowPair_neg {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (v : ι → R) : rowPair A (-v) = -rowPair A v := by
  simp only [rowPair_eq_sum, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem matrix_eq_of_rowIdeal_eq (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (hI : rowIdeal (pencilBase θ A) = rowIdeal (pencilBase θ B))
    (hF : (pencilMatrix (pencilBase θ A)).det = (pencilMatrix (pencilBase θ B)).det) :
    A = B := by
  classical
  have hE := rowEntry_eq_of_rowIdeal_eq θ hθ A B hk hI
  have hpair (v : Fin (k+1) → K[X]) :
      rowPair (pencilBase θ A) v = rowPair (pencilBase θ B) v := by
    simp only [rowPair_eq_sum, hE]
  have hz (j : Fin (k+1)) : rowContraction θ A (fun i => A i j - B i j) = 0 := by
    let v : Fin (k+1) → K[X] := Pi.single j 1
    have ha := X_mul_rowPair (pencilBase θ A) v
    have hb := X_mul_rowPair (pencilBase θ B) v
    rw [hpair v, hF, hb, rowPair_neg, rowPair_neg, ← hpair] at ha
    have hr : rowPair (pencilBase θ A) ((pencilBase θ A).mulVec v) =
        rowPair (pencilBase θ A) ((pencilBase θ B).mulVec v) := by
      linear_combination ha
    have hh := sub_eq_zero.mpr hr
    rw [← rowPair_sub] at hh
    convert hh using 1
    unfold rowContraction
    congr 1
    funext i
    simp [v, pencilBase,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, sub_eq_add_neg]
    ring
  ext i j
  exact sub_eq_zero.mp (congrFun ((rowContraction_eq_zero_iff θ hθ A _).mp (hz j)) i)
end RowRecovery
end PermanentBorder.AdjugateAlgebra

end OAI
