import OAI.Probability.SignedSweeps.TransposeSpecht

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma span_monomial_evaluations {I S : Type*} [Fintype I]
    (v : I → S →₀ ℕ) (hv : Function.Injective v) :
    Submodule.span ℂ (Set.range (fun x : S → ℂ =>
      fun i => (v i).prod (fun s k => x s ^ k))) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.mpr h)
  let b := Pi.basisFun ℂ I
  let P : MvPolynomial S ℂ := ∑ i, MvPolynomial.monomial (v i) (f (b i))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_zero, P, map_sum, MvPolynomial.eval_monomial]
    have hx := hker (Submodule.subset_span
      (Set.mem_range_self x : (fun i => (v i).prod (fun s k => x s ^ k)) ∈ _))
    change f (fun i => (v i).prod (fun s k => x s ^ k)) = 0 at hx
    rw [← b.sum_repr (fun i => (v i).prod (fun s k => x s ^ k))] at hx
    simpa only [map_sum, map_smul, b, Pi.basisFun_repr, smul_eq_mul, mul_comm] using hx
  have hz (i : I) : f (b i) = 0 := by
    have hc := congrArg (fun polynomial : MvPolynomial S ℂ => polynomial.coeff (v i)) hP
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv.eq_iff] using hc
  apply hf
  apply b.ext
  exact fun i => hz i

def wordHistogram {p : ℕ} {C : Type*} (w : Fin p → C) : C →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

lemma wordHistogram_apply {p : ℕ} {C : Type*} (w : Fin p → C) (c : C) :
    wordHistogram w c = Fintype.card {i // w i = c} := by
  simp [wordHistogram, Finsupp.single_apply, Fintype.card_subtype, eq_comm]

lemma wordHistogram_le {p : ℕ} {C : Type*} (w : Fin p → C) (c : C) :
    wordHistogram w c ≤ p := by
  rw [wordHistogram_apply]
  exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin p)

lemma wordHistogram_relabel {p : ℕ} {C : Type*} (w : Fin p → C)
    (g : SymmetricGroup p) : wordHistogram (w ∘ g) = wordHistogram w :=
  Equiv.sum_comp g (fun i => Finsupp.single (w i) 1)

lemma wordHistogram_eq_orbit {p : ℕ} {C : Type*} (w z : Fin p → C)
    (h : wordHistogram w = wordHistogram z) :
    ∃ g : SymmetricGroup p, ∀ i, z (g i) = w i := by
  have hc (c : C) : Fintype.card {i // w i = c} = Fintype.card {i // z i = c} := by
    simpa only [wordHistogram_apply] using congrArg (fun a => a c) h
  let e (c : C) : {i // w i = c} ≃ {i // z i = c} := Fintype.equivOfCardEq (hc c)
  let g : SymmetricGroup p := (Equiv.sigmaFiberEquiv w).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv z))
  exact ⟨g, fun i => (e (w i) ⟨i, rfl⟩).property⟩

lemma wordHistogram_monomial_eval {p : ℕ} {C : Type*} (w : Fin p → C) (x : C → ℂ) :
    (wordHistogram w).prod (fun c k => x c ^ k) = ∏ i, x (w i) := by
  rw [wordHistogram, ← Finsupp.prod_finsetSum_index]
  · simp
  · intro c; simp
  · intro c a b; exact pow_add _ _ _

def wordPairHistogram {p : ℕ} {C : Type*} (x y : Fin p → C) : (C × C) →₀ ℕ :=
  wordHistogram (fun i => (x i, y i))

abbrev WordOrbit (p : ℕ) (C : Type*) :=
  {v : (C × C) →₀ ℕ // ∃ x y : Fin p → C, v = wordPairHistogram x y}

instance wordOrbitFinite {p : ℕ} {C : Type*} [Finite C] : Finite (WordOrbit p C) := by
  let f : (Fin p → C) × (Fin p → C) → WordOrbit p C :=
    fun z => ⟨wordPairHistogram z.1 z.2, ⟨z.1, z.2, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨v, x, y, rfl⟩
  exact ⟨(x,y), rfl⟩

instance wordOrbitFintype {p : ℕ} {C : Type*} [Finite C] : Fintype (WordOrbit p C) :=
  Fintype.ofFinite _

lemma card_wordOrbit_le {p : ℕ} {C : Type*} [Fintype C] :
    Fintype.card (WordOrbit p C) ≤ (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  let f : WordOrbit p C → (C × C → Fin (p + 1)) := fun v c =>
    ⟨v.1 c, by obtain ⟨x,y,hxy⟩ := v.2; rw [hxy]; exact Nat.lt_succ_of_le (wordHistogram_le _ _)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    exact Finsupp.ext (fun c => congrArg Fin.val (congrFun he c))
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_le_of_injective f hf

def wordPositionEquiv {p : ℕ} {C : Type*} (g : SymmetricGroup p) :
    Equiv.Perm (Fin p → C) where
  toFun w := w ∘ g.symm
  invFun w := w ∘ g
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp

@[simp] lemma wordPositionEquiv_apply {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C) (i : Fin p) : wordPositionEquiv g w i = w (g⁻¹ i) := rfl

def wordPositionMatrix {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    Matrix (Fin p → C) (Fin p → C) ℂ :=
  Equiv.Perm.permMatrix ℂ (wordPositionEquiv (C := C) g)⁻¹

def wordTensorMatrix (p : ℕ) {C : Type*} (A : Matrix C C ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ := fun x y => ∏ i, A (x i) (y i)

lemma wordTensorMatrix_mul {p : ℕ} {C : Type*} [Fintype C]
    (A B : Matrix C C ℂ) :
    wordTensorMatrix p (A * B) = wordTensorMatrix p A * wordTensorMatrix p B := by
  ext x y
  simp only [wordTensorMatrix, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

lemma wordTensorMatrix_one {p : ℕ} {C : Type*} [Fintype C] :
    wordTensorMatrix p (1 : Matrix C C ℂ) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y; simp [wordTensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [Matrix.one_apply, ite_eq_right h, wordTensorMatrix]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma wordTensorMatrix_star {p : ℕ} {C : Type*} (A : Matrix C C ℂ) :
    wordTensorMatrix p A.conjTranspose = (wordTensorMatrix p A).conjTranspose := by
  ext x y
  simp only [wordTensorMatrix, Matrix.conjTranspose_apply, star_prod]

def wordCommutant (p : ℕ) (C : Type*) [Fintype C] :
    Submodule ℂ (Matrix (Fin p → C) (Fin p → C) ℂ) where
  carrier := {A | ∀ g : SymmetricGroup p, A * wordPositionMatrix g = wordPositionMatrix g * A}
  zero_mem' := by simp
  add_mem' := by intro A B hA hB g; simp only [Matrix.add_mul, Matrix.mul_add, hA g, hB g]
  smul_mem' := by intro c A hA g; simp only [Matrix.smul_mul, Matrix.mul_smul, hA g]

lemma mem_wordCommutant_iff {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) :
    A ∈ wordCommutant p C ↔ ∀ g : SymmetricGroup p, ∀ x y,
      A (x ∘ g) (y ∘ g) = A x y := by
  change (∀ g : SymmetricGroup p, _) ↔ _
  simp only [wordPositionMatrix, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  constructor
  · intro h g x y
    have hh := congrArg (fun M : Matrix (Fin p → C) (Fin p → C) ℂ => M x (y ∘ g)) (h g)
    change A x ((y ∘ g) ∘ g.symm) = A (x ∘ g) (y ∘ g) at hh
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Equiv.symm_comp_self, Function.comp_id] using hh.symm
  · intro h g
    ext x y
    change A x (y ∘ g.symm) = A (x ∘ g) y
    have hh := h g x (y ∘ g.symm)
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Equiv.symm_comp_self, Function.comp_id] using hh.symm

lemma wordCommutant_histogram_constant {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C)
    {x y z w : Fin p → C} (h : wordPairHistogram x y = wordPairHistogram z w) :
    A x y = A z w := by
  obtain ⟨g, hg⟩ := wordHistogram_eq_orbit (fun i => (x i, y i)) (fun i => (z i, w i)) h
  have hx : z ∘ g = x := funext (fun i => congrArg Prod.fst (hg i))
  have hy : w ∘ g = y := funext (fun i => congrArg Prod.snd (hg i))
  simpa only [hx, hy] using (mem_wordCommutant_iff A).mp hA g z w

def wordOrbitMatrix {p : ℕ} {C : Type*} [Fintype C] :
    (WordOrbit p C → ℂ) →ₗ[ℂ] Matrix (Fin p → C) (Fin p → C) ℂ where
  toFun f x y := f ⟨wordPairHistogram x y, ⟨x, y, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma range_wordOrbitMatrix {p : ℕ} {C : Type*} [Fintype C] :
    (wordOrbitMatrix (p := p) (C := C)).range = wordCommutant p C := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [mem_wordCommutant_iff]
    intro g x y
    change f _ = f _
    congr 1
    apply Subtype.ext
    exact wordHistogram_relabel (fun i => (x i, y i)) g
  · intro A hA
    let f : WordOrbit p C → ℂ := fun v =>
      A (Classical.choose v.2) (Classical.choose (Classical.choose_spec v.2))
    refine ⟨f, ?_⟩
    ext x y
    let v : WordOrbit p C := ⟨wordPairHistogram x y, ⟨x, y, rfl⟩⟩
    apply wordCommutant_histogram_constant A hA
    exact (Classical.choose_spec (Classical.choose_spec v.2)).symm

theorem span_wordTensorMatrix {p : ℕ} {C : Type*} [Fintype C] :
    Submodule.span ℂ (Set.range (wordTensorMatrix p (C := C))) = wordCommutant p C := by
  let v : WordOrbit p C → (C × C) →₀ ℕ := Subtype.val
  have h := congrArg (Submodule.map (wordOrbitMatrix (p := p) (C := C)))
    (span_monomial_evaluations v Subtype.val_injective)
  rw [Submodule.map_span, ← LinearMap.range_eq_map, range_wordOrbitMatrix] at h
  rw [← h]
  congr 1
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨_, ⟨(fun c => B c.1 c.2), rfl⟩, ?_⟩
    ext x y
    exact wordHistogram_monomial_eval (fun i => (x i, y i)) (fun c => B c.1 c.2)
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fun c e => z (c, e)), ?_⟩
    ext x y
    exact (wordHistogram_monomial_eval (fun i => (x i, y i)) z).symm

theorem wordCommutant_finrank_le {p : ℕ} {C : Type*} [Fintype C] :
    finrank ℂ (wordCommutant p C) ≤ (p + 1) ^ (Fintype.card C * Fintype.card C) := by
  rw [← range_wordOrbitMatrix]
  exact (LinearMap.finrank_range_le _).trans (by simpa using (card_wordOrbit_le (p := p) (C := C)))

end SignedSweeps
end

end OAI
