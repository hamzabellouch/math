import Mathlib

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

def SupportBound (ρ : σ → ℝ) (N : ℝ) (p : MvPolynomial σ E) : Prop :=
  ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N

theorem SupportBound.mono {ρ : σ → ℝ} {M N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hMN : M ≤ N) : SupportBound ρ N p :=
  fun d hd => (hp d hd).trans hMN

theorem supportBound_zero (ρ : σ → ℝ) (N : ℝ) :
    SupportBound ρ N (0 : MvPolynomial σ E) := by
  intro d hd
  simp at hd

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem supportBound_X (ρ : σ → ℝ) (i : σ) :
    SupportBound ρ (ρ i) (MvPolynomial.X i : MvPolynomial σ E) := by
  classical
  intro d hd
  have he : d = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

theorem SupportBound.pow {ρ : σ → ℝ} {N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (m : ℕ) : SupportBound ρ ((m : ℝ) * N) (p ^ m) := by
  induction m with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem supportBound_prod {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : α → ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ (N i) (p i)) :
    SupportBound ρ (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_sum {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ N (p i)) :
    SupportBound ρ N (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supportBound_zero ρ N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_aeval_monomial (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (d : ι →₀ ℕ) (c : C) :
    SupportBound κ (Finsupp.weight ρ d) (MvPolynomial.aeval g (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hC : SupportBound κ 0 (algebraMap C (MvPolynomial σ E) c) :=
    supportBound_C κ (algebraMap C E c)
  have hprod := supportBound_prod d.support κ (fun i => g i ^ d i)
    (fun i => (d i : ℝ) * ρ i) (fun i _ => (hg i).pow (d i))
  have h := hC.mul hprod
  simpa only [zero_add, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finsupp.prod] using h

theorem supportBound_aeval (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound κ N (MvPolynomial.aeval g p) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum p, map_sum]
  exact supportBound_sum p.support κ _ N
    (fun d hd => (supportBound_aeval_monomial ρ κ g hg d (p.coeff d)).mono (hp d hd))

noncomputable def sliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial A E := by
  classical
  exact MvPolynomial.aeval (fun i => if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i))

@[simp] theorem sliceMap_X_mem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∈ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_X_notMem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∉ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.C (b i) := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_C (A : Finset ι) (b : ι → E) (c : C) :
    sliceMap A b (MvPolynomial.C c) = MvPolynomial.C (algebraMap C E c) := by
  classical
  simp [sliceMap]

theorem sliceMap_eval (A : Finset ι) (b : ι → E) :
    ((MvPolynomial.aeval (fun i : A => b i)).restrictScalars C).comp (sliceMap A b) =
      MvPolynomial.aeval b := by
  classical
  ext i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, MvPolynomial.aeval_X]
  by_cases hi : i ∈ A
  · simp [sliceMap_X_mem A b i hi]
  · simp [sliceMap_X_notMem A b i hi]

theorem supportBound_sliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun i : A => ρ i) N (sliceMap A b p) := by
  classical
  let g : ι → MvPolynomial A E := fun i =>
    if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i)
  change SupportBound (fun i : A => ρ i) N (MvPolynomial.aeval g p)
  have hg : ∀ i, SupportBound (fun j : A => ρ j) (ρ i) (g i) := by
    intro i
    dsimp only [g]
    split_ifs with hi
    · exact supportBound_X (E := E) (fun j : A => ρ j) ⟨i, hi⟩
    · exact (supportBound_C (fun j : A => ρ j) (b i)).mono (hρ i)
  exact supportBound_aeval ρ (fun i : A => ρ i) g hg N p hp

theorem supportBound_sliceMap_sum (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ∀ d ∈ (sliceMap A b p).support,
      (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N := by
  have h := supportBound_sliceMap A b ρ hρ N p (by
    simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hp)
  simpa only [SupportBound, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using h

theorem supportBound_renameEquiv (e : ι ≃ σ) (ρ : ι → ℝ) (N : ℝ)
    (p : MvPolynomial ι E) (hp : SupportBound ρ N p) :
    SupportBound (fun j => ρ (e.symm j)) N (MvPolynomial.rename e p) := by
  rw [MvPolynomial.rename_eq_aeval]
  apply supportBound_aeval (C := E) ρ (fun j => ρ (e.symm j)) (MvPolynomial.X ∘ e) _ N p hp
  intro i
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    supportBound_X (E := E) (fun j => ρ (e.symm j)) (e i)

noncomputable def enumeratedSliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial (Fin A.card) E :=
  ((MvPolynomial.rename (R := E) A.equivFin).restrictScalars C).comp (sliceMap A b)

theorem supportBound_enumeratedSliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun j : Fin A.card => ρ (A.equivFin.symm j)) N
      (enumeratedSliceMap A b p) :=
  supportBound_renameEquiv A.equivFin (fun i : A => ρ i) N (sliceMap A b p)
    (supportBound_sliceMap A b ρ hρ N p hp)

theorem supportBound_enumeratedSliceMap_sum (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ∀ d ∈ (enumeratedSliceMap A b p).support,
      (∑ j ∈ d.support, (d j : ℝ) * ρ (A.equivFin.symm j)) ≤ N := by
  have h := supportBound_enumeratedSliceMap A b ρ hρ N p (by
    simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hp)
  simpa only [SupportBound, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using h

theorem enumeratedSliceMap_eval (A : Finset ι) (b : ι → E) :
    ((MvPolynomial.aeval (fun j : Fin A.card => b (A.equivFin.symm j))).restrictScalars C).comp
      (enumeratedSliceMap A b) = MvPolynomial.aeval b := by
  apply AlgHom.ext
  intro p
  change MvPolynomial.aeval (fun j : Fin A.card => b (A.equivFin.symm j))
    (MvPolynomial.rename A.equivFin (sliceMap A b p)) = MvPolynomial.aeval b p
  rw [MvPolynomial.aeval_rename]
  have he : (fun j : Fin A.card => b (A.equivFin.symm j)) ∘ A.equivFin =
      (fun i : A => b i) := by
    funext i
    simp
  rw [he]
  exact AlgHom.congr_fun (sliceMap_eval (C := C) A b) p

end PiExponent.WeightedSliceDegree

end OAI
