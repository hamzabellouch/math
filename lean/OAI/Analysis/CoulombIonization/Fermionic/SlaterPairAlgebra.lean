import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterBody

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

lemma permutations_eq_or_swap_of_agree_except_two {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (j k : Fin n)
    (h : ∀ i, i ≠ j → i ≠ k → σ i = τ i) :
    τ = σ ∨ τ = σ * Equiv.swap j k := by
  classical
  by_cases hj : σ j = τ j
  · left
    exact (permutations_eq_of_agree_except σ τ k (fun i hik => by
      by_cases hij : i=j
      · simpa only [hij] using hj
      · exact h i hij hik)).symm
  · right
    have hk : σ k = τ j := by
      obtain ⟨i,hi⟩ := σ.surjective (τ j)
      by_cases hij : i=j
      · exact (hj (hij ▸ hi)).elim
      by_cases hik : i=k
      · exact hik ▸ hi
      have hit : τ i = τ j := (h i hij hik).symm.trans hi
      exact (hij (τ.injective hit)).elim
    apply (permutations_eq_of_agree_except (σ * Equiv.swap j k) τ k ?_).symm
    intro i hik
    by_cases hij : i=j
    · subst i
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hk
    · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik] using h i hij hik

abbrev SlaterPairRest {n : ℕ} (j k : Fin n) := {i : Fin n // i ≠ j ∧ i ≠ k}

def slaterRestTensor {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) (x : SlaterPairRest j k → α) : ℂ :=
  ∏ i : SlaterPairRest j k, φ (σ i) (x i)

def slaterPairAmplitude {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) (u v : α) : ℂ :=
  φ (σ j) u * φ (σ k) v

def slaterPairSliceRaw {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ)
    (j k : Fin n) (u v : α) (x : SlaterPairRest j k → α) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((σ.sign : ℤ) : ℂ) *
    slaterPairAmplitude φ j k σ u v * slaterRestTensor φ j k σ x

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma memLp_slaterRestTensor {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (j k : Fin n) (σ : Equiv.Perm (Fin n)) :
    MemLp (slaterRestTensor φ j k σ) 2 (Measure.pi fun _ : SlaterPairRest j k => μ) := by
  have hm : AEStronglyMeasurable (slaterRestTensor φ j k σ)
      (Measure.pi fun _ : SlaterPairRest j k => μ) := by
    unfold slaterRestTensor
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hφ (σ i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : SlaterPairRest j k => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [slaterRestTensor, norm_prod, Finset.prod_pow] using
    Integrable.fintype_prod (fun i : SlaterPairRest j k => (hφ (σ i)).norm.integrable_sq)

lemma slaterRestTensor_inner (φ : Fin n → α → ℂ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (j k : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterRestTensor φ j k σ x) * slaterRestTensor φ j k τ x
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) =
      if τ=σ ∨ τ=σ * Equiv.swap j k then 1 else 0 := by
  classical
  simp only [slaterRestTensor, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : SlaterPairRest j k => μ)
    (fun (i : SlaterPairRest j k) t => conj (φ (σ i) t) * φ (τ i) t)]
  simp_rw [ho]
  split_ifs with he
  · apply Finset.prod_eq_one
    intro i _
    apply ite_eq_left
    rcases he with rfl | rfl
    · rfl
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne i.2.1 i.2.2]
  · have hh : ∃ i, i ≠ j ∧ i ≠ k ∧ σ i ≠ τ i := by
      by_contra! hh
      exact he (permutations_eq_or_swap_of_agree_except_two σ τ j k hh)
    obtain ⟨i,hij,hik,hi⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hij,hik⟩ : SlaterPairRest j k))
    exact ite_eq_right hi

lemma perm_mul_swap_ne_self {n : ℕ} (σ : Equiv.Perm (Fin n)) {j k : Fin n} (hjk : j ≠ k) :
    σ * Equiv.swap j k ≠ σ := by
  intro h
  have he := congrArg (fun τ : Equiv.Perm (Fin n) => τ j) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he
  exact hjk (σ.injective he).symm

lemma complex_sign_mul_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) {j k : Fin n} (hjk : j ≠ k) :
    ((((σ * Equiv.swap j k).sign : ℤ) : ℂ)) = -((σ.sign : ℤ) : ℂ) := by
  simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hjk]

lemma slaterPairSliceRaw_norm_sq_integral {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    {j k : Fin n} (hjk : j ≠ k) (u v : α) :
    (Complex.ofReal (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ))) =
      ∑ σ : Equiv.Perm (Fin n),
        (conj (slaterPairAmplitude φ j k σ u v) * slaterPairAmplitude φ j k σ u v -
        conj (slaterPairAmplitude φ j k σ u v) *
          slaterPairAmplitude φ j k (σ * Equiv.swap j k) u v) := by
  classical
  rw [show slaterPairSliceRaw φ j k u v = fun x => ∑ σ : Equiv.Perm (Fin n),
    ((σ.sign : ℤ) : ℂ) * slaterPairAmplitude φ j k σ u v *
      slaterRestTensor φ j k σ x from rfl,
    integral_norm_sq_weighted_sum _ _ (memLp_slaterRestTensor hφ j k)]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [slaterRestTensor_inner φ ho j k]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)]
  rw [ite_eq_left (show σ=σ ∨ σ=σ * Equiv.swap j k from Or.inl rfl), mul_one]
  simp only [map_mul, map_intCast]
  have hne := perm_mul_swap_ne_self σ hjk
  rw [Finset.sum_eq_single (σ * Equiv.swap j k)]
  · rw [ite_eq_left (Or.inr rfl), mul_one, complex_sign_mul_swap σ hjk]
    have hs := complex_sign_sq σ
    ring_nf at hs ⊢
    simp only [hs, one_mul]
  · intro τ ht htne
    have htσ : τ ≠ σ := (Finset.mem_erase.mp ht).1
    rw [ite_eq_right (not_or.mpr ⟨htσ,htne⟩), mul_zero]
  · intro ht
    apply (ht ?_).elim
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩

end Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

def slaterPairIndex {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Fin 2 ≃ {i : Fin n // i=j ∨ i=k} where
  toFun a := if a=0 then ⟨j,Or.inl rfl⟩ else ⟨k,Or.inr rfl⟩
  invFun i := if i.1=j then 0 else 1
  left_inv a := by
    fin_cases a <;> simp [Ne.symm hjk]
  right_inv i := by
    rcases i with ⟨i,hi|hi⟩
    · subst i; simp
    · subst i; simp [Ne.symm hjk]

def slaterRestIndex {n : ℕ} (j k : Fin n) :
    SlaterPairRest j k ≃ {i : Fin n // ¬ (i=j ∨ i=k)} where
  toFun i := ⟨i,not_or.mpr i.2⟩
  invFun i := ⟨i,(not_or.mp i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

def slaterPairSplit {j k : Fin n} (hjk : j ≠ k) :
    (Fin n → α) ≃ᵐ (α × α) × (SlaterPairRest j k → α) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α) (fun i => i=j ∨ i=k)).trans
    ((MeasurableEquiv.prodCongr
      ((MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i=j ∨ i=k} => α)
        (slaterPairIndex hjk)).symm.trans (MeasurableEquiv.piFinTwo (fun _ => α)))
      (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // ¬(i=j ∨ i=k)} => α)
        (slaterRestIndex j k)).symm))

lemma slaterPairSplit_preserving {j k : Fin n} (hjk : j ≠ k) :
    MeasurePreserving (slaterPairSplit (α := α) hjk)
      (Measure.pi fun _ : Fin n => μ)
      ((μ.prod μ).prod (Measure.pi fun _ : SlaterPairRest j k => μ)) := by
  apply (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ)
    (fun i => i=j ∨ i=k)).trans
  exact ((measurePreserving_piCongrLeft (fun _ : {i : Fin n // i=j ∨ i=k} => μ)
    (slaterPairIndex hjk)).symm.trans (measurePreserving_piFinTwo (fun _ => μ))).prod
    (measurePreserving_piCongrLeft (fun _ : {i : Fin n // ¬(i=j ∨ i=k)} => μ)
      (slaterRestIndex j k)).symm

lemma slaterPairSplit_apply {j k : Fin n} (hjk : j ≠ k) (x : Fin n → α) :
    slaterPairSplit hjk x = ((x j,x k),fun i : SlaterPairRest j k => x i) := by
  rfl

lemma slaterPairSplit_symm_apply_left {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    (slaterPairSplit hjk).symm ((u,v),y) j = u := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.1.1)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

lemma slaterPairSplit_symm_apply_right {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) :
    (slaterPairSplit hjk).symm ((u,v),y) k = v := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.1.2)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

lemma slaterPairSplit_symm_apply_rest {j k : Fin n} (hjk : j ≠ k)
    (u v : α) (y : SlaterPairRest j k → α) (i : SlaterPairRest j k) :
    (slaterPairSplit hjk).symm ((u,v),y) i = y i := by
  have h := congrArg (fun z : (α×α) × (SlaterPairRest j k → α) => z.2 i)
    ((slaterPairSplit hjk).apply_symm_apply ((u,v),y))
  simpa only [slaterPairSplit_apply] using h

end CoulombAtom

end

end OAI
