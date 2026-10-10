import Mathlib

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.LaurentTails
noncomputable section
open LaurentPolynomial
open scoped LaurentPolynomial
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module K[T;T⁻¹] M]

lemma positive_tail (A : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, T_add, mul_smul]
      using hA _ ih

lemma negative_tail (B : Submodule K M)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B) {x : M} (hx : x ∈ B) :
    ∀ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    simpa only [he, T_add, mul_smul] using hB _ ih

variable [IsScalarTower K K[T;T⁻¹] M]

theorem quotient_finite [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B)
    (locA : ∀ x : M, ∃ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B) :
    Module.Finite K (M ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[T;T⁻¹]) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  let q := (A ⊔ B).mkQ
  let J := (i : Fin n) × ↥(Finset.Icc (-(b i : ℤ)) (a i : ℤ))
  let g : J → M ⧸ (A ⊔ B) := fun v => q ((T v.2.val : K[T;T⁻¹]) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ) : q ((T z : K[T;T⁻¹]) • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z
    · have he : z = ((z - a i).toNat : ℤ) + a i := by omega
      have hm : (T z : K[T;T⁻¹]) • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact positive_tail A hA (ha i) _
      have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
        (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show A ≤ A ⊔ B from le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : z ≤ -(b i : ℤ)
      · have he : z = -((-(b i : ℤ) - z).toNat : ℤ) + -(b i : ℤ) := by omega
        have hm : (T z : K[T;T⁻¹]) • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact negative_tail B hB (hb i) _
        have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
          (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show B ≤ A ⊔ B from le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · exact Submodule.subset_span ⟨⟨i,⟨z,Finset.mem_Icc.mpr (by omega)⟩⟩,rfl⟩
  have scalar_monomial (i : Fin n) (p : K[T;T⁻¹]) : q (p • s i) ∈ W := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | C_mul_T z c =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul]
      exact W.smul_mem c (monomial i z)
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m,rfl⟩ := (A ⊔ B).mkQ_surjective x
    have hm : m ∈ Submodule.span K[T;T⁻¹] (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : K[T;T⁻¹], q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro scalar; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentTails
end


end
end

end OAI
