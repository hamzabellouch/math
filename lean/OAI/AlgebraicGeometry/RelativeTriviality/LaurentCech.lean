import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open scoped LaurentPolynomial
open LaurentPolynomial
universe u v
variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R[T;T⁻¹] M]
variable [Module R M]

lemma positive_shift_mem (P : Submodule R M)
    (hp : ∀ x ∈ P, T (R := R) 1 • x ∈ P)
    {x : M} (hx : x ∈ P) (k : ℤ) (hk : 0 ≤ k) : T (R := R) k • x ∈ P := by
  have step : ∀ n : ℕ, T (R := R) (n : ℤ) • x ∈ P := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_comm, T_add, mul_smul]
      exact hp _ ih
  simpa [Int.toNat_of_nonneg hk] using step k.toNat

lemma negative_shift_mem (Q : Submodule R M)
    (hq : ∀ x ∈ Q, T (R := R) (-1) • x ∈ Q)
    {x : M} (hx : x ∈ Q) (k : ℤ) (hk : k ≤ 0) : T (R := R) k • x ∈ Q := by
  have step : ∀ n : ℕ, T (R := R) (-(n : ℤ)) • x ∈ Q := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, neg_add, add_comm, T_add, mul_smul]
      exact hq _ ih
  have he : k = - ((-k).toNat : ℤ) := by omega
  rw [he]
  exact step _

variable [IsScalarTower R R[T;T⁻¹] M]

lemma eventual_negative_chart (Q : Submodule R M)
    (hq : ∀ x ∈ Q, T (R := R) (-1) • x ∈ Q)
    (hQ : Submodule.span R[T;T⁻¹] (Q : Set M) = ⊤) (x : M) :
    ∃ N : ℤ, ∀ k : ℤ, k ≤ N → T (R := R) k • x ∈ Q := by
  have hx : x ∈ Submodule.span R[T;T⁻¹] (Q : Set M) := by rw [hQ]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun k hk ↦ negative_shift_mem R M Q hq hx k hk⟩
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨N, hN⟩ := ihx
      obtain ⟨L, hL⟩ := ihy
      exact ⟨min N L, fun k hk ↦ by
        rw [smul_add]
        exact Q.add_mem (hN k (hk.trans (min_le_left _ _)))
          (hL k (hk.trans (min_le_right _ _)))⟩
  | smul a x hx ih =>
      obtain ⟨N, hN⟩ := ih
      induction a using LaurentPolynomial.induction_on' with
      | add a b iha ihb =>
          obtain ⟨A, hA⟩ := iha
          obtain ⟨B, hB⟩ := ihb
          refine ⟨min A B, fun k hk ↦ ?_⟩
          rw [add_smul, smul_add]
          exact Q.add_mem (hA k (hk.trans (min_le_left _ _)))
            (hB k (hk.trans (min_le_right _ _)))
      | C_mul_T n r =>
          refine ⟨N - n, fun k hk ↦ ?_⟩
          have he : T (R := R) k • ((C r * T n) • x) = r • (T (R := R) (k+n) • x) := by
            rw [← mul_smul, mul_left_comm, mul_smul, ← T_add, C_eq_algebraMap,
              IsScalarTower.algebraMap_smul]
          rw [he]
          exact Q.smul_mem r (hN (k+n) (by omega))

theorem finite_cech_cokernel [Module.Finite R[T;T⁻¹] M]
    (P Q : Submodule R M)
    (hp : ∀ x ∈ P, T (R := R) 1 • x ∈ P)
    (hq : ∀ x ∈ Q, T (R := R) (-1) • x ∈ Q)
    (hP : Submodule.span R[T;T⁻¹] (P : Set M) = ⊤)
    (hQ : Submodule.span R[T;T⁻¹] (Q : Set M) = ⊤) :
    Module.Finite R (M ⧸ (P ⊔ Q)) := by
  classical
  have hfg : (Submodule.span R[T;T⁻¹] (P : Set M)).FG := by
    rw [hP]; exact Module.Finite.fg_top
  obtain ⟨s, hsP, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hstop : Submodule.span R[T;T⁻¹] (s : Set M) = ⊤ := hs.symm.trans hP
  choose N hN using eventual_negative_chart R M Q hq hQ
  let q := (P ⊔ Q).mkQ
  let fs : Finset (M ⧸ (P ⊔ Q)) := s.biUnion fun x ↦
    (Finset.Icc (min (N x) 0) 0).image fun k ↦ q (T (R := R) k • x)
  let B : Submodule R (M ⧸ (P ⊔ Q)) := Submodule.span R (fs : Set _)
  have hmon : ∀ x ∈ s, ∀ k : ℤ, q (T (R := R) k • x) ∈ B := by
    intro x hx k
    by_cases hk0 : 0 ≤ k
    · have hmem : T (R := R) k • x ∈ P ⊔ Q :=
        (show P ≤ P ⊔ Q from le_sup_left) (positive_shift_mem R M P hp (hsP hx) k hk0)
      have hz : q (T (R := R) k • x) = 0 := (Submodule.Quotient.mk_eq_zero (P ⊔ Q)).mpr hmem
      rw [hz]; exact B.zero_mem
    · by_cases hkN : k ≤ N x
      · have hz : q (T (R := R) k • x) = 0 :=
          (Submodule.Quotient.mk_eq_zero (P ⊔ Q)).mpr ((show Q ≤ P ⊔ Q from le_sup_right) (hN x k hkN))
        rw [hz]; exact B.zero_mem
      · apply Submodule.subset_span
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hx, Finset.mem_image.mpr ⟨k, ?_, rfl⟩⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hgen : ∀ x ∈ s, ∀ a : R[T;T⁻¹], q (a • x) ∈ B := by
    intro x hx a
    induction a using LaurentPolynomial.induction_on' with
    | add a b ha hb => simpa [add_smul] using B.add_mem ha hb
    | C_mul_T n r =>
        have he : (C r * T n) • x = r • (T (R := R) n • x) := by
          rw [mul_smul, C_eq_algebraMap, IsScalarTower.algebraMap_smul]
        rw [he, map_smul]
        exact B.smul_mem r (hmon x hx n)
  have hall : ∀ x : M, ∀ a : R[T;T⁻¹], q (a • x) ∈ B := by
    intro x
    have hx : x ∈ Submodule.span R[T;T⁻¹] (s : Set M) := by rw [hstop]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => intro a; simp
    | add x y hx hy ihx ihy =>
        intro a
        simpa [smul_add] using B.add_mem (ihx a) (ihy a)
    | smul a x hx ih =>
        intro b
        simpa [mul_smul] using ih (b*a)
  have hB : B = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨x, rfl⟩ := (P ⊔ Q).mkQ_surjective z
    simpa [q] using hall x 1
  refine ⟨?_⟩
  rw [← hB]
  exact Submodule.fg_span fs.finite_toSet
end

open scoped TensorProduct
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (P Q M : Type u) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup M]
  [Module R P] [Module R Q] [Module R M]
  (P' Q' M' : Type u) [AddCommGroup P'] [AddCommGroup Q'] [AddCommGroup M']
  [Module R P'] [Module R Q'] [Module R M']
  [Module S P'] [Module S Q'] [Module S M']
  [IsScalarTower R S P'] [IsScalarTower R S Q'] [IsScalarTower R S M']
  (a : P →ₗ[R] M) (b : Q →ₗ[R] M) (a' : P' →ₗ[S] M') (b' : Q' →ₗ[S] M')
  (p : P →ₗ[R] P') (q : Q →ₗ[R] Q') (m : M →ₗ[R] M')

theorem tensor_cech_vanish (hp : IsBaseChange S p) (hq : IsBaseChange S q)
    (hm : IsBaseChange S m)
    (ha : ∀ x, m (a x) = a' (p x)) (hb : ∀ x, m (b x) = b' (q x))
    (hspan : LinearMap.range a' ⊔ LinearMap.range b' = ⊤) :
    Subsingleton (S ⊗[R] (M ⧸ (LinearMap.range a ⊔ LinearMap.range b))) := by
  let N := M ⧸ (LinearMap.range a ⊔ LinearMap.range b)
  let π : M →ₗ[R] N := (LinearMap.range a ⊔ LinearMap.range b).mkQ
  let g : M →ₗ[R] (S ⊗[R] N) := (TensorProduct.mk R S N 1).comp π
  let l : M' →ₗ[S] (S ⊗[R] N) := hm.lift g
  have hl (x : M) : l (m x) = g x := hm.lift_eq g x
  have hpa (x : P) : g (a x) = 0 := by
    change 1 ⊗ₜ[R] π (a x) = 0
    have h : a x ∈ LinearMap.range a ⊔ LinearMap.range b :=
      Submodule.mem_sup_left (show a x ∈ LinearMap.range a from ⟨x,rfl⟩)
    have he : π (a x) = 0 := Submodule.Quotient.mk_eq_zero _ |>.mpr h
    rw [he, TensorProduct.tmul_zero]
  have hqb (x : Q) : g (b x) = 0 := by
    change 1 ⊗ₜ[R] π (b x) = 0
    have h : b x ∈ LinearMap.range a ⊔ LinearMap.range b :=
      Submodule.mem_sup_right (show b x ∈ LinearMap.range b from ⟨x,rfl⟩)
    have he : π (b x) = 0 := Submodule.Quotient.mk_eq_zero _ |>.mpr h
    rw [he, TensorProduct.tmul_zero]
  have ha0 (x : P') : l (a' x) = 0 := by
    induction x using hp.inductionOn with
    | tmul x => rw [← ha, hl, hpa]
    | smul s x hx => rw [map_smul, map_smul, hx, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hb0 (x : Q') : l (b' x) = 0 := by
    induction x using hq.inductionOn with
    | tmul x => rw [← hb, hl, hqb]
    | smul s x hx => rw [map_smul, map_smul, hx, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hall (x : M') : l x = 0 := by
    have hx : x ∈ LinearMap.range a' ⊔ LinearMap.range b' := by rw [hspan]; trivial
    obtain ⟨y,⟨u,rfl⟩,z,⟨v,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add,ha0,hb0,add_zero]
  have hzero (x : S ⊗[R] N) : x = 0 := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [hx,hy,add_zero]
    | tmul s x =>
      obtain ⟨y,rfl⟩ := (LinearMap.range a ⊔ LinearMap.range b).mkQ_surjective x
      have hg : (1 : S) ⊗ₜ[R] π y = 0 := (hl y).symm.trans (hall (m y))
      have he : s ⊗ₜ[R] π y = s • ((1 : S) ⊗ₜ[R] π y) := by simp [TensorProduct.smul_tmul']
      rw [he,hg,smul_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩
end CampanaPeternellSix.RelativeCech

end

end OAI
