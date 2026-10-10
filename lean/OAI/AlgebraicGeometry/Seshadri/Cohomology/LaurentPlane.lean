import Mathlib

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

abbrev Ring (K : Type*) [CommRing K] := AddMonoidAlgebra K (ℤ × ℤ)

def T {K : Type*} [CommRing K] (z : ℤ × ℤ) : Ring K :=
  AddMonoidAlgebra.single z 1

@[simp] lemma T_zero {K : Type*} [CommRing K] : T (K := K) 0 = 1 := rfl
lemma T_add {K : Type*} [CommRing K] (a b : ℤ × ℤ) :
    T (K := K) (a+b) = T a * T b := by
  simp [T, AddMonoidAlgebra.single_mul_single]

section Evaluation
variable {K R : Type*} [CommRing K] [CommRing R]

def monomials (u v : Rˣ) : Multiplicative (ℤ × ℤ) →* R where
  toFun z := ↑(u ^ z.toAdd.1 * v ^ z.toAdd.2)
  map_one' := by simp
  map_mul' z w := by
    change ↑(u ^ (z.toAdd.1 + w.toAdd.1) * v ^ (z.toAdd.2 + w.toAdd.2)) =
      (↑(u ^ z.toAdd.1 * v ^ z.toAdd.2) : R) * ↑(u ^ w.toAdd.1 * v ^ w.toAdd.2)
    simp only [zpow_add, Units.val_mul]
    ring

def eval (k : K →+* R) (u v : Rˣ) : Ring K →+* R :=
  AddMonoidAlgebra.liftNCRingHom k (monomials u v) (fun _ _ => .all _ _)

@[simp] lemma eval_T (k : K →+* R) (u v : Rˣ) (z : ℤ × ℤ) :
    eval k u v (T z) = ↑(u ^ z.1 * v ^ z.2) := by
  simp [eval, T, monomials, AddMonoidAlgebra.liftNCRingHom_single]

@[simp] lemma eval_algebraMap (k : K →+* R) (u v : Rˣ) (a : K) :
    eval k u v (algebraMap K (Ring K) a) = k a := by
  change eval k u v (AddMonoidAlgebra.single 0 a) = k a
  simp [eval, monomials, AddMonoidAlgebra.liftNCRingHom_single]

end Evaluation

theorem finite_of_clearing {P R N M : Type*} [CommRing P] [CommRing R]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (e : P →+* R) (f : N →+ M)
    (hf : ∀ p n, f (p • n) = e p • f n)
    (hclear : ∀ m : M, ∃ r : R, ∃ n : N, m = r • f n) : Module.Finite R M := by
  classical
  obtain ⟨d,s,hs⟩ := Module.Finite.exists_fin (R := P) (M := N)
  let V := Submodule.span R (Set.range (fun i => f (s i)))
  have image (n : N) : f n ∈ V := by
    have hn : n ∈ Submodule.span P (Set.range s) := hs ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨i,rfl⟩ := hn
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add n m hn hm ih ih' => simpa only [map_add] using V.add_mem ih ih'
    | smul p n hn ih => rw [hf]; exact V.smul_mem (e p) ih
  have hV : V = ⊤ := by
    apply top_unique
    intro m hm
    obtain ⟨r,n,rfl⟩ := hclear m
    exact V.smul_mem r (image n)
  exact Module.Finite.of_fg_top (hV ▸ Submodule.fg_span (Set.finite_range _))

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

theorem quotient_finite [Module.Finite (Ring K) M]
    (A B C : Submodule K M)
    (hA : ∀ z : ℤ × ℤ, 0 ≤ z.2 → ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z : ℤ × ℤ, 0 ≤ z.1 → ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z : ℤ × ℤ, z.1 + z.2 ≤ 0 → ∀ x ∈ C, T (K := K) z • x ∈ C)
    (locA : ∀ x : M, ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, T (K := K) ((n : ℤ),0) • x ∈ B)
    (locC : ∀ x : M, ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • x ∈ C) :
    Module.Finite K (M ⧸ ((A ⊔ B) ⊔ C)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := Ring K) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  choose c hc using fun i : Fin n => locC (s i)
  let Q := (A ⊔ B) ⊔ C
  let q := Q.mkQ
  let J := (i : Fin n) ×
    (↥(Finset.Icc (-(c i : ℤ) - a i) (b i : ℤ)) ×
     ↥(Finset.Icc (-(c i : ℤ) - b i) (a i : ℤ)))
  let g : J → M ⧸ Q := fun v => q (T (K := K) (v.2.1.val, v.2.2.val) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ × ℤ) : q (T (K := K) z • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z.2
    · have he : z = (z.1, z.2 - a i) + (0, (a i : ℤ)) := by ext <;> simp
      have hm : T (K := K) z • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact hA _ (by dsimp; omega) _ (ha i)
      have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
        ((show A ≤ Q from le_sup_of_le_left le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : (b i : ℤ) ≤ z.1
      · have he : z = (z.1 - b i, z.2) + ((b i : ℤ), 0) := by ext <;> simp
        have hm : T (K := K) z • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact hB _ (by dsimp; omega) _ (hb i)
        have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
          ((show B ≤ Q from le_sup_of_le_left le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · by_cases hzC : z.1 + z.2 ≤ -(c i : ℤ)
        · have he : z = (z.1, z.2 + c i) + (0, -(c i : ℤ)) := by ext <;> simp
          have hm : T (K := K) z • s i ∈ C := by
            rw [he, T_add, mul_smul]
            exact hC _ (by dsimp; omega) _ (hc i)
          have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
            ((show C ≤ Q from le_sup_right) hm)
          rw [hq]; exact W.zero_mem
        · exact Submodule.subset_span
            ⟨⟨i, ⟨⟨z.1, Finset.mem_Icc.mpr (by omega)⟩,
                   ⟨z.2, Finset.mem_Icc.mpr (by omega)⟩⟩⟩, rfl⟩
  have scalar_monomial (i : Fin n) (p : Ring K) : q (p • s i) ∈ W := by
    induction p using AddMonoidAlgebra.induction_on with
    | of z => exact monomial i z
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | smul d p hp =>
      rw [smul_assoc, map_smul]
      exact W.smul_mem d hp
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m, rfl⟩ := Q.mkQ_surjective x
    have hm : m ∈ Submodule.span (Ring K) (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : Ring K, q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentPlane

end


end OAI
