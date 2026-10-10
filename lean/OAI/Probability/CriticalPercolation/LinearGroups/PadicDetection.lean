import Mathlib

namespace OAI

section
noncomputable section
open Set Function Cardinal Polynomial
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma rat_exists_prime_norm_gt_one (q : ℚ) (hq : q.den≠1) :
    ∃ p : ℕ, p.Prime ∧ 1<padicNorm p q := by
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hq
  let : Fact p.Prime := ⟨hp⟩
  have hpn : ¬p∣q.num.natAbs := by
    intro hd
    have hh := Nat.dvd_gcd hd hpd
    rw [q.reduced] at hh
    exact hp.not_dvd_one hh
  have hnum : padicNorm p (q.num:ℚ)=1 :=
    (padicNorm.int_eq_one_iff _).mpr (by simpa only [Int.natCast_dvd] using hpn)
  have hden : padicNorm p (q.den:ℚ)<1 := (padicNorm.nat_lt_one_iff _).mpr hpd
  have hpos : 0<padicNorm p (q.den:ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm
    (padicNorm.nonzero (by exact_mod_cast q.den_nz)))
  refine ⟨p,hp,?_⟩
  conv_rhs => rw [←Rat.num_div_den q]
  rw [padicNorm.div,hnum]
  exact (one_lt_div hpos).mpr (by simpa only [one_mul] using hden)

lemma rat_integer_of_all_padic_norm_le_one (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → padicNorm p q≤1) : ∃ z : ℤ, (z:ℚ)=q := by
  have hd : q.den=1 := by
    by_contra hn
    obtain ⟨p,hp,hpq⟩ := rat_exists_prime_norm_gt_one q hn
    exact hpq.not_ge (h p hp)
  exact ⟨q.num,by simpa only [hd,Nat.cast_one,div_one] using (Rat.num_div_den q)⟩

lemma coeff_norm_le_one_of_roots {F : Type*} [NormedField F]
    (hna : IsNonarchimedean (norm : F → ℝ)) (P : F[X]) (hm : P.Monic) (hs : P.Splits)
    (hr : ∀ z∈P.roots, ‖z‖≤1) (i : ℕ) : ‖P.coeff i‖≤1 := by
  let R : Subring F := {
    carrier := {z | ‖z‖≤1}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := fun hx hy => (hna _ _).trans (max_le hx hy)
    mul_mem' := fun hx hy => by
      change ‖_ * _‖≤1
      rw [norm_mul]
      exact (mul_le_mul hx hy (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    neg_mem' := fun hx => by simpa only [Set.mem_ofPred_eq,norm_neg] using hx }
  have hP := hs.mem_lift_of_roots_mem_range hm R.subtype (fun z hz => ⟨⟨z,hr z hz⟩,rfl⟩)
  obtain ⟨Q,hQ⟩ := hP
  change Q.map R.subtype=P at hQ
  rw [←hQ,coeff_map]
  exact (Q.coeff i).property

lemma integral_of_all_padic_embeddings {A : Type} [Field A] [NumberField A] (x : A)
    (h : ∀ (p : ℕ) (_ : Fact p.Prime) (f : A →+* AlgebraicClosure (Padic p)),
      spectralNorm (Padic p) (AlgebraicClosure (Padic p)) (f x)≤1) : IsIntegral ℤ x := by
  have hcoeff : ∀ i, ∃ z : ℤ, (z:ℚ)=(minpoly ℚ x).coeff i := by
    intro i
    apply rat_integer_of_all_padic_norm_le_one
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    let F := AlgebraicClosure (Padic p)
    let : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField (Padic p) F
    let : NormedAlgebra (Padic p) F := spectralNorm.normedAlgebra (Padic p) F
    have hh : ‖((minpoly ℚ x).map (algebraMap ℚ F)).coeff i‖≤1 := by
      apply coeff_norm_le_one_of_roots (isNonarchimedean_spectralNorm (K:=Padic p) (L:=F))
        _ ((minpoly.monic (Algebra.IsSeparable.isIntegral ℚ x)).map _) (IsAlgClosed.splits _)
      intro z hz
      have hroot : z∈(minpoly ℚ x).rootSet F := by
        exact Multiset.mem_toFinset.mpr hz
      obtain ⟨f,hf⟩ := (NumberField.Embeddings.range_eval_eq_rootSet_minpoly A F x).symm.subset hroot
      rw [←hf]
      exact h p inferInstance f
    have he : ‖algebraMap ℚ F ((minpoly ℚ x).coeff i)‖ =
        (padicNorm p ((minpoly ℚ x).coeff i):ℝ) := by
      rw [IsScalarTower.algebraMap_apply ℚ (Padic p) F,norm_algebraMap']
      exact Padic.eq_padicNorm _
    rw [coeff_map,he] at hh
    exact_mod_cast hh
  have hl : minpoly ℚ x ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    exact hcoeff i
  obtain ⟨P,hP⟩ := hl
  change P.map (Int.castRingHom ℚ)=minpoly ℚ x at hP
  refine ⟨P,?_,?_⟩
  · apply Polynomial.monic_of_injective (f:=Int.castRingHom ℚ) (Int.cast_injective (α:=ℚ))
    simpa only [hP] using minpoly.monic (Algebra.IsSeparable.isIntegral ℚ x)
  · change Polynomial.aeval x P=0
    rw [←Polynomial.aeval_map_algebraMap ℚ]
    change Polynomial.aeval x (P.map (Int.castRingHom ℚ))=0
    rw [hP]
    exact minpoly.aeval ℚ x

end CriticalPercolation.Arithmetic
end
end

end OAI
