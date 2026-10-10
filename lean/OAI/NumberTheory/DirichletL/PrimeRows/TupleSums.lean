import OAI.NumberTheory.DirichletL.PrimeRows.SlotSums

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_bound (K : ℕ) (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : (∀i, T i),‖∏i,
        W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
          (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
          (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏i,(Y i)^r := by
  let d : ℝ := eps/((K:ℝ)+1)
  have hd : 0<d := div_pos heps (by positivity)
  obtain ⟨C,hC,hmain⟩ := continued_selected_slot_bound d a b r B hd ha hb hr hB
  refine ⟨C^K,pow_pos hC K,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 1≤N := by
    dsimp [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hdK : d*(K:ℝ)≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)]
    nlinarith
  have hpow : (N^d)^K≤N^eps := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤N)]
    exact Real.rpow_le_rpow_of_exponent_le hN hdK
  let F : ∀i:Fin K,T i→ℂ := fun i P=>
    W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u P.val (hT i P.val P.property).1 x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  change (∑P:(∀i,T i),‖∏i,F i (P i)‖)≤C^K*N^eps*∏i,(Y i)^r
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i P=>‖F i P‖)]
  calc
    _ ≤ ∏i:Fin K, (C*N^d*(Y i)^r) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.sum_nonneg fun _ _=>norm_nonneg _
      · intro i _; exact hmain η u (T i) (hT i) (Y i) (hY i) (W i) (hWS i) (hWB i) x w z hx hw hz
    _ = C^K*(N^d)^K*∏i:Fin K,(Y i)^r := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ C^K*N^eps*∏i:Fin K,(Y i)^r := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _)

end SevenEighths.ProbeHighRowFamily
end

end OAI
