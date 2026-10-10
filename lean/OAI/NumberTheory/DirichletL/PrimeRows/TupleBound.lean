import OAI.NumberTheory.DirichletL.PrimeRows.TupleSums
import OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_with_correction (K : ℕ) (δ a b r B : ℝ)
    (hδ : 0<δ) (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (T : Fin K→Finset PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      1+eps≤x.re+w.re →
      (∑P : (∀i,T i),‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
        (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
            (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*∏i,(Y i)^r := by
  obtain ⟨C₁,hC₁,hmain⟩ := continued_selected_tuple_bound K (δ/2) a b r B (by linarith) ha hb hr hB
  obtain ⟨C₂,hC₂,hcorr⟩ := unselectedCorrection_first_subpower (δ/2) (by linarith)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  intro eps S hS hfirst η u T hT Y hY W hWS hWB x w z hx hw hz hxw
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  let F : (∀i,T i)→ℂ := fun P=>∏i,
    W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  calc
    _ ≤ ∑P:(∀i,T i),(C₂*N^(δ/2))*‖F P‖ := by
      apply Finset.sum_le_sum
      intro P _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hcorr eps S hS hfirst (Finset.univ.image (fun i=>(P i).val)) η u x w z
          (by linarith) (by linarith) (by rw [hz];exact hr) hxw) (norm_nonneg _)
    _ = (C₂*N^(δ/2))*∑P:(∀i,T i),‖F P‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C₂*N^(δ/2))*(C₁*N^(δ/2)*∏i,(Y i)^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmain η u T hT Y hY W hWS hWB x w z hx hw hz
    _ = (C₂*C₁)*N^δ*∏i,(Y i)^r := by
      have hp : N^(δ/2)*N^(δ/2)=N^δ := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (C₂*C₁)*(N^(δ/2)*N^(δ/2))*∏i,(Y i)^r := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
