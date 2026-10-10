import OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit
import OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem central_regular_slot_sum (eps c d B : ℝ) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (480:ℝ)≤P.val.absNorm ∧ IsCoprime P.val η.modulus)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc c d →
      (∀y,‖W y‖≤B) → ∀(a e : ℝ) (x w z : ℂ),
      (51/100:ℝ)≤a → a≤1 → 0<e → e≤1/1000 →
      x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      (∀P∈T,198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∑P:T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralRegularError η u P.val (hT P.val P.property).1 x w z‖)≤
      C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    eps c d (-(4/25:ℝ)) 1 B 1440 heps hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB a e x w z ha ha1 he he1 hx hw hz hsmall
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := fun P Q h=>Subtype.ext (Subtype.ext h)
  let E : T→ℂ := fun P=>centralRegularError η u P.val (hT P.val P.property).1 x w z
  let G : T→ℂ := fun P=>((f P).absNorm:ℂ)^(1/2:ℂ)*E P
  have hnorm (P : T) : ‖G P‖≤1440*(if f P∣Ideal.span {u.val} then ((f P).absNorm:ℝ)^(1:ℝ) else 1) := by
    have hQ : (480:ℝ)≤(f P).absNorm := (hT P.val P.property).2.1
    have hQ0 : (0:ℝ)<(f P).absNorm := by linarith
    have hQ1 : (1:ℝ)≤(f P).absNorm := by linarith
    have hb := (central_actual_local_bounds η u P.val (hT P.val P.property).1
      (hT P.val P.property).2.2 a e x w z hQ (hsmall P.val P.property) ha ha1 he he1 hx hw hz).2.1
    have hn : ‖((f P).absNorm:ℂ)^(1/2:ℂ)‖=((f P).absNorm:ℝ)^(1/2:ℝ) := by
      rw [show ((f P).absNorm:ℂ)=(((f P).absNorm:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0];norm_num
    dsimp only [G]
    rw [norm_mul,hn]
    calc
      _ ≤ ((f P).absNorm:ℝ)^(1/2:ℝ)*(1440*(if f P∣Ideal.span {u.val} then
          ((f P).absNorm:ℝ)^(1/2:ℝ) else ((f P).absNorm:ℝ)^(-(51/100:ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ0.le _)
      _ ≤ _ := by
        by_cases hp : f P∣Ideal.span {u.val}
        · simp only [ite_eq_left hp]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          norm_num
        · simp only [ite_eq_right hp,mul_one]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          have hh : ((f P).absNorm:ℝ)^((1/2:ℝ)-(51/100:ℝ))≤1 := by
            exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (1/2:ℝ)-51/100≤0)).trans_eq (Real.rpow_zero _)
          norm_num only [show (1/2:ℝ)+-(51/100:ℝ)=(1/2:ℝ)-(51/100:ℝ) by ring]
          nlinarith
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G (fun P _=>hnorm P)
    (z-1/2) (by simp only [Complex.sub_re];rw [hz];norm_num)
  have heq (P : T) :
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^((z-1/2)-1)*G P=
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^(z-1)*E P := by
    have hn : ((f P).absNorm:ℂ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _) ,←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simpa only [heq] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI
