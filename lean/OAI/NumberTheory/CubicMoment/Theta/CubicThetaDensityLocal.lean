import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTotientSeries

namespace OAI

/-! The local prime factor of the actual normalized residue-unit density. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaIdealDensity_product (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity ν=
      ∏ p ∈ ν.support, (1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹) := by
  have he : (cubicThetaIdealTotient ν:ℝ)/idealExponentNorm ν=
      ∏ p ∈ ν.support, (1-1/(normNat (idealPrimeRepresentative p):ℝ)) := by
    rw [cubicThetaIdealTotient_euler,mul_div_cancel_left₀ _ (idealExponentNorm_pos ν).ne']
  simpa only [cubicThetaIdealDensity,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,one_div,
    Complex.ofReal_inv] using congrArg Complex.ofReal he

lemma cubicThetaIdealDensity_prime_step (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    cubicThetaIdealDensity (Finsupp.single p 1+ν)=
      if ν p=0 then (1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*cubicThetaIdealDensity ν
      else cubicThetaIdealDensity ν := by
  have hs : (Finsupp.single p 1+ν).support=insert p ν.support := by
    ext q
    by_cases hq : q=p
    · subst q
      simp [Finsupp.mem_support_iff]
    · simp [Finsupp.mem_support_iff,hq]
  rw [cubicThetaIdealDensity_product,hs]
  by_cases hp : ν p=0
  · rw [ite_eq_left hp,Finset.prod_insert (Finsupp.notMem_support_iff.mpr hp),
      cubicThetaIdealDensity_product]
  · rw [ite_eq_right hp,Finset.insert_eq_of_mem (Finsupp.mem_support_iff.mpr hp),
      cubicThetaIdealDensity_product]

def cubicThetaPrimeDensity (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) : ℂ :=
  if 0<ν p then cubicThetaIdealDensity ν else 0

lemma cubicThetaPrimeDensity_norm (p : EisensteinIdealPrime) (ν : EisensteinIdealExponent) :
    ‖cubicThetaPrimeDensity p ν‖≤1 := by
  unfold cubicThetaPrimeDensity
  split_ifs
  · exact cubicThetaIdealDensity_norm ν
  · simp

lemma cubicThetaPrimeDensity_series_equation (p : EisensteinIdealPrime)
    {s : ℂ} (hs : 1<s.re) :
    normDirichletSeries (cubicThetaPrimeDensity p) idealExponentNorm s =
      (normNat (idealPrimeRepresentative p):ℂ)^(-s)*
        ((1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*
          normDirichletSeries cubicThetaIdealDensity idealExponentNorm s+
          (normNat (idealPrimeRepresentative p):ℂ)⁻¹*
            normDirichletSeries (cubicThetaPrimeDensity p) idealExponentNorm s) := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := cubicThetaIdealDensity ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := cubicThetaPrimeDensity p ν*(idealExponentNorm ν:ℂ)^(-s)
  have hf : Summable f := (idealDirichlet_norm_summable _ cubicThetaIdealDensity_norm hs).of_norm
  have hg : Summable g := (idealDirichlet_norm_summable _ (cubicThetaPrimeDensity_norm p) hs).of_norm
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
    intro ν hν
    have hp : 0<ν p := by
      by_contra h
      exact hν (by simp [g,cubicThetaPrimeDensity,h])
    exact ⟨ν-δ,add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr hp))⟩
  have hpoint (ν : EisensteinIdealExponent) :
      g (δ+ν)=(normNat (idealPrimeRepresentative p):ℂ)^(-s)*
        ((1-(normNat (idealPrimeRepresentative p):ℂ)⁻¹)*f ν+
          (normNat (idealPrimeRepresentative p):ℂ)⁻¹*g ν) := by
    have hpos : 0<(δ+ν) p := by simp [δ]
    dsimp only [g,f]
    rw [cubicThetaPrimeDensity,ite_eq_left hpos,idealExponentNorm_add,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (idealExponentNorm_pos δ).le
        (idealExponentNorm_pos ν).le]
    have hδ : idealExponentNorm δ=(normNat (idealPrimeRepresentative p):ℝ) := by
      simp [δ,idealExponentNorm_single]
    rw [hδ,cubicThetaIdealDensity_prime_step]
    by_cases hp : ν p=0
    · simp only [hp,ite_true,cubicThetaPrimeDensity,lt_self_iff_false,ite_false]
      push_cast
      ring
    · rw [ite_eq_right hp,cubicThetaPrimeDensity,ite_eq_left (Nat.pos_of_ne_zero hp)]
      push_cast
      ring
  change (∑' ν, g ν)=_
  rw [←hi.tsum_eq hsup]
  simp_rw [hpoint]
  rw [tsum_mul_left, (hf.mul_left _).tsum_add (hg.mul_left _),tsum_mul_left,tsum_mul_left]
  rfl

end CubicFirstMoment

end

end OAI
