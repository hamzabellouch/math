import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramPrimeSquareFilter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramSinglePrime

namespace OAI

/-! Exact prime-free/single-prime splitting of the finite denominator
set after the stationary-phase square-factor exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaGramDenominators_iff (ε δ : ℝ) (c : Eisenstein) :
    c∈cubicThetaGramDenominators ε δ ↔ norm c≤1/(ε*δ) ∧ (3:Eisenstein)∣c ∧ c≠0 := by
  unfold cubicThetaGramDenominators
  rw [Finset.mem_filter,(finite_norm_le _).mem_toFinset]
  rfl

lemma cubicThetaGramDenominators_mul_prime {p : Eisenstein} (hp : primaryPrime p)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (d : Eisenstein) :
    d∈cubicThetaGramDenominators ε (δ*norm p) ↔ p*d∈cubicThetaGramDenominators ε δ := by
  have hpN := norm_pos_of_ne_zero hp.2.ne_zero
  have h3p : IsCoprime (3:Eisenstein) p :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
  have hscale : 1/(ε*(δ*norm p))=(1/(ε*δ))/norm p := by
    field_simp
  have hn : norm d≤1/(ε*(δ*norm p)) ↔ norm (p*d)≤1/(ε*δ) := by
    rw [hscale,le_div_iff₀ hpN,norm_mul_eq]
    rw [mul_comm (norm d)]
  have hd : (3:Eisenstein)∣p*d ↔ (3:Eisenstein)∣d :=
    ⟨h3p.dvd_of_dvd_mul_left,fun hd => dvd_mul_of_dvd_right hd p⟩
  have hz : p*d≠0 ↔ d≠0 := by simp only [ne_eq,mul_eq_zero,hp.2.ne_zero,false_or]
  rw [cubicThetaGramDenominators_iff,cubicThetaGramDenominators_iff,hn,hd,hz]

lemma cubicThetaGramDenominators_single_prime_sum {p : Eisenstein} (hp : primaryPrime p)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (F : Eisenstein → ℂ) :
    (∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => p∣c ∧ ¬p^2∣c),F c)=
      ∑ d∈(cubicThetaGramDenominators ε (δ*norm p)).filter (fun d => ¬p∣d),F (p*d) := by
  symm
  apply Finset.sum_bij (fun d _ => p*d)
  · intro d hd
    obtain ⟨hd,hpd⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    refine ⟨(cubicThetaGramDenominators_mul_prime hp hε hδ d).mp hd,dvd_mul_right p d,?_⟩
    simpa only [pow_two,mul_dvd_mul_iff_left hp.2.ne_zero] using hpd
  · intro d₁ _ d₂ _ he
    exact mul_left_cancel₀ hp.2.ne_zero he
  · intro c hc
    obtain ⟨hc,hpc,hppc⟩ := Finset.mem_filter.mp hc
    obtain ⟨d,rfl⟩ := hpc
    refine ⟨d,Finset.mem_filter.mpr ⟨(cubicThetaGramDenominators_mul_prime hp hε hδ d).mpr hc,?_⟩,rfl⟩
    simpa only [pow_two,mul_dvd_mul_iff_left hp.2.ne_zero] using hppc
  · intro d _
    rfl

theorem cubicThetaGramDenominators_prime_split {p : Eisenstein} (hp : primaryPrime p)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (F : Eisenstein → ℂ) :
    (∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p^2∣c),F c)=
      (∑ c∈(cubicThetaGramDenominators ε δ).filter (fun c => ¬p∣c),F c)+
      ∑ d∈(cubicThetaGramDenominators ε (δ*norm p)).filter (fun d => ¬p∣d),F (p*d) := by
  rw [←cubicThetaGramDenominators_single_prime_sum hp hε hδ F,
    Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hpc : p∣c
  · by_cases hppc : p^2∣c <;> simp [hpc,hppc]
  · have hppc : ¬p^2∣c := fun hd => hpc (dvd_trans (dvd_pow_self p (by decide : 2≠0)) hd)
    simp [hpc,hppc]

end CubicFirstMoment

end

end OAI
