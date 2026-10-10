import OAI.NumberTheory.DirichletL.Moments.OriginalRadialTail
import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
open HeckeFamily ConcreteTraceCRT CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialTail CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

lemma retained_conductor (η:Character) (Z m q xi Ck K:ℝ) (hZ:0<Z) (hCk:0≤Ck)
    (hη:(η.modulus.absNorm:ℝ)≤Z^m) (hK:K≤Ck*Z^q)
    (z:O) (hz:z≠0) (hrow:‖eisEmbedding z‖^2≤K*Z^xi) :
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*Ck*Z^(m+q+xi) := by
  have hn:((Ideal.span {z}).absNorm:ℝ)≤Ck*Z^(q+xi) := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    apply hrow.trans
    have hh:=mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hZ.le xi)
    simpa only [Real.rpow_add hZ,mul_assoc] using hh
  have hh:=(naturalRow η z hz).modulus_power_bound Z m (q+xi) Ck hZ hCk hη hn
  simpa only [add_assoc] using hh

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

theorem actual_tail_arbitrary_saving (xi saving mass : ℝ) (hxi:0<xi) :
    ∃order:ℕ,∀(F:O→ℂ)(B:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Z:ℝ),
      (∀z,‖F z‖≤B) → 0<K → 1≤Z → B^2*max 1 K≤Z^mass →
      radialEnergy F (fun z=>keep z ∧ K*Z^xi<‖eisEmbedding z‖^2) Φ K≤
        (4*(1+Real.pi)^2*tailControl order Φ)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=exists_nat_ge ((mass+saving)/xi)
  have ho:mass-xi*(order:ℝ)≤-saving := by
    have hh:mass+saving≤(order:ℝ)*xi:=(div_le_iff₀ hxi).mp horder
    linarith
  refine ⟨order,?_⟩
  intro F B keep Φ K Z hF hK hZ hmass
  have hz:0<Z:=by linarith
  have hh:=actual_radial_tail order F B hF keep Φ K (K*Z^xi) hK (by positivity)
  have hdiv:K*Z^xi/K=Z^xi:=by field_simp
  rw [hdiv] at hh
  have hc:0≤4*(1+Real.pi)^2*tailControl order Φ:=by unfold tailControl;positivity
  have hb:(B^2*max 1 K)*((1+Z^xi)^order)⁻¹≤Z^(-saving) := by
    calc
      _≤Z^mass*Z^(-xi*(order:ℝ)) :=
        mul_le_mul hmass (reciprocal_cutoff_bound Z xi order hz) (by positivity) (Real.rpow_nonneg hz.le _)
      _=Z^(mass-xi*(order:ℝ)) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^(-saving):=Real.rpow_le_rpow_of_exponent_le hZ ho
  apply hh.trans
  convert mul_le_mul_of_nonneg_left hb hc using 1 ; ring

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI
