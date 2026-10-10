import OAI.Probability.InvariantIsing.Magnetic.MagneticInwardApproximation
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariationalContinuity

namespace OAI

/-! The rational supremum also dominates every real interior profile.
Approximation toward zero only increases its constrained entropy. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma finiteMagneticFunctional_real_profile {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ b mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a| < 1) :
    (∑ a, γ a*b a*mag a)+
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal := by
  classical
  let R := finiteR ρ eig hρ hsum
  let V := fun s => (magneticVariationalFunctional R γ s).toReal
  let F := (finiteMagneticFunctional R γ b).toReal
  let C := ∑ a, γ a* |b a|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => mul_nonneg (hγ a) (abs_nonneg _))
  have hv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).le)
  have hr := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hr.1 hr.2
  by_contra hnot
  let gap := (∑ a, γ a*b a*mag a)+V mag-F
  have hgap : 0 < gap := sub_pos.mpr (lt_of_not_ge hnot)
  let δ := gap/(2*(C+1))
  have hδ : 0 < δ := div_pos hgap (by positivity)
  choose q hqabs hq hclose using fun a => exists_inward_rat_close (hmag a) hδ
  let qm : RationalMagnetization A := ⟨q,hq⟩
  have hqv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
    (fun a => (q a : ℝ)) hγ hγsum (fun a => (hq a).le)
  have hmono := magneticVariational_inward_mono R γ (fun a => (q a : ℝ)) mag hγ hmag hqabs
  rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_toReal hqv.1 hqv.2] at hmono
  have hV : V mag ≤ V (fun a => (q a : ℝ)) := EReal.coe_le_coe_iff.mp hmono
  have hsup := le_iSup (fun t : RationalMagnetization A =>
    ((∑ a, γ a*b a*(t.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional R γ (fun a => (t.val a : ℝ))) qm
  change ((∑ a, γ a*b a*(q a : ℝ) : ℝ) : EReal)+
    magneticVariationalFunctional R γ (fun a => (q a : ℝ)) ≤ finiteMagneticFunctional R γ b at hsup
  rw [← EReal.coe_toReal hqv.1 hqv.2,← EReal.coe_add,← EReal.coe_toReal hf.1 hf.2] at hsup
  have hsup' : (∑ a, γ a*b a*(q a : ℝ))+V (fun a => (q a : ℝ)) ≤ F :=
    EReal.coe_le_coe_iff.mp hsup
  have hdiff : (∑ a, γ a*b a*mag a)-(∑ a, γ a*b a*(q a : ℝ)) ≤ C*δ := by
    rw [← Finset.sum_sub_distrib,show C*δ=∑ a, γ a* |b a| * δ by rw [Finset.sum_mul]]
    apply Finset.sum_le_sum
    intro a _
    calc
      _ = γ a*b a*(mag a-(q a : ℝ)) := by ring
      _ ≤ |γ a*b a*(mag a-(q a : ℝ))| := le_abs_self _
      _ = γ a* |b a| * |mag a-(q a : ℝ)| := by rw [abs_mul,abs_mul,abs_of_nonneg (hγ a)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hclose a).le (mul_nonneg (hγ a) (abs_nonneg _))
  have hδeq : δ*(2*(C+1))=gap := div_mul_cancel₀ _ (by positivity)
  have hsmall : C*δ<gap := by nlinarith
  dsimp only [gap] at hsmall
  linarith

end InvariantIsing

end

end OAI
