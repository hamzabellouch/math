import Mathlib
import OAI.Analysis.CoulombIonization.Variational.InsertionSwap

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators

namespace CoulombAtom

instance cosetWedgeFintype {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :
    Fintype (Equiv.Perm (Fin n) ⧸ H) := Fintype.ofFinite _

def SubgroupFermion {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n) : Prop :=
  ∀ κ ∈ H, ∀ s, ∀ᵐ x, T.value (s ∘ κ) (x ∘ κ) =
    (((Equiv.Perm.sign κ : ℤ) : ℂ) * T.value s x)

def cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n)
    (q : Equiv.Perm (Fin n) ⧸ H) : FormVector n :=
  scaleForm (((Equiv.Perm.sign q.out : ℤ) : ℝ)) (reindexForm q.out.symm T)

def cosetWedge {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n) : FormVector n :=
  sumForm (cosetWedgeTerm H T)

lemma cosetWedgeTerm_value {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n)
    (q : Equiv.Perm (Fin n) ⧸ H) (s : Spins n) (x : Configuration n) :
    (cosetWedgeTerm H T q).value s x = (((Equiv.Perm.sign q.out : ℤ) : ℂ)) *
      T.value (s ∘ q.out) (x ∘ q.out) := by
  simp only [cosetWedgeTerm, scaleForm, reindexForm, Equiv.symm_symm, Complex.ofReal_intCast]

lemma SobolevVector.cosetWedgeTerm {n : ℕ} {T : FormVector n} (hT : SobolevVector T)
    (H : Subgroup (Equiv.Perm (Fin n))) (q : Equiv.Perm (Fin n) ⧸ H) :
    SobolevVector (cosetWedgeTerm H T q) :=
  (hT.reindex q.out.symm).scale _

lemma cosetWedge_fermion {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hTa : SubgroupFermion H T) : SobolevFermion (cosetWedge H T) := by
  classical
  have hw := SobolevVector.sum (fun q => hT.cosetWedgeTerm H q)
  refine ⟨hw.1,hw.2.1,hw.2.2,?_⟩
  intro π s
  have hh (q : Equiv.Perm (Fin n) ⧸ H) : ∀ᵐ x,
      (cosetWedgeTerm H T q).value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ)) * (cosetWedgeTerm H T (π • q)).value s x := by
    let κ := (π • q).out⁻¹ * (π * q.out)
    have hk : κ ∈ H := by
      apply QuotientGroup.eq.mp
      exact (QuotientGroup.out_eq' (π • q)).trans
        (MulAction.Quotient.mk_smul_out H π q).symm
    have he : π * q.out = (π • q).out * κ := by simp [κ]
    have hp := (permuteConfiguration_preserving (π • q).out).quasiMeasurePreserving.ae
      (hTa κ hk (s ∘ (π • q).out))
    filter_upwards [hp] with x hx
    simp only [permuteConfiguration_apply] at hx
    have hsg : (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) =
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) := by
      have ht := congrArg (fun σ => (((Equiv.Perm.sign σ : ℤ) : ℂ))) he
      simpa only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul] using ht
    have hsg' : (((Equiv.Perm.sign q.out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) := by
      have hs := complex_sign_sq (π • q).out
      have ht := complex_sign_sq q.out
      linear_combination -(((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) * hsg +
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (π • q).out : ℤ) : ℂ)) * ht -
        (((Equiv.Perm.sign κ : ℤ) : ℂ)) *
        (((Equiv.Perm.sign q.out : ℤ) : ℂ)) * hs
    have hv : ((s ∘ π) ∘ q.out) = (s ∘ (π • q).out) ∘ κ := by
      change s ∘ (π * q.out) = s ∘ ((π • q).out * κ)
      rw [he]
    have hvx : ((x ∘ π) ∘ q.out) = (x ∘ (π • q).out) ∘ κ := by
      change x ∘ (π * q.out) = x ∘ ((π • q).out * κ)
      rw [he]
    rw [cosetWedgeTerm_value,cosetWedgeTerm_value,hv,hvx,hx,← mul_assoc,hsg',mul_assoc]
  have ha := (ae_all_iff.mpr hh)
  filter_upwards [ha] with x hx
  change (∑ q, (cosetWedgeTerm H T q).value (s ∘ π) (x ∘ π)) =
    _ * ∑ q, (cosetWedgeTerm H T q).value s x
  simp_rw [hx]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm π) (fun q => (cosetWedgeTerm H T q).value s x)

lemma formMass_cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (T : FormVector n) (q : Equiv.Perm (Fin n) ⧸ H) :
    formMass (cosetWedgeTerm H T q) = formMass T := by
  rw [cosetWedgeTerm, formMass_scale, formMass_reindex, real_sign_sq, one_mul]

lemma formEnergy_cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (T : FormVector n) (q : Equiv.Perm (Fin n) ⧸ H) (Z : ℝ) :
    formEnergy Z (cosetWedgeTerm H T q) = formEnergy Z T := by
  rw [cosetWedgeTerm, formEnergy_scale, formEnergy_reindex, real_sign_sq, one_mul]

lemma formMass_cosetWedge {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hd : FormsDisjoint (cosetWedgeTerm H T)) :
    formMass (cosetWedge H T) = (Fintype.card (Equiv.Perm (Fin n) ⧸ H) : ℝ) * formMass T := by
  rw [cosetWedge, formMass_sum_disjoint (fun q => hT.cosetWedgeTerm H q) hd]
  simp only [formMass_cosetWedgeTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma formEnergy_cosetWedge {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hd : FormsDisjoint (cosetWedgeTerm H T)) (Z : ℝ) :
    formEnergy Z (cosetWedge H T) = (Fintype.card (Equiv.Perm (Fin n) ⧸ H) : ℝ) * formEnergy Z T := by
  rw [cosetWedge, formEnergy_sum_disjoint (fun q => hT.cosetWedgeTerm H q) hd]
  simp only [formEnergy_cosetWedgeTerm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem normalized_coset_wedge_trial {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : FormVector n}
    (hT : SobolevVector T) (hTa : SubgroupFermion H T) (hm : formMass T = 1)
    (hd : FormsDisjoint (cosetWedgeTerm H T)) (Z : ℝ) :
    ∃ F : FormVector n, FormAdmissible F ∧ formEnergy Z F = formEnergy Z T := by
  have hw := formMass_cosetWedge hT hd
  rw [hm,mul_one] at hw
  have hp : 0 < formMass (cosetWedge H T) := by
    rw [hw]
    exact_mod_cast Fintype.card_pos
  refine ⟨scaleForm (Real.sqrt (formMass (cosetWedge H T)))⁻¹ (cosetWedge H T),
    (cosetWedge_fermion hT hTa).normalize hp,?_⟩
  rw [formEnergy_scale,formEnergy_cosetWedge hT hd,hw,inv_pow,
    Real.sq_sqrt (le_of_lt (show (0:ℝ) < Fintype.card (Equiv.Perm (Fin n) ⧸ H) by
      exact_mod_cast Fintype.card_pos))]
  field_simp

end CoulombAtom

end

end OAI
