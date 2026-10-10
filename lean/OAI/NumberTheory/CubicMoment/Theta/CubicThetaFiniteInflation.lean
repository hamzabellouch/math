import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteConductor

namespace OAI

/-! The exact multiplicity in a finite residue-ring inflation. The
surjective reduction is used directly, so no choice of residue representatives
enters the resulting sum identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_sum_surjective_addHom {R S : Type*} [AddCommGroup R] [AddCommGroup S]
    [Fintype R] [Fintype S] (r : R →+ S) (hr : Function.Surjective r) (f : S → ℂ) :
    (∑ x : R, f (r x))=(Fintype.card R:ℂ)/(Fintype.card S:ℂ)*∑ y : S, f y := by
  have hshift (y : S) : (∑ x : R, f (r x+y))=∑ x : R, f (r x) := by
    obtain ⟨b,rfl⟩ := hr y
    have he := Equiv.sum_comp (Equiv.addRight b) (fun x => f (r x))
    change (∑ x : R, f (r (x+b)))=∑ x : R, f (r x) at he
    simpa only [map_add] using he
  have he : (Fintype.card S:ℂ)*(∑ x : R, f (r x))=
      (Fintype.card R:ℂ)*(∑ y : S, f y) := by
    calc
      _ = ∑ y : S, ∑ x : R, f (r x+y) := by simp_rw [hshift]; simp
      _ = ∑ x : R, ∑ y : S, f (r x+y) := Finset.sum_comm
      _ = ∑ _x : R, ∑ y : S, f y := by
        apply Finset.sum_congr rfl
        intro x _
        exact Equiv.sum_comp (Equiv.addLeft (r x)) f
      _ = _ := by simp
  have hcard : (Fintype.card S:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply (mul_left_cancel₀ hcard)
  calc
    _ = (Fintype.card R:ℂ)*(∑ y : S, f y) := he
    _ = _ := by field_simp

theorem residue_sum_inflation {q d : Eisenstein} (hq : q≠0) (hd0 : d≠0)
    (hd : d ∣ q) (f : Residues d → ℂ) :
    (∑' x : Residues q, f (residueReduction hd x))=
      ((norm q/norm d:ℝ):ℂ)*∑' y : Residues d, f y := by
  let : Finite (Residues q) := finite_residues hq
  let : Finite (Residues d) := finite_residues hd0
  let : Fintype (Residues q) := Fintype.ofFinite _
  let : Fintype (Residues d) := Fintype.ofFinite _
  have he := finite_sum_surjective_addHom (residueReduction hd).toAddMonoidHom
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr hd)) f
  change (∑ x : Residues q, f (residueReduction hd x))=
    (Fintype.card (Residues q):ℂ)/(Fintype.card (Residues d):ℂ)*∑ y : Residues d, f y at he
  have hqcard : (Fintype.card (Residues q):ℂ)=(norm q:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hq]
    exact_mod_cast (normNat_cast q)
  have hdcard : (Fintype.card (Residues d):ℂ)=(norm d:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hd0]
    exact_mod_cast (normNat_cast d)
  simpa only [tsum_fintype,hqcard,hdcard,Complex.ofReal_div] using he

lemma residueFourierChar_mul_factor {d k : Eisenstein} (hd : d≠0) (hk : k≠0)
    (h a : Eisenstein) :
    residueFourierChar (d*k) (mul_ne_zero hd hk)
        (Ideal.Quotient.mk (modulus (d*k)) (k*h*a))=
      residueFourierChar d hd (Ideal.Quotient.mk (modulus d) (h*a)) := by
  rw [residueFourierChar_mk,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  have hdC : (d:ℂ)≠0 := fun he => hd (Subtype.ext he)
  have hkC : (k:ℂ)≠0 := fun he => hk (Subtype.ext he)
  push_cast
  field_simp [hdC,hkC,traceLambda_ne_zero]

theorem residueFourier_inflation {d k : Eisenstein} (hd : d≠0) (hk : k≠0)
    (f : Residues d → ℂ) (h : Eisenstein) :
    (∑' x : Residues (d*k), f (residueReduction (dvd_mul_right d k) x)*
      residueFourierChar (d*k) (mul_ne_zero hd hk)
        (Ideal.Quotient.mk (modulus (d*k)) (k*h)*x))=
      (norm k:ℂ)*∑' y : Residues d, f y*
        residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y) := by
  have he (x : Residues (d*k)) :
      residueFourierChar (d*k) (mul_ne_zero hd hk)
          (Ideal.Quotient.mk (modulus (d*k)) (k*h)*x)=
        residueFourierChar d hd
          (Ideal.Quotient.mk (modulus d) h*residueReduction (dvd_mul_right d k) x) := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul,residueReduction_mk,← map_mul]
    exact residueFourierChar_mul_factor hd hk h a
  simp_rw [he]
  have hs := residue_sum_inflation (mul_ne_zero hd hk) hd (dvd_mul_right d k)
    (fun y => f y*residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y))
  have hn : norm (d*k)/norm d=norm k := by
    rw [norm_mul_eq,mul_div_cancel_left₀ _ (ne_of_gt (norm_pos_of_ne_zero hd))]
  simpa only [hn] using hs

theorem residueFourier_inflation_of_eq {q d k : Eisenstein}
    (hq : q≠0) (hd : d≠0) (hk : k≠0) (hf : q=d*k) (hdq : d ∣ q)
    (f : Residues d → ℂ) (h : Eisenstein) :
    (∑' x : Residues q, f (residueReduction hdq x)*
      residueFourierChar q hq (Ideal.Quotient.mk (modulus q) (k*h)*x))=
      (norm k:ℂ)*∑' y : Residues d, f y*
        residueFourierChar d hd (Ideal.Quotient.mk (modulus d) h*y) := by
  subst q
  exact residueFourier_inflation hd hk f h

end CubicFirstMoment

end

end OAI
