import OAI.NumberTheory.DirichletL.Moments.NaturalReflection
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem actual_original_twisted_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(_ha : 0<a)(_hs : Function.support W⊆Set.Icc a b)
        (_hW : ContDiff ℝ ∞ W)(omega X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 omega=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false
                (paperRadialFourier (CompletedHeight.normTwistedSource W (omega/(2*Real.pi))))
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,hreflect⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W a b ha hs hW omega X hX
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi)) : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W (omega/(2*Real.pi)) := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW _ x
  have hh := hreflect (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi))) X hX
  rw [he] at hh
  have ht : 2*Real.pi*(omega/(2*Real.pi))=omega := by field_simp
  rw [←ht,polynomial_twisted_source χ W X (omega/(2*Real.pi)) hX]
  simpa only [ht] using hh

end SevenEighths.CenteredMomentTwistedReflection

end

end OAI
