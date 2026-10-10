import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.Vanishing

namespace OAI

noncomputable section

namespace Foulkes.Vanishing
open MvPolynomial Foulkes.Polarization Foulkes.PolynomialSpan

lemma vanishing_zero {a n : ℕ} {l : P a n →ₗ[ℂ] ℂ} (hz : ProductsVanish l 0)
    {f : P a n} (hf : f ∈ W a n 0) : l f = 0 := by
  have h1 : l 1 = 0 := by simpa using hz (fun i => Fin.elim0 i)
  have hW : W a n 0 ≤ LinearMap.ker l := by
    rw [W_eq_span_pureRows]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    simpa [pureRows] using h1
  exact hW hf

theorem block_vanishing (a : ℕ) : ∀ {n b : ℕ}, 1 ≤ a → (a-1)^2 ≤ b →
    ∀ {l : P a n →ₗ[ℂ] ℂ}, Symmetric l → ProductsVanish l b →
      ∀ f : P a n, f ∈ W a n b → l f = 0 := by
  induction a with
  | zero => intro n b ha; omega
  | succ r ih =>
    intro n b ha hb l hs hz f hf
    have hpure : ∀ v : Fin (r+1) → Fin n → ℂ, l (pureRows b v) = 0 := by
      intro v
      by_cases hr : r = 0
      · subst r
        have hh := hz (fun _ => v 0)
        simpa [pureRows, z, Fin.prod_univ_one] using hh
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        have hrb : r ≤ b := by
          simp only [Nat.add_sub_cancel] at hb
          nlinarith
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrb
        have hb' : r*r ≤ r+m := by simpa [pow_two] using hb
        have hrestrict (x t : Fin n → ℂ) (g : P r n) (hg : g ∈ W r n m) :
            restrictionFunctional l x t (r+m) g = 0 := by
          by_cases hm : m = 0
          · subst m
            exact vanishing_zero (restriction_products hrpos hs hz x t) hg
          · apply ih (by omega) ?_ (restriction_symmetric hs x t)
              (restriction_products hrpos hs hz x t) g hg
            have he : (r-1)+1 = r := by omega
            nlinarith
        have hh := remove_common_power hb'
          (v (Fin.last r)) (fun x g hg => hrestrict x (v (Fin.last r)) g hg)
          (fun i => v i.castSucc)
        simpa only [pureRows, Fin.prod_univ_castSucc] using hh
    have hW : W (r+1) n b ≤ LinearMap.ker l := by
      rw [W_eq_span_pureRows]
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      exact hpure v
    exact hW hf

end Foulkes.Vanishing

end

end OAI
