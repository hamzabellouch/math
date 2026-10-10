import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScaled
import OAI.NumberTheory.DirichletL.PrimeLogProfile
import OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem source_log_profile_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq L : ℝ,
      0≤r → r≤R → σmin≤σ → σ≤σmax → L∈Icc (0 : ℝ) 1 →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖polynomial (χ k) (PrimeLogProfile.profile W L) ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ η he he' hκ hη
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+κ) 0
    hτ hdmax (by positivity) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) 2
  obtain ⟨Cn,hCn,hmn⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq L
    hr hrR hσmin hσmax hL k hQ hfreq hheight
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hs : Icc (a+8*e-σ) (2-σ)⊆Icc (-σmax) (2-σmin) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hleft : a+8*e-σ∈Icc (-σmax) (2-σmin) := by
    constructor <;> linarith
  have hb := hdirect χ hχ (Z^τ) a i hT ha ha' hmax k
    (PrimeLogProfile.profile W L) A B hA
    ((PrimeLogProfile.profile_support W L).trans hWs)
    (PrimeLogProfile.profile_smooth W A B hA hWs hW L)
    U r R σ freq (Z^τ/2) C₂ Cn n hU2 hQ hr hrR (by positivity)
    hfreq hheight hC₂.le hCn.le (hm₂ L hL _ hleft) (fun x hx => hmn L hL x (hs hx))
  have htail' := htail Z d 0 hZ hd hd' (by norm_num)
  simp only [Real.rpow_zero,mul_one] at htail'
  have hexp : (a-1/2+8*e)*r+κ≤(a-1/2)*r+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hrR (by positivity : 0≤8*e)]
  have hp : 0≤(a-1/2)*r+ε := by
    have : 0≤8*e*R := by positivity
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr]
  calc
    _ ≤ Cd*C₂*U^((a-1/2)*r+ε)+Cd*Cn*(2 : ℝ)^n := by
      apply hb.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)
      · calc
          _ = (Cd*Cn)*(U^(2*R+κ)/(1+Z^τ/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ (Cd*C₂+Cd*Cn*(2 : ℝ)^n)*U^((a-1/2)*r+ε) := by
      rw [add_mul]
      apply add_le_add (le_refl _)
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hU hp)

end SevenEighths.HeckePrimeDyadic

end

end OAI
