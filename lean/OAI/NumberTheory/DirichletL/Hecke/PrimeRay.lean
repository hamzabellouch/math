import OAI.NumberTheory.DirichletL.Hecke.PrimeBin
import OAI.NumberTheory.DirichletL.Hecke.RayQuotient
import OAI.NumberTheory.DirichletL.Hecke.IdealOperations

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def twistedFamily (η : Character) (θ : RayQuotient.Characters M H) : Character :=
  η.product (HeckeRayQuotient.character M H hH θ)

def rayPrimePolynomial (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter
    (fun I => Prime I ∧ I∈RayQuotient.identityClass M H),
      idealCoeff η I*annularWeight W D σ freq I

theorem finite_average (η : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S.filter (fun I => I∈RayQuotient.identityClass M H), idealCoeff η I*f I) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, ∑ I∈S,
          idealCoeff (twistedFamily M H hH η θ) I*f I := by
  rw [Finset.sum_filter,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [twistedFamily,idealCoeff_product]
  have hs : (∑ θ : RayQuotient.Characters M H,
      idealCoeff η I*idealCoeff (HeckeRayQuotient.character M H hH θ) I*f I) =
      (idealCoeff η I*f I)*∑ θ : RayQuotient.Characters M H,
        idealCoeff (HeckeRayQuotient.character M H hH θ) I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [hs,mul_left_comm,HeckeRayQuotient.average_idealCoeff M H hH I]
  split_ifs <;> simp

theorem rayPrimePolynomial_eq_average (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) :
    rayPrimePolynomial M H η W b D σ freq =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          primePolynomial (twistedFamily M H hH η θ) W b D σ freq := by
  unfold rayPrimePolynomial
  have hfilter : (annulusSet b D).filter (fun I => Prime I ∧ I∈RayQuotient.identityClass M H) =
      ((annulusSet b D).filter Prime).filter (fun I => I∈RayQuotient.identityClass M H) := by
    ext I
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter,finite_average M H hH η _ (annularWeight W D σ freq)]
  simp only [primePolynomial]
  rw [←Finset.mul_sum]
  ring

theorem rayPrimePolynomial_norm_le (η : Character) (W : ℝ→ℂ) (b D σ freq C : ℝ)
    (hbound : ∀ θ : RayQuotient.Characters M H,
      ‖primePolynomial (twistedFamily M H hH η θ) W b D σ freq‖≤C) :
    ‖rayPrimePolynomial M H η W b D σ freq‖≤C := by
  rw [rayPrimePolynomial_eq_average M H hH η W b D σ freq,norm_mul,norm_inv]
  have hcard : (0 : ℝ)<RayQuotient.classNumber M H := by
    exact_mod_cast RayQuotient.classNumber_pos M H
  have heq : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : ‖(RayQuotient.classNumber M H : ℂ)‖=(RayQuotient.classNumber M H : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (RayQuotient.classNumber M H : ℝ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, C :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun θ _ => hbound θ)))
        (by positivity)
    _ = C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,heq]; rw [←mul_assoc,inv_mul_cancel₀ hcard.ne',one_mul]

theorem ray_prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (ηrow : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ηrow θ).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH ηrow) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH ηrow θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H ηrow W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨C,hC,hbound⟩ := prime_bin_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hd' hU hT ηrow hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge hQ hfreq hheight
  apply rayPrimePolynomial_norm_le M H hH
  intro θ
  exact hbound Z d hZ hd hd' hU hT (twistedFamily M H hH ηrow) hχ a i ha ha' hmax
    r σ freq hr hrR hσmin hσmax hlarge θ (hQ θ) hfreq hheight

end SevenEighths.HeckePrimeRay

end

end OAI
