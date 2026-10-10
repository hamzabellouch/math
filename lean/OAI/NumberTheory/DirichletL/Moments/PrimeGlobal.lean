import OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeGlobal
open HeckeFamily HeckePrimeRay HeckeZeroSupremum

lemma zeroMaximum_le_beta {ι : Type*} [Fintype ι]
    (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ)
    (hbeta : (51/100:ℝ)≤beta) :
    HeckeDetectorZeros.zeroMaximum χ hχ T≤beta := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hbeta
  · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
    have hz := (HeckeDetectorZeros.mem_familyZeros χ hχ T i s).mp hs
    exact zero_re_le_beta (χ i) (by linarith [hz.1]) (Or.inr (hχ i)) hz.2.2.2

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_prime_global_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e slack η σmin σmax κ : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hslack : 0<slack) (hη : 0≤η)
    (hbudget : 8*e*R+slack≤ε) (hbeta : (51/100:ℝ)≤beta)
    (hκ : 2*beta-1≤κ) :
    ∃ C : ℝ,0<C ∧ ∀ Z d : ℝ,1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (_hn : ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (i : ℕ),
    ∀ r σ freq : ℝ,0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq‖^2≤
        C*(Z^d)^(κ*r+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e slack η σmin σmax hR hdmax hτ hε he he' hslack hη hbudget
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z d hZ hd hdmax hU hT χ hn i r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hmax := zeroMaximum_le_beta (twistedFamily M H hH χ) hn
    (3*(i+1:ℕ)*Z^τ) hbeta
  have hb := hbound Z d hZ hd hdmax hU hT χ hn beta i hbeta beta_le_one
    (by linarith) r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hUp : 0<Z^d := by linarith
  have hp : ((Z^d)^((beta-1/2)*r+ε))^2 = (Z^d)^(2*((beta-1/2)*r+ε)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  calc
    _≤(C*(Z^d)^((beta-1/2)*r+ε))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _=C^2*(Z^d)^(2*((beta-1/2)*r+ε)) := by rw [mul_pow,hp]
    _≤C^2*(Z^d)^(κ*r+2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z^d)
        (by nlinarith [mul_le_mul_of_nonneg_right hκ hr])) (sq_nonneg _)

end SevenEighths.CenteredMomentPrimeGlobal

end

end OAI
