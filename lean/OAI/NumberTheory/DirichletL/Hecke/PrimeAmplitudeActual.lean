import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale
import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_amplitude_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, rmin≤r → r≤R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  have hbins := actual_bins_eventually C dmin rmin ε mesh hdmin hrmin hmesh hgap
  have hlog := HeckePrimeScale.log_scale_eventually dmin rmin
    (2*(|Real.log A|+|Real.log B|)+1) hdmin hrmin
  filter_upwards [hbins,hlog,eventually_ge_atTop (1 : ℝ)] with Z hb hl hZ
  intro d hd hd' hU hT χ hχ a i ha ha' hmax r σ freq hr hr' hσ hσ' hQ hf ht
  have hestimate := hbound Z d hZ (hdmin.trans_le hd).le hd' hU hT χ hχ a i
    ha ha' hmax r σ freq (hrmin.trans_le hr).le hr' hσ hσ' (hl d r hd hr) hQ hf ht
  exact hb d hd r (a-1/2) hr (by linarith) _ hestimate

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI
