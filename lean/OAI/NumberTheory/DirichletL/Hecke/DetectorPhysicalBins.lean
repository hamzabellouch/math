import OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem physical_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (data : RowData M) (cert : Ramification M data) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum
        (HeckePrimeRay.twistedFamily M H hH (data.character M))
        (cert.nonprincipal M H hH) (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ (r : ℝ) (z : ℂ), rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm≤Z^d →
      |z.im|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H data.u W B ((Z^d)^r) z
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  have hh := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA hWs hW
    R dmin dmax rmin τ ε e κ η mesh σmin σmax hR hdmin hdmax hrmin
    hτ hε he he' hκ hη hmesh hbudget hgap
  filter_upwards [hh] with Z hZ
  intro d hd hd' hU hT data cert a i ha ha' hnext r z hr hr' hs hs' hQ hf ht
  have hQ' (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤Z^d := by
    have hb := data.twisted_conductor M H hH θ
    have hb' : ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤
        ((M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
          (Ideal.span {data.u}).absNorm : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (by exact_mod_cast hQ)
  have hb := hZ d hd hd' hU hT (data.character M) (cert.nonprincipal M H hH)
    a i ha ha' hnext r (1-z.re) z.im hr hr' hs hs' hQ' hf ht
  simpa only [data.amplitude_eq M H hH] using hb

end SevenEighths.HeckeDetectorPhysicalBins

end

end OAI
