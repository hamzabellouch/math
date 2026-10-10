import OAI.NumberTheory.DirichletL.Detector.RayPhaseBins
import OAI.NumberTheory.DirichletL.PrimeRows.CubeScale

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hν : 0<ν) (hheight : 2*τ<dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤r → r≤R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end SevenEighths.ProbeHighRowFamily

end

end OAI
