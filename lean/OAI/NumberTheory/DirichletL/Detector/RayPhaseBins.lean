import OAI.NumberTheory.DirichletL.Detector.RayCharacterFamily
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeRayPhaseBins
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh σmin σmax δ : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      CanonicalQuadraticSieve.Supported (Ideal.span {u.val}) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d →
    ∀(a : ℝ) (i : ℕ),51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (z : ℂ),rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      |z.im|+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost →
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA
    (hWs.trans Ioo_subset_Icc_self) hW R dmin dmax rmin τ ε e κ cost mesh σmin σmax
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hbudget hgap
  have hn := large_supported_twists_eventually M δ hδ
  have ht := ProbeRaySlots.power_fixed_exclusions S A (dmin*rmin) hA (mul_pos hdmin hrmin)
    (fun p : {p : ℝ×ℝ // dmin≤p.1 ∧ rmin≤p.2}=>p.val.1*p.val.2)
    (fun p=>mul_le_mul p.property.1 p.property.2 hrmin.le (hdmin.trans_le p.property.1).le)
  filter_upwards [hb,hn,ht,eventually_ge_atTop (1:ℝ)] with Z hb hn ht hZ
  intro d hd hd' hU hT η u hu hs hcond a i ha ha' hbin r z hr hr' hσ hσ' hf hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hsmall : ∀P∈S,(P.absNorm:ℝ)≤A*(Z^d)^r := by
    intro P hP
    rw [←Real.rpow_mul hZp.le]
    exact ht ⟨(d,r),hd,hr⟩ P hP
  have hnp := hn u hu hs H hH
  have hzmax := (source_nonprincipal_maximum_dominates S hS η u
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse) hnp _).trans_lt hbin
  have hq (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤Z^d :=
    (show ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ) by
        exact_mod_cast raw_twisted_conductor M H hH u θ).trans hcond
  have heq := canonical_amplitude_raw M H S hS hbad u W A B ((Z^d)^r) hD hWs hsmall z
  have hbins := hb d hd hd' hU hT (rawRow u).inverse hnp a i ha ha' hzmax
    r (1-z.re) z.im hr hr' hσ hσ' hq hf hh
  rw [←heq] at hbins
  refine ⟨hbins.1,hbins.2.1,hbins.2.2.1,hbins.2.2.2.1,hbins.2.2.2.2,?_⟩
  rw [central_phase_norm M H S u.val W A B ((Z^d)^r) hA hAB hD hWs hsmall z]
  calc
    _ ≤ ((Z^d)^r)^(z.re-1/2)*((Z^d)^r)^(_+mesh) :=
      mul_le_mul_of_nonneg_left hbins.2.2.2.1 (Real.rpow_nonneg hD.le _)
    _ = _ := by rw [←Real.rpow_add hD];congr 1;ring
end SevenEighths.ProbeRayPhaseBins

end

end OAI
