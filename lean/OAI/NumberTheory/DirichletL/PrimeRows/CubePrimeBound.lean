import OAI.NumberTheory.DirichletL.Detector.CentralPrimeSum
import OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
import OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeThresholds
import OAI.NumberTheory.DirichletL.PrimeRows.CentralHeightCost

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem poolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀r : Fin N→ℝ,(∀j,rmin≤r j) → (∀j,r j≤R) →
      let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
      let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*r j*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>poolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  have hb (j : Fin N) := actual_phase_bins_on_cube M H hH S hS.prime hS.bad hmax (W j) c b hc hcb
    (hWs j) (hW j) R dmin dmax rmin τ ε e κ cost mesh δ margin n
    hR hdmin hdmax hrmin hτ hε he he1 hκ hcost hmesh hδ hbudget hgap hmargin hheight
  have hbAll := Filter.eventually_all.mpr hb
  obtain ⟨C,hC,hbound⟩ := ProbeCentralPrimeSum.actual_central_prime_sum N e eps c b A
    he he1 heps hc (hc.trans_le hcb) hA S hS hfirst hmax
  refine ⟨C,hC,?_⟩
  intro η
  have hscale := HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin 2 hdmin
  filter_upwards [hbAll,central_pool_good_eventually η e c b dmin rmin he hc hcb hdmin hrmin,
    cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hloss,
    hscale,source_cube_height_eventually τ hτ] with Z hb hg hheightZ hscaleZ hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  dsimp only
  intro hdis t ht
  let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
  let T : Fin N→Finset PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh
    (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
  have hU : 2≤Z^d := hscaleZ d hd
  have hUp : 0<Z^d := by linarith
  have hY (j : Fin N) : 1≤Y j := Real.one_le_rpow (by linarith) (hrmin.trans_le (hr j)).le
  have hYp (j : Fin N) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hphase (j : Fin N) := hb j d hd hd' hU hZ.2 η u hulo hcal huhi a i hi ha ha1 hbin (r j) t (hr j) (hr' j) ht
  refine ⟨fun j=>⟨(hphase j).1,(hphase j).2.1,(hphase j).2.2.1,(hphase j).2.2.2.1,(hphase j).2.2.2.2.1⟩,?_⟩
  let p : Fin N→ℝ := fun j=>(Y j)^(g j+mesh)
  have hp (j : Fin N) : 1≤p j := Real.one_le_rpow (hY j) (by have := (hphase j).1;dsimp [g];linarith)
  have hph (j : Fin N) : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j := by
    have hj := (hphase j).2.2.2.2.2
    have hsum : phaseSlot u (T j) (W j) (Y j) z=
        ∑P∈T j,W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val)) :=
      Finset.sum_coe_sort (T j) (fun P=>W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u.val P.val)))
    have hj' : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ)+g j+mesh) := by
      rw [hsum]
      convert hj using 1
      simp only [Y,g,z]
      congr 1
      norm_num
    apply hj'.trans_eq
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  have hgood (j : Fin N) (P : PrimeIdeal) (hP : P∈T j) := hg (RayQuotient.identityClass M H) S d (r j) hd (hr j) P hP
  have hfreq := cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht
    (Real.rpow_nonneg (zero_le_one.trans hZ.1) _) (by push_cast;have hh : 0≤Z^τ := Real.rpow_nonneg (zero_le_one.trans hZ.1) _;nlinarith)
  have hbound' := hbound u hu η (rayCubeFamily M H hH u) (Z^τ) a i hZ.2 ha ha1 hbin T
    (poolOutside M H S N c b Y) hdis (fun j P hP=>(hgood j P hP).2.1)
    (fun j P hP=>(hgood j P hP).2.2.1) (fun j P hP=>(hgood j P hP).2.2.2)
    W Y hY (fun j=>(hWs j).trans Ioo_subset_Icc_self) hWB
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z
    (by simp) (by simp) (by simp [z]) (by simpa using hfreq.1) (by simpa using hfreq.2.1) p hp hph
  have hprod : (∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)=∏j,(Y j)^(-(4/25:ℝ)+g j+mesh) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*Z^τ)^(2+4*eps)*((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      exact hbound'.trans_eq (by ring)
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
        ((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg
        (Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hYp j).le _))
        (Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))))
      exact mul_le_mul_of_nonneg_left (hheightZ i hi) (by unfold rowNorm;positivity)
    _ = _ := by rw [hprod]

end SevenEighths.ProbeHighRowFamily

end

end OAI
