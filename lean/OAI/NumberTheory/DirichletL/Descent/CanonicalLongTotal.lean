import OAI.NumberTheory.DirichletL.Descent.CanonicalLongFinite

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_energy_from_live_bins (K:ℕ)(b L eps:ℝ)
    (hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(Z N V R H₀ Eshort Elong:ℝ),
      1≤Z → 0<R → N≤L → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D → 0≤Elong →
      Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2)≤Eshort →
      (∀j∈cubeLogRange b (Z^N),
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤Elong) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2)≤
      2*Eshort+C*Z^eps*Elong := by
  obtain ⟨Cw,hCw,hw⟩:=actual_complete_finite_split K L (eps/2) hL (by positivity)
  obtain ⟨Cb,hCb,hbnd⟩:=actual_cube_bin_count b L (eps/2) hb hL (by positivity)
  refine ⟨2*Cw*Cb,by positivity,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc Z N V R H₀ Eshort Elong
    hZ hR hN hV hnorm hW hD hE hshort hlong
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:=hw S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have ha:=actual_large_bins_aggregate S D labels Ψ m W b (Z^N) H₀ R Z V Elong slots lists a hlong hE
  have hc:=hbnd (Z^N) Z (Real.rpow_nonneg hz.le _) hZ (Real.rpow_le_rpow_of_exponent_le hZ hN)
  have hh:Z^(eps/2)*Z^(eps/2)=Z^eps := by rw [←Real.rpow_add hz];congr 1;ring
  have hp:Z^(-V+eps/2)=Z^(-V)*Z^(eps/2):=Real.rpow_add hz _ _
  have ha':2*Cw*Z^(-V+eps/2)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
        Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤
      (2*Cw*Cb)*Z^eps*Elong := by
    have h1:=mul_le_mul_of_nonneg_left ha (show 0≤2*Cw*Z^(eps/2) by positivity)
    have h2:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE)
      (show 0≤2*Cw*Z^(eps/2) by positivity)
    have ht:=h1.trans h2
    rw [hp]
    convert ht using 1
    · ring
    · rw [←hh];ring
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_left hshort (by norm_num:0≤(2:ℝ))) ha')

end SevenEighths.InverseMoment

end

end OAI
