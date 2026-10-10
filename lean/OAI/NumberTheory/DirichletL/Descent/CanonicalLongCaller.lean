import OAI.NumberTheory.DirichletL.Descent.CanonicalLongWeight
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCount
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongIntegral

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem normalized_complete_marked_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z→0<R→V≤L→(∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      (∀t,W t≠0→t≤b)→b*Z^N≤D→
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W (Z^N) Z (N+V)≤
      2*C*Z^(-V+eps)*(
        rowFamilyEnergy labels (fun I z=>markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W (Z^N) H₀
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)) R+
        (cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
          rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
            (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
            Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R) := by
  obtain ⟨C,hC,hh⟩:=normalized_second_energy_le_actual_family K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀
    hZ hR hV hnorm hW hD
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=hh (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels hlabels W
    (Z^N) Z (N+V) V R hZ hR hV hnorm
  have hsplit:=actual_marked_family_binned S D hbad hSp labels Ψ m W hWc
    b (Z^N) H₀ R (Real.rpow_pos_of_pos hz _) hR hW hD slots lists a
  have hcost: C*Z^(-(N+V)+eps)*(2*Z^N)=2*C*Z^(-V+eps) := by
    calc
      _=2*C*(Z^(-(N+V)+eps)*Z^N):=by ring
      _=2*C*Z^(-V+eps):=by rw [←Real.rpow_add hz];congr 2;ring
  apply hb.trans
  have he:=mul_le_mul_of_nonneg_left hsplit (show 0≤C*Z^(-(N+V)+eps) by positivity)
  rw [←mul_assoc,hcost] at he
  exact he

end SevenEighths.InverseMoment

end

end OAI
