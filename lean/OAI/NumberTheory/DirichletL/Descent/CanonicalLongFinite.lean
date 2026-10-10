import OAI.NumberTheory.DirichletL.Descent.CanonicalLongAggregate

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_finite_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z → 0<R → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2) ≤
      2*(Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2))+
      2*C*Z^(-V+eps)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R := by
  obtain ⟨C,hC,hweight⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let bins:=cubeLogRange b (Z^N)
  let short:=fun I z=>markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
    W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  let long:=fun j I z=>markedReopenedCubeBin S D
    (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
    Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a
  let ball:=nonzeroChildFrequencyBall 1 R
  have hpoint (I:Ideal O)(z:O):
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2≤
      2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2) := by
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b (Z^N) H₀ slots lists a
      hbad hSp hWc (Real.rpow_pos_of_pos hz _) hW hD
    convert hh using 1
    congr 2
    apply congrArg (fun x:ℝ=>(bins.card:ℝ)*x)
    apply Finset.sum_congr rfl
    intro j hj
    rw [marked_long_filter S D (activeCubeLogBin S D b (Z^N) j) Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a]
  have hlong (j:ℕ):
      (∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2)≤
      C*Z^eps*rowFamilyEnergy labels (long j) R := by
    rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hb:=finite_nonzero_row_energy_le_majorant (long j I) ball R hR
      (by intro z hz;rw [←eisEmbedding_norm_sq_eq_absNorm_span]
          simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).2)
      (by intro z hz he
          have hn:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).1
          simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hn)
    exact (mul_le_mul_of_nonneg_right (hweight Z V hZ hV I (hlabels I hI) (hnorm I hI))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hsum:=Finset.sum_le_sum (s:=labels) (fun I hI=>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=ball) (fun z hz=>hpoint I z))
      (show 0≤secondLabelWeight K I by unfold secondLabelWeight;positivity))
  have he:=mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le (-(N+V)))
  have hc:Z^(-(N+V))*Z^N=Z^(-V):=by rw [←Real.rpow_add hz];congr 1;ring
  have rearrange:
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈ball,
        2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2))=
      2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)+
      2*Z^(-V)*bins.card*∑j∈bins,∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2 := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp_rw [Finset.sum_comm (s:=ball) (t:=bins)]
    rw [Finset.sum_comm (s:=labels) (t:=bins)]
    simp only [←Finset.mul_sum,mul_assoc,mul_left_comm]
    rw [←hc]
    ring
  rw [rearrange] at he
  apply he.trans
  have hj:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=bins) (fun j hj=>hlong j))
    (show 0≤2*Z^(-V)*(bins.card:ℝ) by positivity)
  rw [←Finset.mul_sum] at hj
  have hpow:Z^(-V)*Z^eps=Z^(-V+eps):=(Real.rpow_add hz _ _).symm
  convert add_le_add_left hj (2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)) using 1 <;>
    dsimp [bins,short,long,ball] <;> (try rw [←hpow]) <;> ring

end SevenEighths.InverseMoment

end

end OAI
