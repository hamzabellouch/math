import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCoefficient

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualCubeLength (Z:ℝ)(j:ℕ):ℝ:=Real.logb Z (normLogScale j)

theorem actualCubeLength_power (Z:ℝ)(hZ:1<Z)(j:ℕ) :
    Z^(actualCubeLength Z j)=normLogScale j :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normLogScale_pos j)

theorem actual_long_bin_geometry
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (b Z N V cutoff eta L:ℝ)(j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:eta≤1)
    (hV:0≤V)(hparent:N+V≤L)(hb:b≤Z^eta)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j)).Nonempty) :
    let ell:=actualCubeLength Z j;
    let r:=N-3*ell;
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j);
    0≤ell ∧ -eta≤r ∧ r≤L ∧ ell≤L ∧ r+3*ell+V≤L ∧ cutoff-eta≤ell+V ∧
      ∀v∈Q,Z^ell≤‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2≤Real.exp 1*Z^ell := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hp:Z^(actualCubeLength Z j)=normLogScale j:=actualCubeLength_power Z hZ j
  have hel:0≤actualCubeLength Z j:=Real.logb_nonneg hZ (normLogScale_ge_one j)
  have hnorm (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
      (hv:v∈activeCubeLogBin S D b (Z^N) j) :
      Z^(actualCubeLength Z j)≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) ∧
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*Z^(actualCubeLength Z j) := by
    rw [hp]
    exact activeCubeLogBin_norms S D b (Z^N) j v hv
  obtain ⟨v,hv⟩:=hne
  have hvbin: v∈activeCubeLogBin S D b (Z^N) j := (Finset.mem_filter.mp hv).1
  have hactive:= (Finset.mem_filter.mp hvbin).1
  have hcube:(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3≤b*Z^N :=
    (Finset.mem_filter.mp hactive).2
  have hsc:(Z^(actualCubeLength Z j))^3≤Z^(N+eta) := by
    calc
      _≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (hnorm v hvbin).1 3
      _≤b*Z^N:=hcube
      _≤Z^eta*Z^N:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(N+eta):=by rw [Real.rpow_add hz];ring
  rw [←Real.rpow_mul_natCast hz.le] at hsc
  have hscale:actualCubeLength Z j*3≤N+eta := (Real.rpow_le_rpow_left_iff hZ).mp hsc
  have hprogress:=long_cube_progress_with_slack S D (activeCubeLogBin S D b (Z^N) j)
    Z cutoff V (actualCubeLength Z j) eta hZ hlog ⟨v,hv⟩ (fun v hv=>(hnorm v hv).2)
  refine ⟨hel,by linarith,by linarith,by linarith,by linarith,hprogress,?_⟩
  intro u hu
  rw [cubeIdeal_primeProduct_norm _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  exact hnorm u (Finset.mem_filter.mp hu).1

end SevenEighths.InverseMoment

end

end OAI
