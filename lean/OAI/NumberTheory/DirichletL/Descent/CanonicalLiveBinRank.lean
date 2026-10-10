import OAI.NumberTheory.DirichletL.Descent.CanonicalRankCapChildren
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongGeometry

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_bin_rank_children
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:0≤eta)(heta1:eta≤1)
    (hcut:0<cutoff)(hsmall:eta≤cutoff/32)(hV:0≤V)(hparentcap:N+V≤L)
    (hbW:bW≤Z^eta)(hlog:1≤eta*Real.log Z)(hexp:Real.exp 1≤Z^eta)
    (hbin:2≤Z^eta)(hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤Mnext)(hFc:N+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree :=by
  dsimp only
  intro h₁ h₂ k l jj negative
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D hbad bW Z N V cutoff eta L j
    hZ hL heta1 hV hparentcap hbW hlog hne
  have hs:(N-3*actualCubeLength Z j)+3*actualCubeLength Z j+V=N+V:=by ring
  apply canonical_rank_cap_children (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun i=>(primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2)
    Finset.univ _ k l jj negative base Ψ hΨ m hm slots lists a ω₁ ω₂
    Z M _ _ V eta tau window b (cutoff/2) Qwidth z c eps A Mnext Fnext cnext K degree
    hZ heta hbin hel hV hb hbt hwindow (by linarith) (by linarith) (by linarith)
    (by simpa only [hs] using hparent) hpuncture ?_ hMc (by simpa only [hs] using hFc) hcc h₁ h₂
  intro v hv
  apply (hqn v hv).2.trans
  calc
    _≤Z^eta*Z^(actualCubeLength Z j):=mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (by linarith) _)
    _=Z^(actualCubeLength Z j+eta):=by rw [Real.rpow_add (by linarith : 0<Z)];ring

end SevenEighths.InverseMoment

end

end OAI
