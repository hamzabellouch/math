import OAI.NumberTheory.DirichletL.Inversion.InitialTotalEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawInputBound
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT CompletedGauss SecondPassArithmetic CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalCoefficientClass InverseMoment InverseInitialProfile InverseInitialRayAttachment
open InverseInitialQuotientGeometry InverseInitialProfileBounds
local notation "O"=>ActualEisensteinCubic.O

theorem raw_input_bound
    (W:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support W⊆Set.Icc a b)
    (Φ:𝓢(ℝ,ℂ))(gap eps π η τ loss:ℝ)
    (hgap:0<gap)(heps:0<eps)(hπ:0<π)(hη:0<η)(hηone:η≤1)
    (hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss):
    ∃J:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^3≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hg:=poolPrimary_good F hF;
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀ (r t : ℝ), (-2 : ℝ) ≤ r → r ≤ 1 - 2 * gap → 2 * r ≤ 3 - 2 * gap → r + 7 * η ≤ 2 →
    ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z)*
      (‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ 1 1 1
        (initialTest p (fun _=>1) (childLogTest W t) Z r) u‖^2:ℝ)‖≤
      C*Z^(1+15*η+π+eps+loss)*(1+‖t‖)^(2*J) := by
  have hB:0≤SchwartzMap.seminorm ℝ 0 0 W:=apply_nonneg _ _
  have hb:∀x,‖W x‖≤SchwartzMap.seminorm ℝ 0 0 W:=fun x=>by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using W.le_seminorm ℝ 0 0 x
  obtain ⟨degree,Btree,hBtree,hbound⟩:=InverseInitialTotalEnergy.original_input_bound
    W a b 1 ha le_rfl hs (W.smooth ⊤) Φ _ hB hb 2 gap eps π η τ loss
    (by norm_num) hgap heps hπ hη hηone hηsmall hτ hτsmall hloss 0
  refine ⟨InverseClippingProfiles.momentOrder (4*degree),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hpool F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro p hg Ψ hΨ hperiod r t hrlo hr₁ hr₂ hrcap
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hpool':Btree*Z^((2:ℝ)+1)≤Dpool:=by norm_num;exact hpool
  have hp:=Real.one_le_rpow hZp.le hη.le
  have h:=hbound Z hZ Dpool hpool' (σ:=Fin 0) ∅ ∅ (by simp) (by simp)
    (fun _=>∅) (fun _=>1) (fun _ _=>0) (by simp) (by simp) (by simp) (by simp)
    (fun _=>1) (fun _=>0) (fun _=>1) (fun _=>1) (fun _ _=>0)
    (by simp) (by simp) (by simp) (by simp) Ψ hΨ hperiod r 1 r
    (by norm_num) (by norm_num) hrlo (by simpa using hp) (by simpa [assignedCenter] using hp)
    (by simp [assignedCenter]) (by simpa [assignedCenter] using hr₁)
    (by simpa [assignedCenter] using hr₂) (by simpa [assignedCenter] using hrcap)
    1 t le_rfl le_rfl
  simp only [Finset.sdiff_self,assignedElement,Finset.prod_empty] at h
  have hemark : primeMark (∅:Finset (Fin 0)) (fun _=> (∅:Finset (primePool F)))
      (fun _ _=> (0:ℂ))=(fun _=>1) := by
    funext A
    exact primeMark_empty _ _ A
  rw [hemark] at h
  simpa only [
    Real.rpow_one,←childLogTest_eq_clipped] using h

end SevenEighths.DetectorDictionaryInverseRawInputBound

end

end OAI
