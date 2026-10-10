import OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
import OAI.NumberTheory.DirichletL.Descent.MarkBounds

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem marked_coefficient_mass (eps b B:ℝ)(heps:0<eps)(hb:0<b)(_hB:0≤B):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X:ℝ,0<X→
      (∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)≤C*X^(1+eps) := by
  obtain ⟨Cm,hCm,hm⟩:=finite_primeMark_small_power (eps/2) (by positivity)
  refine ⟨128*b*(Cm*b^(eps/2)*B)^2+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  let T:=pool.powerset.filter (fun A=>W (primeProductNorm p A/X)≠0)
  have hXb:0<b*X:=mul_pos hb hX
  have hnorm:∀A∈T,primeProductNorm p A≤b*X:=by
    intro A hA
    exact (div_le_iff₀ hX).mp (hs _ (Finset.mem_filter.mp hA).2)
  have hcard:(T.card:ℝ)≤128*(b*X):=by
    by_cases hsmall:1≤b*X
    · apply (Nat.cast_le.mpr (Finset.card_le_card (show T⊆boundedPrimeSupports p pool (b*X) from ?_))).trans
        (boundedPrimeSupports_card p hinj pool (b*X) hsmall)
      intro A hA
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,hnorm A hA⟩
    · have hz:T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        exact hsmall ((primeProductNorm_ge_one p hp A).trans (hnorm A hA))
      rw [hz]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have he:(∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)=
      ∑A∈T,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    have hz:W (primeProductNorm p A/X)=0:=by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
    simp only [secondInputCoefficient,hz,mul_zero,norm_zero,zero_pow (by decide:2≠0)]
  have hcoeff:∀A∈T,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖≤Cm*(b*X)^(eps/2)*B:=by
    intro A hA
    apply (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d _ A).trans
    rw [norm_mul]
    apply mul_le_mul _ (hW _) (norm_nonneg _) (by positivity)
    exact (hm p hp hcop slots lists a hdis ha A).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (primeProductNorm_pos p hp A).le (hnorm A hA) (by positivity)) hCm.le)
  rw [he]
  calc
    _≤∑_A∈T,(Cm*(b*X)^(eps/2)*B)^2:=by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff A hA) 2
    _=(T.card:ℝ)*(Cm*(b*X)^(eps/2)*B)^2:=by simp
    _≤(128*(b*X))*(Cm*(b*X)^(eps/2)*B)^2:=mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=(128*b*(Cm*b^(eps/2)*B)^2)*X^(1+eps):=by
      rw [Real.mul_rpow hb.le hX.le,Real.rpow_add hX,Real.rpow_one]
      have hh:(X^(eps/2))^2=X^eps:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
        congr 1
        norm_num
      calc
        _=(128*b*(Cm*b^(eps/2)*B)^2)*(X*(X^(eps/2))^2):=by ring
        _=_:=by rw [hh]
    _≤_:=by nlinarith [Real.rpow_nonneg hX.le (1+eps)]

theorem marked_normalized_zero (eps b B:ℝ)(heps:0<eps)(hb:0<b)(hB:0≤B)
    (Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X Y:ℝ,0<X→0<Y→
      ∀K:Finset ι→Finset ι→Finset O,
      (∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈K G E)→
      ‖(X⁻¹:ℂ)*truncatedSecondZero p hg pool Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K‖≤C*Y*X^eps := by
  obtain ⟨Cm,hCm,hm⟩:=marked_coefficient_mass eps b B heps hb hB
  refine ⟨Cm*‖paperRadialFourier Φ 0‖+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X Y hX hY K hK
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ m c d
    (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K hK
  rw [abs_of_pos hY] at hz
  apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hX.le)).trans
  have hm':=hm p hp hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  calc
    _≤X⁻¹*(Y*‖paperRadialFourier Φ 0‖*(Cm*X^(1+eps))):=by gcongr
    _=(Cm*‖paperRadialFourier Φ 0‖)*Y*X^eps:=by
      rw [Real.rpow_add hX,Real.rpow_one]
      field_simp
    _≤_:=by nlinarith [mul_nonneg hY.le (Real.rpow_nonneg hX.le eps)]

end SevenEighths.InverseInitialZeroMode

end

end OAI
