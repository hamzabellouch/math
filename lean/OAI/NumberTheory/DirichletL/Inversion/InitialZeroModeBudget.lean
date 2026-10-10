import OAI.NumberTheory.DirichletL.Inversion.InitialZeroModePhysical

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem physical_marked_zero_bound (loss L b B:ℝ)(hloss:0<loss)(hL:0≤L)
    (hb:0<b)(hB:0≤B)(Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,λ₀^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→
      ∀Z D m:ℝ,1≤Z→D≤L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hp hcop hg Ψ j (primeMark slots lists a)
            W Φ Z D m G U T E 0 else 0‖≤C*Z^(m+loss) := by
  let eps:=loss/(L+1)
  have heps:0<eps:=div_pos hloss (by linarith)
  obtain ⟨C,hC,hbound⟩:=marked_normalized_zero eps b B heps hb hB Φ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j slots lists a hdis ha W hW hs Z D m hZ hD
  have hZ0:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  rw [physical_zero_sum p hp hcop hg hinj hc hpr]
  have heq:((Z^(-D):ℝ):ℂ)=((Z^D:ℝ):ℂ)⁻¹:=by
    rw [Real.rpow_neg hZ0.le,Complex.ofReal_inv]
  rw [heq]
  have hb':=hbound p hp hcop hg hinj pool Ψ hΨ j 1 1 slots lists a hdis ha
    W hW hs (Z^D) (Z^m) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (fun _ _=>{0}) (by intros; simp)
  change ‖_‖≤C*Z^(m+loss)
  apply hb'.trans
  rw [←Real.rpow_mul hZ0.le, mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  have hprod:D*eps≤loss:=by
    apply (mul_le_mul_of_nonneg_right hD heps.le).trans
    dsimp [eps]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith:0<L+1)).mpr
    nlinarith
  linarith

end SevenEighths.InverseInitialZeroMode

end

end OAI
