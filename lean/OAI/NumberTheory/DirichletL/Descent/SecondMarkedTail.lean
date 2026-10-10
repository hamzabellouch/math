import OAI.NumberTheory.DirichletL.Descent.SecondWholeCutoff
import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hz)
    have hn0 : 0 ≤ primeProductNorm p U := (primeProductNorm_pos p hp U).le
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem full_marked_second_tail (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V W : 𝓢(ℝ,ℂ)) (X M Y H R : ℝ),
      0 < X → 0 < Y → 0 ≤ H → 1 ≤ X*Real.exp M →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      wholeSecondRadius d (X*Real.exp M) Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (fun _ E => childFrequencyBall (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*(X*Real.exp M))^4 *
          (((2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
              (1+(X*Real.exp M)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_whole_column_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha A V W X M Y H R hX hY hH hL hV hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d hd (markedRadial p slots lists a A V X) W
    _ Y H (X*Real.exp M) R (by positivity) hY hH hL
  · exact hmark p hp hcop slots lists a hslots ha A V X M hX hV
  · exact markedRadial_support p slots lists a A V X M hX hV
  · exact hR

end
end SevenEighths.InverseMoment

end OAI
