import OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy
import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma zero_mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (0 : Eis) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simpa using hR

def secondPhysicalCutoff {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) : Finset Eis :=
  childFrequencyBall (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R

def secondPhysicalMask {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R then 1 else 0

lemma secondPhysicalMask_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (d : Eis) (R : ℝ) (G E : Finset ι) (k : Eis) :
    ‖secondPhysicalMask p d R G E k‖ ≤ 1 := by
  unfold secondPhysicalMask
  split_ifs <;> norm_num

lemma secondPhysicalMask_exact {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (d : Eis) (hd : d ≠ 0) (R : ℝ) (G E : Finset ι) (k : Eis) :
    secondPhysicalMask p d R G E k =
      if 0 < ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ≤ R
      then 1 else 0 := by
  unfold secondPhysicalMask
  have he := mem_nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R k
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (he.mp h₁)).elim
  · exact (h₁ (he.mpr h₂)).elim
  · rfl

theorem physical_child_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis), d ≠ 0 → ∀ (V W : 𝓢(ℝ, ℂ)) (X M Y R : ℝ),
      0 < X → 1 ≤ Y → 0 ≤ R →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalMask p d R)‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s,C,hC,he⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d hd V W X M Y R hX hY hR hV
  apply he p hp hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d V W X M Y hX hY hV
  · intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R hR
  · intro G hG E k
    exact secondPhysicalMask_norm_le_one p d R G E.val k.val

end
end SevenEighths.InverseMoment

end OAI
