import OAI.NumberTheory.DirichletL.Descent.MarkBounds
import OAI.NumberTheory.DirichletL.Descent.PoissonTails

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def markedColumn {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ U) * C U

lemma markedColumn_source_support {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι)
    (h : markedColumn slots lists a A C U ≠ 0) : C U ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem markedColumn_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (C : Finset ι → ℂ) (G X M : ℝ),
      0 ≤ G → 0 < X →
      (∀ U ∈ F.powerset, ‖C U‖ ≤ G) →
      (∀ U ∈ F.powerset, C U ≠ 0 → columnLog p X U ≤ M) →
      ∀ U ∈ F.powerset, ‖markedColumn slots lists a A C U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A F C G X M hG hX hC hsupport U hU
  by_cases hz : C U = 0
  · simp only [markedColumn,hz,mul_zero,norm_zero]
    positivity
  · have hn := columnLog_norm_upper p hp X M hX U (hsupport U hU hz)
    rw [markedColumn,norm_mul]
    have hm := hmark p hp hcop slots lists a hslots ha A U
    have hnorm : 0 < primeProductNorm p U := primeProductNorm_pos p hp U
    apply (mul_le_mul hm (hC U hU) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem marked_first_kernel_remainder (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
      (F B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), Disjoint F B →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
        (a₁ a₂ : σ → ι → ℂ),
      (slots₁ : Set σ).PairwiseDisjoint lists₁ → (slots₂ : Set σ).PairwiseDisjoint lists₂ →
      (∀ i ∈ slots₁, ∀ k ∈ lists₁ i, ‖a₁ i k‖ ≤ 1) →
      (∀ i ∈ slots₂, ∀ k ∈ lists₂ i, ‖a₂ i k‖ ≤ 1) →
      ∀ (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0 ≤ G₁ → 0 ≤ G₂ → 0 < X₁ → 0 < X₂ → 0 < K → 0 ≤ P →
      (∀ U ∈ F.powerset, ‖C₁ U‖ ≤ G₁) → (∀ U ∈ F.powerset, ‖C₂ U‖ ≤ G₂) →
      (∀ U ∈ F.powerset, C₁ U ≠ 0 → columnLog p X₁ U ≤ M₁) →
      (∀ U ∈ F.powerset, C₂ U ≠ 0 → columnLog p X₂ U ≤ M₂) →
      ∀ d : Eis, d ≠ 0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let G₁' := (2:ℝ)^A₁.card * Cm * U₁^ε * G₁
      let G₂' := (2:ℝ)^A₂.card * Cm * U₂^ε * G₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑' h : {h : Eis // h ∉ T}, actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (markedColumn slots₁ lists₁ a₁ A₁ C₁) (markedColumn slots₂ lists₂ a₂ A₂ C₂)
        W (fun _ => 1) (fun _ => 1) X₁ X₂ K d h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*K) *
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_actualFirstKernel_disk_remainder order
  obtain ⟨Cm,hCm,hmark⟩ := markedColumn_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc F B A₁ A₂ v ε₁ ε₂ hFB
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ hl₁ hl₂ ha₁ ha₂ C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂
    hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hs₁ hs₂ d hd
  apply htail p hp hinj hcop hg hc F B v ε₁ ε₂ hFB _ _ W _ _ X₁ X₂ K P M₁ M₂
    (by positivity) (by positivity) hX₁ hX₂ hK hP
  · exact hmark p hp hcop slots₁ lists₁ a₁ hl₁ ha₁ A₁ F C₁ G₁ X₁ M₁ hG₁ hX₁ hC₁ hs₁
  · exact hmark p hp hcop slots₂ lists₂ a₂ hl₂ ha₂ A₂ F C₂ G₂ X₂ M₂ hG₂ hX₂ hC₂ hs₂
  · intro U hU hn
    exact hs₁ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · intro U hU hn
    exact hs₂ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · exact hd

end
end SevenEighths.InverseMoment

end OAI
