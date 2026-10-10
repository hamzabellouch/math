import OAI.NumberTheory.DirichletL.Descent.FirstMarkedZeroSource
import OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_reopened_marked_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (W:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Γ G L K B F:ℝ),
      0≤Γ → 0≤G → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ u‖≤1) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖W (primeProductNorm p U)‖≤G) →
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤L) →
      ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ K)‖≤
      C*B^(1+ε)*L*F*Γ^2*((B^2*L)^ε)^2*(G^2*|K| *‖paperRadialFourier Φ 0‖) := by
  obtain ⟨C,hC,he⟩ := full_marked_first_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G L K B F
    hΓ hG hL hB hF hΨ hQ hn hFlabels hβ hslots ha hW hs
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hcoeff := reopenedPairCoefficient_bound Q labels β Γ hΓ hβ
  have hh := he p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (fun _ U=>W (primeProductNorm p U))
    (fun _ U=>W (primeProductNorm p U))
    (fun b=>b.rightExponent.support) (fun b=>b.leftExponent.support)
    slots lists a Φ (Γ^2) G G L K B F (sq_nonneg _) hG hG hL hB hF hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun b hb'=> (hb b hb').1) (fun b hb'=> (hb b hb').2)
    hn hFlabels (fun b hb C hC I hI=>hcoeff b hb C I hI) hslots ha
    (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hs) (fun _ _=>hs)
  simpa only [reopenedPhysicalSourceSum,Finset.union_comm,pow_two] using hh

end SevenEighths.InverseMoment

end

end OAI
