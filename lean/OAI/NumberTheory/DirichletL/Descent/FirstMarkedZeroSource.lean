import OAI.NumberTheory.DirichletL.Descent.FirstZeroSource
import OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_marked_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (coeff:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ)
      (extra₁ extra₂ : CubeCoordinates ι→Finset ι)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖coeff b D I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,coeff b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W K‖≤
      C*B^(1+ε)*L*F*Γ*((B^2*L)^ε)^2*(G₁*G₂ * |K| * ‖paperRadialFourier W 0‖) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_variable_first_zero_bound ε hε
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cz*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    test₁ test₂ extra₁ extra₂ slots lists a W Γ G₁ G₂ L K B F
    hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff hslots ha
    he₁ he₂ htest₁ htest₂ hs₁ hs₂
  have hB0 : 0≤B := le_trans zero_le_one hB
  have hextra (extra : CubeCoordinates ι→Finset ι) (he : ∀b∈bs,extra b⊆b.support)
      (b : CubeCoordinates ι) (hb : b∈bs) : primeProductNorm p (extra b)≤B^2 :=
    (primeProductNorm_mono p hp (he b hb)).trans (cube_whole_support_dyad p hp b B hB0 (hb₁ b hb) (hb₂ b hb))
  have ht₁ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₁ b∪U)*test₁ b U‖≤Cm*(B^2*L)^ε*G₁ :=
    hmark p hp hcop slots lists a hslots ha (extra₁ b) (test₁ b) (B^2) G₁ L
      (sq_nonneg _) hG₁ hL.le (hextra extra₁ he₁ b hb) (htest₁ b hb) (hs₁ b hb)
  have ht₂ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₂ b∪U)*test₂ b U‖≤Cm*(B^2*L)^ε*G₂ :=
    hmark p hp hcop slots lists a hslots ha (extra₂ b) (test₂ b) (B^2) G₂ L
      (sq_nonneg _) hG₂ hL.le (hextra extra₂ he₂ b hb) (htest₂ b hb) (hs₂ b hb)
  have hh := hzero p hp hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W
    Γ (Cm*(B^2*L)^ε*G₁) (Cm*(B^2*L)^ε*G₂) L K B F
    hΓ (by positivity) (by positivity) hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff ht₁ ht₂
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2)
  exact hh.trans_eq (by ring)

end SevenEighths.InverseMoment

end

end OAI
