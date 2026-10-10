import Mathlib
import OAI.Computability.MinUncut.Search.InnerParameters

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner

lemma uniformWeight_sum {Ξ : Type*} [Fintype Ξ] (F : Ξ → ℝ) :
    (∑ ξ, (Fintype.card Ξ:ℝ)⁻¹*F ξ) = 𝔼 ξ,F ξ := by
  rw [← Finset.mul_sum,Fintype.expect_eq_sum_div_card]
  ring

attribute [local irreducible] firstError secondError thirdError atomProbability

theorem InnerParameters.decode_expect {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J)
    {Ξ : Type*} [Fintype Ξ] [Nonempty Ξ] (V A : Ξ → Type*)
    [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
    [∀ ξ, Fintype (A ξ)] (f : ∀ ξ, FoldedProof (A ξ))
    (h1 : (𝔼 ξ,firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J))
    (h2 : (𝔼 ξ,secondError (m := P.m) (n := P.n) (f ξ)
      ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)))
    (h3 : (𝔼 ξ,thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤
      J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ 𝔼 ξ,atomProbability (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J) P.θ := by
  let w := fun _ : Ξ => (Fintype.card Ξ:ℝ)⁻¹
  have hw (ξ : Ξ) : 0≤w ξ := by dsimp [w]; positivity
  have hw1 : ∑ ξ,w ξ=1 := by
    simpa only [mul_one,Fintype.expect_const] using (uniformWeight_sum (fun _ : Ξ => (1:ℝ)))
  have hh1 : (∑ ξ,w ξ*firstError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J) := by
    simpa only [w,uniformWeight_sum] using h1
  have hh2 : (∑ ξ,w ξ*secondError (m := P.m) (n := P.n) (f ξ) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤ J*(10*(sourceEta J+sourceEta J)) := by
    simpa only [w,uniformWeight_sum] using h2
  have hh3 : (∑ ξ,w ξ*thirdError (m := P.m) (n := P.n) (f ξ) (sourceSigma J) (sourceEta J)) ≤ J/(Fintype.card (Code P.m P.n):ℝ) := by
    simpa only [w,uniformWeight_sum] using h3
  simpa only [w,uniformWeight_sum] using P.decode hJ V A w hw hw1 f hh1 hh2 hh3
end MinUncut.Inner

open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S]

abbrev EdgeSamples (I S : Type*) [Fintype I] (k : ℕ) :=
  FixedSets I k × (I → S) × (I → Fin 3)

def edgeSampleSecond (equations : S → Equation Name) {k : ℕ} (e : EdgeSamples I S k) :
    I → SecondQuestion Name := secondQuestion (fun i => equations (e.2.1 i)) (hiddenSet e.1.val) e.2.2

lemma edgeSample_expect (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) :
    (𝔼 e : EdgeSamples I S k, F (fun i => equations (e.2.1 i)) (hiddenSet e.1.val) e.2.2) =
      edgeMean equations k F := by
  rw [expect_pair]
  simp_rw [expect_pair]
  rfl

theorem ProofFamily.atomTotal_lower [Nonempty S]
    (f : ProofFamily Name I) (equations : S → Equation Name) {J : ℝ} (hJ : 1≤J)
    (P : InnerParameters J) {k : ℕ} (hk : k≤Fintype.card I)
    (h1 : edgeMean equations k (fun U h pos => firstError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J)) ≤ J*(10*sourceSigma J))
    (h2 : edgeMean equations k (fun U h pos => secondError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J)) ≤
        J*(10*(sourceEta J+sourceEta J)))
    (h3 : edgeMean equations k (fun U h pos => thirdError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J)) ≤
        J/(Fintype.card (Code P.m P.n):ℝ)) :
    (P.p:ℝ) ≤ edgeMean equations k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ) := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  let A := fun e : EdgeSamples I S k => SecondAlphabet (edgeSampleSecond equations e)
  rw [← edgeSample_expect equations k (f.atomTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J) P.θ)]
  change (P.p:ℝ) ≤ 𝔼 e : EdgeSamples I S k,atomProbability (m := P.m) (n := P.n)
    (f.second (edgeSampleSecond equations e)) (sourceSigma J) (sourceEta J) P.θ
  apply P.decode_expect hJ A A (fun e => f.second (edgeSampleSecond equations e))
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => firstError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))]
    exact h1
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => secondError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) ((sourceEta J)^2/(P.m:ℝ)) (sourceSigma J) (sourceEta J))]
    exact h2
  · simp only [A,edgeSampleSecond]
    erw [edgeSample_expect equations k (fun U h pos => thirdError (m := P.m) (n := P.n)
      (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))]
    exact h3
end MinUncut.Outer

end

end OAI
