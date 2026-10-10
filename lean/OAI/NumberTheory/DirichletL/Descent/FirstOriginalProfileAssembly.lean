import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCells

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coefficient (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (negative : Bool)
    (x : OriginalIndex ι) : Finset ι→ℂ :=
  firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 negative Ψ m (divisorElement p x.1)
    (mark (if negative then x.1.1.rightExponent else x.1.1.leftExponent)) x.2

def weight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (x : OriginalIndex ι) : ℂ :=
  retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
    (divisorElement p x.1) (firstOriginalWeight p β R x.1) x.2

def sourceSummand (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) : ℂ :=
  weight p hp hcop hg β R Ψ m x *
    firstCommonWeight p hg (coefficient p hp hcop hg Ψ m mark true x)
      (coefficient p hp hcop hg Ψ m mark false x) x.2.2 j *
    firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)

theorem original_retained_sum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y,
        ∑j∈firstCommonIndices pool,sourceSummand p hp hcop hg β R Ψ m mark W Φ K x j := by
  have hleft : s 0*s 2*s 5*s 7≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))
  simp only [originalRetainedFamily,firstFamilyPhysicalRows,firstBlockedPhysicalRows,
    Finset.mul_sum,sourceSummand,weight,coefficient,leftNorm,rightNorm,commonNorm,activeNorm,divisorElement,
    Bool.false_eq_true,ite_true,ite_false,one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hleft,mul_div_cancel₀ _ hright]
  ring

theorem original_retained_cell_partition (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β R Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑k∈sourceKeys (originalNorms p) source,∑l∈liveCommonKeys p pool source (fun _ _=>1) term,
        ∑x∈sourceCell (originalNorms p) source k,∑j∈firstCommonIndices pool,
          commonSelector p (fun _=>1) l j.2.1*term x j := by
  intro source term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s hs]
  simpa only [one_mul] using original_live_signed_partition p pool source (originalNorms p) (fun _ _=>1) term

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
