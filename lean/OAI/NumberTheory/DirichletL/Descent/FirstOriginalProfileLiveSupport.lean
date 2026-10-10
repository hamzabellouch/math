import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveCount
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
import OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def liveNormCap (L B Y : ℝ) : ℝ := max Y (max L (max (L*B^2) (B^2)))

theorem original_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K L B : ℝ)
    (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤L) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)).card≤
        (dyadIndex (liveNormCap L B Y)+1)^8 := by
  apply liveJointKeys_card_of_norm_cap
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg
    pool Q labels Y β cutoff Ψ m mark W Φ K L B hB hQ hlabels hW x hx j hn
  have hc : ∀i : Fin 6,(![L,L,L,L*B^2,B^2,Y] : Fin 6→ℝ) i≤liveNormCap L B Y := by
    intro i
    fin_cases i <;> simp [liveNormCap,le_max_iff]
  refine ⟨fun i=>⟨lt_of_lt_of_le zero_lt_one (original_source_norms_ge_one p hp pool Q labels Y x hx i),(h₁ i).trans (hc i)⟩,?_,?_⟩
  · exact ⟨primeProductNorm_pos p hp _,h₂.trans (le_max_of_le_right (le_max_left _ _))⟩
  · refine ⟨lt_of_lt_of_le zero_lt_one (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)),?_⟩
    exact h₃.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem original_twisted_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K b B X theta : ℝ)
    (hX : 0<X) (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤b) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>CompletedHeight.normTwistedSource W theta (y/X)) Φ K)).card≤
        (dyadIndex (liveNormCap (b*X) B Y)+1)^8 := by
  apply original_live_joint_card p hp hcop hg pool Q labels Y β cutoff Ψ m mark _ Φ K (b*X) B hB hQ hlabels
  intro y hy
  have hwy : W (y/X)≠0 := by
    intro hz
    exact hy (by simp [CompletedHeight.normTwistedSource,hz])
  exact (div_le_iff₀ hX).mp (hW _ hwy)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
