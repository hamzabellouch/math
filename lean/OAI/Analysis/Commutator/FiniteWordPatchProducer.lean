import Mathlib
import OAI.Analysis.Commutator.BoundedWordPool
import OAI.Analysis.Commutator.CornerCenteredEstimates
import OAI.Analysis.Commutator.PartialUnitaryWords
import OAI.Analysis.Commutator.RelativeCornerPhase
import OAI.Analysis.Commutator.RelativeCornerQuantization

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {ι : ℕ → Type*} [∀ n,Fintype (ι n)] [∀ n,LinearOrder (ι n)]
  [∀ n,Nonempty (ι n)]

variable (stage : ∀ n,Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range)

include hRM hτ hmono in
theorem exists_finite_word_patch {J K : Type*} [Fintype J] [Fintype K]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (ι n) (ι n) ℂ),stage n a*b=b*stage n a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R)
    (x : J → M) (k : K → ℤ) (hk : ∀ i,k i≠0)
    (v : PartialUnitary M) (hvR : (v.support : H →L[ℂ] H)∈R)
    (hrest : 0<(τ (1-v.support)).re) (N : ℕ) {δ ζ : ℝ} (hδ : 0<δ) (hζ : 0<ζ) :
    ∃ w : PartialUnitary M, (w.val : H →L[ℂ] H)∈R ∧
      (w.support : H →L[ℂ] H)∈R ∧ w.support ≤ 1-v.support ∧
      v.support*w.support=0 ∧ 0<(τ w.support).re ∧ (τ w.support).re<ζ ∧
      (∀ i,‖τ (w.power (k i))‖ ≤ δ*(τ w.support).re) ∧
      (∀ (s : List (Letter J K)) (j : J),s.length ≤ N →
        TracialL2.norm τ (w.support*cornerCenter τ (1-v.support)
          (word x k v s*x j)*w.support)^2 ≤ δ^2*(τ w.support).re) ∧
      (∀ (s t : List (Letter J K)) (j : J) (i : K),s.length ≤ N → t.length ≤ N →
        ‖τ (w.power (k i)*(word x k v t*word x k v s*x j))‖ ≤ δ*(τ w.support).re) := by
  classical
  let L := SmallList (Letter J K) N
  let c : L×J → M := fun a => cornerCenter τ (1-v.support) (word x k v a.1.val*x a.2)
  have hpR : ((1-v.support:M) : H →L[ℂ] H)∈R := R.sub_mem R.one_mem hvR
  obtain ⟨q,hqR,hq,hqp,hqt,hqζ,hsmall⟩ :=
    RelativeCornerQuantization.exists_relative_centered_compression M τ hτ stage hmono
      hnormal hfaith hone hirr hgrow R hstage (1-v.support) hpR v.projection.one_sub hrest
      c (fun a => cornerCenter_trace τ hτ v.projection.one_sub hrest _)
      (fun a => cornerCenter_left τ v.projection.one_sub _)
      (fun a => cornerCenter_right τ v.projection.one_sub _) hδ hζ
  let a : Option (L×L×J)×K → M := fun i => match i.1 with
    | none => 1
    | some t => word x k v t.2.1.val*word x k v t.1.val*x t.2.2
  obtain ⟨w,hwq,hphase,hwR⟩ := CornerPhase.exists_relative_signed_phase M R hRM τ hτ
    hnormal hfaith hdiffuse q hq hqR hqt a (fun i => k i.2) (fun i => hk i.2) hδ
  have horth : v.support*w.support=0 := by
    rw [hwq]
    have hh := (hq.le_iff_mul_eq_right v.projection.one_sub).mp hqp
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  refine ⟨w,hwR,by simpa only [hwq] using hqR,by simpa only [hwq] using hqp,
    horth,by simpa only [hwq] using hqt,by simpa only [hwq] using hqζ,?_,?_,?_⟩
  · intro i
    have hh := (hphase (none,i)).le
    simpa only [a,mul_one,hwq] using hh
  · intro s j hs
    have hh := (hsmall (smallList (Letter J K) s hs,j)).le
    simpa only [c,smallList,hwq] using hh
  · intro s t j i hs ht
    have hh := (hphase (some (smallList (Letter J K) s hs,smallList (Letter J K) t ht,j),i)).le
    simpa only [a,smallList,hwq] using hh

end Kadison.FinitePatching

end

end
end

end OAI
