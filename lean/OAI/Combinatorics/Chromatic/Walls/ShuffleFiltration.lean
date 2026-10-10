import Mathlib
import OAI.Combinatorics.Chromatic.Histories.ShuffleLeafFiltration
import OAI.Combinatorics.Chromatic.QuantumTorus.ProductUnitFiltration
import OAI.Combinatorics.Chromatic.Shuffle.GridShapeFiltration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private lemma size_positive (d : I → ℕ) (hd : d≠0) : 0<∑ i,d i := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,d i≠0 := by
    by_contra h
    push Not at h
    exact hd (funext h)
  exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨i,Finset.mem_univ _,Nat.pos_of_ne_zero hi⟩

theorem shuffleBUnit_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ) :
    ShuffleFiltered a c η hc θ d e := by
  classical
  suffices H : ∀ N : ℕ,∀ d e : I → ℕ,(∑ i,(d+e) i)=N → ShuffleFiltered a c η hc θ d e from
    H _ d e rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro d e hN hdθ heθ U V f g hf hg
    by_cases hd : d=0
    · subst d
      exact shuffleBUnit_filtered_zero_left a c η hc θ e _ U V f g hf hg
    by_cases he : e=0
    · subst e
      exact shuffleBUnit_filtered_zero_right a c η hc θ d _ U V f g hf hg
    have hdθ' : slope c η d=θ := hdθ.resolve_left hd
    have heθ' : slope c η e=θ := heθ.resolve_left he
    have hde := SlopeArithmetic.add_ne_zero_left d e hd
    rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde]
    apply sourceFiltration_of_binary
    · intro t
      rw [show hdθ.compatible heθ=Or.inr (Or.inr (hdθ'.trans heθ'.symm)) from rfl,
        shuffleBUnit_eq_shuffleB]
      exact shuffleB_translation_leaf_degreeCut a c η hc θ d e hd he hdθ' heθ'
        (hχ d e hd he hdθ' heθ') U V f g
        (by rwa [unitalSourceFiltration_nonzero a c η hc θ d hd] at hf)
        (by rwa [unitalSourceFiltration_nonzero a c η hc θ e he] at hg) t
    · intro α β hα hβ hsα hsβ h
      apply restriction_shuffleBUnit_filtered a c η hc θ d e α β hα hβ hdθ' hsα hsβ _ h
      · intro d' e' h'
        apply ih (∑ i,α i) _ d' e' (by simp only [h'])
        have hp:=size_positive β hβ
        have hh : (∑ i,α i)+(∑ i,β i)=N := by
          rw [←Finset.sum_add_distrib]
          simpa only [Pi.add_apply] using (congrArg (fun x : I → ℕ=>∑ i,x i) h).trans hN
        omega
      · intro d' e' h'
        apply ih (∑ i,β i) _ d' e' (by simp only [h'])
        have hp:=size_positive α hα
        have hh : (∑ i,α i)+(∑ i,β i)=N := by
          rw [←Finset.sum_add_distrib]
          simpa only [Pi.add_apply] using (congrArg (fun x : I → ℕ=>∑ i,x i) h).trans hN
        omega
      · exact hf
      · exact hg

theorem shuffleB_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hd : d≠0) (he : e≠0) (hdθ : slope c η d=θ) (heθ : slope c η e=θ)
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) e)
    (hf : f∈sourceFiltration a c η hc θ d U) (hg : g∈sourceFiltration a c η hc θ e V) :
    shuffleB a c η hc d e (hdθ.trans heθ.symm) f g∈sourceFiltration a c η hc θ (d+e) (U+V) := by
  have h:=shuffleBUnit_filtered a c η hc θ hχ d e
    (Or.inr hdθ) (Or.inr heθ) U V f g
    (by rwa [unitalSourceFiltration_nonzero a c η hc θ d hd])
    (by rwa [unitalSourceFiltration_nonzero a c η hc θ e he])
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) (SlopeArithmetic.add_ne_zero_left d e hd)] at h
  rwa [shuffleBUnit_eq_shuffleB] at h

end ElementaryPositivity.RawShuffle

end

end OAI
