import Mathlib
import OAI.Analysis.HardSphere.Allocation.CertificateMeasurable

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital FreeVisits
attribute [local instance] Classical.propDecidable

lemma certificate_trial_geometry {N K m : ℕ} [Nontrivial (Fin N)] {L : Length}
    (hL : 50 < L.val) (q : ℕ) (r R C S s₀ ell θ H D : ℝ) (hs₀ : 0 ≤ s₀)
    (u : Time) (v : Fin 3→Fin K) (c : Point) (hc : projectPoint L c=gridCenter L v)
    (ω : ConfigurationPath N L) (cert : Certificate q r R C S s₀ ell θ H D u v ω)
    (label : Fin m→Fin N) (hinj : Function.Injective label)
    (hel : ∀i,Eligible q r R C S s₀ u v (label i) ω) (hiso : r+2*S < s₀) :
    ∃y z : Fin m→Point,
      (∀i,projectPoint L (y i)=ω 0 (label i)) ∧
      (∀i,projectPoint L (z i)=ω 1 (label i)) ∧
      (∀i,‖y i-c‖ ≤ 3) ∧ (∀i,‖z i-c‖ ≤ 3) ∧
      (∀i j,i≠j → s₀^2 ≤ square (y i-y j)) ∧
      (∀i j,i≠j → s₀^2 ≤ square (z i-z j)) ∧
      ((visitors (gridCenter L v) ω).card:ℝ) ≤ H*D ∧
      (∀j∈visitors (gridCenter L v) ω,Regular q r R C u S (onePathAt j ω)) ∧
      (∀j∈visitors (gridCenter L v) ω,∀i,j≠label i →
        r+2*S < torusDistance L (projectPoint L (y i)) (onePathAt j ω 0 0)) ∧
      (∀j∈visitors (gridCenter L v) ω,∀i,j≠label i →
        r+2*S < torusDistance L (projectPoint L (z i)) (onePathAt j ω 1 0)) ∧
      (∀j,j∉visitors (gridCenter L v) ω → ∀s,
        12 < torusDistance L (onePathAt j ω s 0) (projectPoint L c)) := by
  choose f hf hfY hfZ hfC using (fun i ↦ eligible_near_lift hL q r R C S s₀ u v c hc (label i) ω (hel i))
  have hp (i : Fin m) (s : Time) : projectPoint L (f i s)=ω s (label i) :=
    congrArg (fun g : ConfigurationPath 1 L ↦ g s 0) (hf i)
  refine ⟨(fun i ↦ f i 0),(fun i ↦ f i 1),(fun i ↦ hp i 0),(fun i ↦ hp i 1),
    (fun i ↦ (hfY i).trans (by norm_num)),hfZ,?_,?_,cert.visit,?_,?_,?_,?_⟩
  · intro i j hij
    have hji : label j≠label i := by intro hh; exact hij (hinj hh.symm)
    have hd := ((hel i).1.2.2 (label j) hji).1
    have hh := projection_square_distance L (f i 0) (f j 0)
    rw [hp,hp] at hh
    exact (pow_le_pow_left₀ hs₀ hd.le 2).trans hh
  · intro i j hij
    have hji : label j≠label i := by intro hh; exact hij (hinj hh.symm)
    have hd := ((hel i).1.2.2 (label j) hji).2
    have hh := projection_square_distance L (f i 1) (f j 1)
    rw [hp,hp] at hh
    exact (pow_le_pow_left₀ hs₀ hd.le 2).trans hh
  · intro j hj
    exact cert.regular j (Finset.mem_filter.mp hj).2
  · intro j _ i hji
    rw [hp]
    exact hiso.trans ((hel i).1.2.2 j hji).1
  · intro j _ i hji
    rw [hp]
    exact hiso.trans ((hel i).1.2.2 j hji).2
  · intro j hj s
    rw [hc]
    by_contra! hh
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨s,hh⟩⟩)

lemma eligible_in_visitors {N K : ℕ} {L : Length}
    (q : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3→Fin K)
    (ω : ConfigurationPath N L) {i : Fin N} (hi : Eligible q r R C S s₀ u v i ω) :
    i∈visitors (gridCenter L v) ω := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,⟨0,?_⟩⟩
  have hh := centeredCell_distance hi.1.1
  linarith

lemma eligible_list_size {N K m : ℕ} [Nontrivial (Fin N)] {L : Length}
    (q : ℕ) (r R C S s₀ ell θ H D : ℝ) (hD : 0 ≤ D) (hθ : θ ≤ ell/6)
    (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath N L)
    (cert : Certificate q r R C S s₀ ell θ H D u v ω)
    (label : Fin m→Fin N) (hinj : Function.Injective label)
    (himage : Finset.univ.image label=eligibleList q r R C S s₀ u v ω) :
    ell*D/2 ≤ (m:ℝ) ∧ (m:ℝ) ≤ H*D ∧
      ∀i,Eligible q r R C S s₀ u v (label i) ω := by
  have hel (i : Fin m) : Eligible q r R C S s₀ u v (label i) ω := by
    apply (Finset.mem_filter.mp (show label i∈eligibleList q r R C S s₀ u v ω from ?_)).2
    rw [←himage]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hcard : (eligibleList q r R C S s₀ u v ω).card=m := by
    rw [←himage,Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  have hlo := certificate_eligible_count q r R C S s₀ ell θ H D u v ω cert
  rw [hcard] at hlo
  have hsub : eligibleList q r R C S s₀ u v ω⊆visitors (gridCenter L v) ω := by
    intro i hi
    exact eligible_in_visitors q r R C S s₀ u v ω (Finset.mem_filter.mp hi).2
  have hhi := Finset.card_le_card hsub
  rw [hcard] at hhi
  have hhi' : (m:ℝ) ≤ ((visitors (gridCenter L v) ω).card:ℝ) := by exact_mod_cast hhi
  refine ⟨?_,hhi'.trans cert.visit,hel⟩
  have hh := mul_le_mul_of_nonneg_right hθ hD
  nlinarith

end HardSphere.Groups

end
end

end

end OAI
