import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayMap
import OAI.Probability.Ballisticity.Walk.UpperKernel

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma hitKernel_translation {d : ℕ} (ω : Environment d) (z x : Lattice d)
    (S T U : Set (Lattice d)) :
    hitKernel ((fun y => z+y) ⁻¹' S) ((fun y => z+y) ⁻¹' T) ((fun y => ω (z+y)),x) U =
      hitKernel S T (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simp only [hitKernel_apply]
  apply tsum_congr
  intro n
  rw [←quenched_translation ω z x,
    Measure.map_apply (by fun_prop) (measurableSet_hitAt _ _ _)]
  congr 1
  ext X
  simp only [Set.mem_preimage,HitAt,Set.mem_ofPred_eq,Set.mem_inter_iff]
  simp only [add_sub_cancel]

lemma strip_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Strip ℓ (z+x) H=Strip ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Strip,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma upper_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) (H : ℝ) :
    (fun y => z+y) ⁻¹' Upper ℓ (z+x) H=Upper ℓ x H := by
  ext y
  simp only [Set.mem_preimage,Upper,Set.mem_ofPred_eq,dot_realPosition_add]
  constructor <;> intro h <;> linarith

lemma variableHitKernel_translation {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (z x : Lattice d) (U : Set (Lattice d)) :
    variableHitKernel ℓ H ((fun y => ω (z+y)),x) U =
      variableHitKernel ℓ H (ω,z+x) ((fun y => y-z) ⁻¹' U) := by
  simpa only [variableHitKernel,Kernel.coe_mk,strip_translation,upper_translation] using
    hitKernel_translation ω z x (Strip ℓ (z+x) H) (Upper ℓ (z+x) H) U

lemma horizontalProjection_add {d : ℕ} (e : Direction d) (x y : Lattice d) :
    horizontalProjection e (x+y)=horizontalProjection e x+horizontalProjection e y := by
  apply Subtype.ext
  funext j
  by_cases hj : j=e.1
  · subst j
    simp [horizontalProjection]
  · simp [horizontalProjection,Function.update_of_ne hj]

lemma horizontalProjection_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    horizontalProjection e (x-y)=horizontalProjection e x-horizontalProjection e y := by
  apply Subtype.ext
  funext j
  by_cases hj : j=e.1
  · subst j
    simp [horizontalProjection]
  · simp [horizontalProjection,Function.update_of_ne hj]

lemma horizontalLift_add {d : ℕ} (e : Direction d) (a b : ℤ) (x y : HorizontalSpace e) :
    horizontalLift e a x+horizontalLift e b y=horizontalLift e (a+b) (x+y) := by
  simp only [horizontalLift,AddSubgroup.coe_add,add_zsmul]
  abel

lemma episodeSpliced_kernel {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (X : EpisodeInput e) (i : ℤ) (m a : ℕ)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    upperHorizontalKernel e (t X.1.1 (i+m)-t X.1.1 i)
      (fun p => episodeSplicedRow e t X i m a p.1 p.2) z A =
    variableHitKernel (realPosition (step e)) (t X.1.1 (i+m)-t X.1.1 i)
      (X.1.1,horizontalLift e (t X.1.1 i) (X.1.2 (i,a)+z))
      {y | horizontalProjection e y-X.1.2 (i,a)∈A} := by
  let b := horizontalLift e (t X.1.1 i) (X.1.2 (i,a))
  let H := t X.1.1 (i+m)-t X.1.1 i
  have he : hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      (upperEnvironment e (fun p => episodeSplicedRow e t X i m a p.1 p.2),horizontalLift e 0 z)=
    hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
      ((fun y => X.1.1 (b+y)),horizontalLift e 0 z) := by
    apply hitKernel_congr
    intro y hy
    have hy0 : 0 ≤ signedHeight e y := by
      have := hy.1
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero] at this
      exact_mod_cast this
    have hyH : (signedHeight e y).toNat<H := by
      have := hy.2
      simp only [signedHeight_projection,signedHeight_horizontalLift,Int.cast_zero,zero_add] at this
      have hylt : signedHeight e y<(H:ℤ) := by exact_mod_cast this
      omega
    change episodeSplicedRow e t X i m a (signedHeight e y).toNat (horizontalProjection e y)=_
    rw [episodeSplicedRow,ite_eq_left hyH]
    simp only [Int.toNat_of_nonneg hy0]
    apply congrArg X.1.1
    calc
      _ = horizontalLift e (t X.1.1 i) (X.1.2 (i,a))+
          horizontalLift e (signedHeight e y) (horizontalProjection e y) :=
        (horizontalLift_add e _ _ _ _).symm
      _ = b+y := by rw [horizontalLift_projection]
  rw [upperHorizontalKernel_apply,he]
  change variableHitKernel (realPosition (step e)) H ((fun y => X.1.1 (b+y)),horizontalLift e 0 z)
    (horizontalProjection e ⁻¹' A)=_
  rw [variableHitKernel_translation]
  dsimp only [b]
  rw [horizontalLift_add,add_zero]
  congr 1
  ext y
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,horizontalProjection_sub,horizontalProjection_lift]

end DirectionalTransience

end

end OAI
