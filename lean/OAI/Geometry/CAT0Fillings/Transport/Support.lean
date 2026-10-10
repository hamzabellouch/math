import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Pushforward
import OAI.Geometry.CAT0Fillings.Currents.WeakMass

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X]
lemma IsMetricCurrent.coord_congr_on [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π σ : Fin n → X → ℝ}
    (hπ : ∀ i, ∃ K, LipschitzWith K (π i)) (hσ : ∀ i, ∃ K, LipschitzWith K (σ i))
    {U : Set X} (hU : IsOpen U) (hbU : Function.support b ⊆ U)
    (heq : ∀ i, EqOn (π i) (σ i) U) : T b π = T b σ := by
  classical
  let a : Fin n → lipSubmodule (X := X) := fun i => ⟨π i,hπ i⟩
  let c : Fin n → lipSubmodule (X := X) := fun i => ⟨σ i,hσ i⟩
  let M := hT.multilinear b hb
  have hd := M.map_sub_map_piecewise a c Finset.univ
  simp only [Finset.piecewise_univ,Finset.mem_univ,true_implies] at hd
  have hz : ∀ i : Fin n, M (fun j => if j < i then a j else if i=j then a j-c j else c j) = 0 := by
    intro i
    apply hT.locality b _ ⟨hb,fun j => (if j < i then a j else if i=j then a j-c j else c j).property⟩
    refine ⟨i,U,0,hU,hbU,?_⟩
    intro x hx
    simp only [lt_self_iff_false,ite_false,ite_true,Submodule.coe_sub,Pi.sub_apply,a,c]
    exact sub_eq_zero.mpr (heq i hx)
  simp only [hz,Finset.sum_const_zero] at hd
  exact sub_eq_zero.mp hd
lemma IsMetricCurrent.first_congr_support [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {K : Set X} (hK : ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0)
    {b c : X → ℝ} {π : Fin n → X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (hπ : ∀ i, ∃ L, LipschitzWith L (π i)) (heq : EqOn b c K) : T b π = T c π := by
  have hz := hK (fun x => 1*b x+(-1)*c x) π
    ⟨(hb.const_mul 1).add (hc.const_mul (-1)),hπ⟩ (fun x hx => by rw [heq hx]; ring)
  rw [hT.linearFirst b c π 1 (-1) hb hc hπ] at hz
  linarith
noncomputable def ballCutoff (o : X) (R : ℝ) (x : X) : ℝ := min 1 (max 0 (R+1-dist x o))
lemma ballCutoff_boundedLip [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) : BoundedLip (ballCutoff o R) := by
  refine ⟨⟨1,?_⟩,1,?_⟩
  · change LipschitzWith 1 (fun x => min 1 (max 0 (R+1-dist x o)))
    simpa only [zero_add] using (((LipschitzWith.const (R+1)).sub (LipschitzWith.dist_left o)).const_max 0).const_min 1
  · intro x
    rw [abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
    exact min_le_left _ _
lemma ballCutoff_one [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) {x : X} (hx : x ∈ closedBall o R) : ballCutoff o R x = 1 := by
  have hh : 1 ≤ R+1-dist x o := by have := hx; change dist x o ≤ R at this; linarith
  exact min_eq_left (hh.trans (le_max_right _ _))
lemma ballCutoff_support [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) : Function.support (ballCutoff o R) ⊆ ball o (R+1) := by
  intro x hx
  by_contra hn
  have hh : R+1-dist x o ≤ 0 := by change ¬dist x o < R+1 at hn; linarith
  exact hx (by simp [ballCutoff,max_eq_left hh])
lemma pushCurrent_eq_of_ball_support [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {K : Set X} (hK : ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0)
    (o : X) (R : ℝ) (hKR : K ⊆ closedBall o R) {P : X → X}
    (hP : LipschitzWith 1 P) (hfix : ∀ x, dist x o ≤ R+2 → P x = x) : pushCurrent P T = T := by
  funext b π
  by_cases hab : Admissible b π
  · rw [pushCurrent_apply P T hab]
    let c := fun x => ballCutoff o R x*b x
    have hc : BoundedLip c := (ballCutoff_boundedLip o R).mul hab.1
    have hπP : ∀ i, ∃ L, LipschitzWith L (π i ∘ P) := (admissible_comp hab hP).2
    calc
      T (b ∘ P) (fun i => π i ∘ P) = T c (fun i => π i ∘ P) := by
        apply hT.first_congr_support hK (boundedLip_comp hab.1 hP) hc hπP
        intro x hx
        have hxR := hKR hx
        have hfixx := hfix x (by have := hxR; change dist x o ≤ R at this; linarith)
        simp only [Function.comp_apply,hfixx,c,ballCutoff_one o R hxR,one_mul]
      _ = T c π := by
        apply hT.coord_congr_on hc hπP hab.2 (U := ball o (R+1)) isOpen_ball ?_ ?_
        · intro x hx
          apply ballCutoff_support o R
          intro hz
          exact hx (by simp only [c,hz,zero_mul])
        · intro i x hx
          rw [Function.comp_apply,hfix x (by change dist x o < R+1 at hx; linarith)]
      _ = T b π := by
        apply hT.first_congr_support hK hc hab.1 hab.2
        intro x hx
        simp only [c,ballCutoff_one o R (hKR hx),one_mul]
  · simp only [pushCurrent,ite_eq_right hab,hT.offDomain b π hab]
end CAT0Fillings
end

end OAI
