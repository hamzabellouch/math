import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCharacterRows

namespace OAI

/-! Exact finite-envelope changes for the actual stopped coefficient.
Every factor in a fibre divides its prescribed product. Thus a bounded
product uses only the smaller prime and divisor cutoffs. The selected-side
predicate is retained verbatim, including any extra restriction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedBeta_selected_congr (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected selected' : Eisenstein → Eisenstein → Prop)
    (b : Eisenstein)
    (hselected : ∀ r ∈ R, ∀ d ∈ D, r*d = b → (selected r d ↔ selected' r d)) :
    stoppedBeta R D v ψ w selected b = stoppedBeta R D v ψ w selected' b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp
  dsimp only
  rw [propext (hselected p.1 hr p.2 hd he)]

lemma primaryPairFiber_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    primaryPairFiber (primaryElementBall F) (primaryElementBall F) b =
      primaryPairFiber (primaryElementBall X) (primaryElementBall X) b := by
  ext p
  simp only [primaryPairFiber,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨hr,hd⟩,he⟩
    have hrb : p.1 ∣ b := ⟨p.2,he.symm⟩
    have hdb : p.2 ∣ b := ⟨p.1,by rw [mul_comm,he]⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (norm_le_of_dvd (primary_ne_zero hb) hrb).trans hbX⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (norm_le_of_dvd (primary_ne_zero hb) hdb).trans hbX⟩⟩,he⟩
  · rintro ⟨⟨hr,hd⟩,he⟩
    exact ⟨⟨mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hr).1,
      (mem_primaryElementBall.mp hr).2.trans hXF⟩,
      mem_primaryElementBall.mpr ⟨(mem_primaryElementBall.mp hd).1,
      (mem_primaryElementBall.mp hd).2.trans hXF⟩⟩,he⟩

lemma primeTupleFiber_restrict {X F : ℝ} (hXF : X ≤ F)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    (Fintype.piFinset (fun _ : ι => primeCutoff F)).filter (fun f => (∏ i, f i) = b) =
      (Fintype.piFinset (fun _ : ι => primeCutoff X)).filter (fun f => (∏ i, f i) = b) := by
  ext f
  simp only [Finset.mem_filter,Fintype.mem_piFinset]
  constructor
  · rintro ⟨hf,he⟩
    refine ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,?_⟩,he⟩
    have hd : f i ∣ b := he ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    exact (norm_le_of_dvd (primary_ne_zero hb) hd).trans hbX
  · rintro ⟨hf,he⟩
    exact ⟨fun i => mem_primeCutoff.mpr ⟨(mem_primeCutoff.mp (hf i)).1,
      (mem_primeCutoff.mp (hf i)).2.trans hXF⟩,he⟩

lemma distinguishedTupleCoefficient_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z b =
      distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z b := by
  unfold distinguishedTupleCoefficient orderedConvolution
  rw [primeTupleFiber_restrict hXF hb hbX]

lemma stoppedBeta_restrict_left (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop)
    (P : Eisenstein → Prop) (b : Eisenstein) :
    stoppedBeta R D (fun r => if P r then v r else 0) ψ w selected b =
      stoppedBeta R D v ψ w (fun r d => P r ∧ selected r d) b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : P p.1 <;> by_cases hs : selected p.1 p.2
  all_goals simp only [hp,hs,ite_true,ite_false,and_self,and_false,false_and,zero_mul]

lemma stoppedBeta_tuple_ball_restrict {X F : ℝ} (hXF : X ≤ F)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F) W ψ w z)
      ψ w selected b =
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  rw [primaryPairFiber_ball_restrict hXF hb hbX]
  apply Finset.sum_congr rfl
  intro p hp
  have hr := (mem_primaryElementBall.mp (Finset.mem_product.mp
    (Finset.mem_filter.mp hp).1).1)
  dsimp only
  rw [distinguishedTupleCoefficient_restrict hXF W ψ w z hr.1 hr.2]

lemma stoppedBeta_tuple_support (X : ℝ)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall X) (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b =
    stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff X))
      (primaryElementBall X)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z)
      ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_congr_of_eq_on_inter
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    have hd := (Finset.mem_product.mp hp'.1).2
    have hr : p.1 ∉ orderedConvolutionSupport (fun _ : ι => primeCutoff X) := by
      intro hr
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,hd⟩,hp'.2⟩)
    have hz : distinguishedTupleCoefficient (fun _ : ι => primeCutoff X) W ψ w z p.1 = 0 := by
      unfold distinguishedTupleCoefficient
      rw [orderedConvolution_eq_zero_of_not_mem _ _ hr,mul_zero]
    simp only [hz,zero_mul,ite_self]
  · intro p hp hn
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hr,hd⟩ := Finset.mem_product.mp hp'.1
    have hrp : primary p.1 := orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr
    have hrX : norm p.1 ≤ X :=
      (norm_le_of_dvd (primary_ne_zero hb) ⟨p.2,hp'.2.symm⟩).trans hbX
    exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_primaryElementBall.mpr ⟨hrp,hrX⟩,hd⟩,hp'.2⟩)).elim
  · intro _ _ _
    rfl

/-- The actual finite-envelope beta, with its exact selected predicate,
is the analytic row at norm twist zero on every bounded primary product. -/
theorem stoppedBeta_eq_stoppedRowCoefficient {X F : ℝ} (hXF : X ≤ F)
    (W : ι → ℝ → ℂ) (w z : ℝ)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hbX : norm b ≤ X) :
    stoppedBeta (primaryElementBall F) (primaryElementBall F)
      (distinguishedTupleCoefficient (fun _ : ι => primeCutoff F)
        (fun i p => W i (norm p)) primeDetectorCutoff w z)
      primeDetectorCutoff w selected b =
      stoppedRowCoefficient X w z 0 W selected b := by
  rw [stoppedBeta_tuple_ball_restrict hXF,stoppedBeta_tuple_support X]
  · simp only [stoppedRowCoefficient,normTwist,zero_mul,Complex.ofReal_zero,
      Complex.exp_zero,mul_one]
  all_goals assumption

end CubicFirstMoment

end

end OAI
