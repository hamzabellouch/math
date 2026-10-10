import OAI.NumberTheory.DirichletL.Detector.LowInverseEnergy
import OAI.NumberTheory.DirichletL.Detector.LowActualEnergies

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowElementRowPoint (m : O) : Oˣ×Id :=
  (InitialMeanSquare.sourceLabelUnit m,Ideal.span {m})

def lowIdealRowElement (p : Oˣ×Id) : O := p.1.val*idealGenerator p.2

lemma lowIdealRowElement_point (m : O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (InitialMeanSquare.sourceLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

lemma lowIdealRowElement_span (p : Oˣ×Id) : Ideal.span {lowIdealRowElement p}=p.2 := by
  rw [lowIdealRowElement,Ideal.span_singleton_mul_left_unit p.1.isUnit,span_idealGenerator]

lemma lowElementRowPoint_element (p : Oˣ×Id) (hp : p.2≠0) :
    lowElementRowPoint (lowIdealRowElement p)=p := by
  apply Prod.ext
  · apply Units.ext
    have hh := InitialMeanSquare.sourceLabelUnit_spec (lowIdealRowElement p)
    rw [lowIdealRowElement_span] at hh
    exact (mul_right_cancel₀ (idealGenerator_ne_zero p.2 hp) hh).symm
  · exact lowIdealRowElement_span p

lemma lowIdealRowElement_norm (p : Oˣ×Id) :
    elementNorm (lowIdealRowElement p)=(Ideal.absNorm p.2:ℝ) := by
  unfold elementNorm
  rw [lowIdealRowElement_span]

def lowIdealRows (R : Finset O) : Finset Id := R.image (fun m=>Ideal.span {m})

lemma lowIdealRows_nonzero (R : Finset O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (hR m hm)

lemma lowIdealRows_norm_bound (R : Finset O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem sum_low_element_rows (R : Finset O) (hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,F m)=∑u : Oˣ,∑I∈lowIdealRows R,
      if u.val*idealGenerator I∈R then F (u.val*idealGenerator I) else 0 := by
  let P := (Finset.univ×ˢlowIdealRows R).filter (fun p : Oˣ×Id=>lowIdealRowElement p∈R)
  have he : (∑m∈R,F m)=∑p∈P,F (lowIdealRowElement p) := by
    apply Finset.sum_bij (fun m hm=>lowElementRowPoint m)
    · intro m hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
      · rwa [lowIdealRowElement_point]
    · intro m hm n hn he
      exact lowElementRowPoint_injective he
    · intro p hp
      obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
      refine ⟨lowIdealRowElement p,hpr,?_⟩
      exact lowElementRowPoint_element p (lowIdealRows_nonzero R hR _ (Finset.mem_product.mp hp).2)
    · intro m hm
      rw [lowIdealRowElement_point]
  rw [he]
  dsimp only [P]
  rw [Finset.sum_filter,Finset.sum_product]
  rfl

theorem low_element_energy_le_units (R : Finset O) (_hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : Oˣ,∑I∈lowIdealRows R,‖F (u.val*idealGenerator I)‖^2 := by
  let P : Finset (Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=>lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=>sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : O→*ℂ) (m : O) (u : Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id))
        (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I) := by
  have he : (InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (InitialMeanSquare.sourceLabelUnit_spec (1:O)).symm
  have harg : m^6*(idealGenerator (1:Id))^4*
      (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I)=m^6*1^4*(u.val*idealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id))^4*(u.val*idealGenerator I) := by ring
      _=_ := by rw [he];ring
  unfold CanonicalRowCompletion.rowTwist
  rw [harg]

lemma low_units_label_one_sum (F : (O→*ℂ)→ℝ) (Ψ : O→*ℂ) (m : O) (I : Id) :
    (∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)))=
      ∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((InitialMeanSquare.sourceLabelUnit (1:O))^4))
    (fun u : Oˣ=>F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset O) (hR : ∀z∈R,z≠0)
    (Ψ : O→*ℂ) (m : O) (F : (O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=>F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

theorem lowSelectedInverseRow_ideal_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (X t : ℝ) (σ : RayFourExpansion.RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow F c η S hS D X t σ z‖^2)≤
      lowCorrectionEnergy*∑χ : RayFourExpansion.RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator (idealGenerator (1:Id)) (u.val*idealGenerator I))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  apply (lowSelectedInverseRow_energy F c η S hS D X t σ R).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (calibrationForSet S hS).generator (fun Ψ=>∑k∈F,c k*InverseMoment.markedCompletedT Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X (fun A=>if D k∣A then (1:ℂ) else 0))

lemma low_unit_card : Fintype.card Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end SevenEighths.ProbePhysical
end

end OAI
