import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D]

lemma commute_posPart_left {a b : D} (h : Commute a b) : Commute a⁺ b := h.cfcₙ_real _
lemma commute_negPart_left {a b : D} (h : Commute a b) : Commute a⁻ b := h.cfcₙ_real _
lemma commute_posPart_right {a b : D} (h : Commute a b) : Commute a b⁺ := (commute_posPart_left h.symm).symm
lemma commute_negPart_right {a b : D} (h : Commute a b) : Commute a b⁻ := (commute_negPart_left h.symm).symm

namespace PositiveQuasitrace
variable [PartialOrder D] [StarOrderedRing D]
variable (T : PositiveQuasitrace D)

def selfAdjointValue (a : selfAdjoint D) : ℝ :=
  T ⟨a.1⁺,CFC.posPart_nonneg _⟩ - T ⟨a.1⁻,CFC.negPart_nonneg _⟩

lemma selfAdjointValue_sub (a : selfAdjoint D) (p q : Positive D)
    (hpq : a.1 = p.1-q.1) (hcomm : Commute p.1 q.1) :
    T.selfAdjointValue a = T p-T q := by
  have hb : Positive.add ⟨a.1⁺,CFC.posPart_nonneg _⟩ q =
      Positive.add p ⟨a.1⁻,CFC.negPart_nonneg _⟩ := by
    apply Subtype.ext
    exact sub_eq_sub_iff_add_eq_add.mp ((CFC.posPart_sub_negPart a.1 a.2).trans hpq)
  have haq : Commute a.1 q.1 := by rw [hpq]; exact hcomm.sub_left (Commute.refl _)
  have hap : Commute a.1 p.1 := by rw [hpq]; exact (Commute.refl _).sub_left hcomm.symm
  have hv := congrArg T.toFun hb
  rw [T.map_add_commute _ _ (commute_posPart_left haq),
    T.map_add_commute _ _ (commute_negPart_left hap).symm] at hv
  unfold selfAdjointValue
  linarith

lemma selfAdjointValue_add (a b : selfAdjoint D) (h : Commute a.1 b.1) :
    T.selfAdjointValue (a+b) = T.selfAdjointValue a+T.selfAdjointValue b := by
  let p := Positive.add (⟨a.1⁺,CFC.posPart_nonneg _⟩ : Positive D) ⟨b.1⁺,CFC.posPart_nonneg _⟩
  let q := Positive.add (⟨a.1⁻,CFC.negPart_nonneg _⟩ : Positive D) ⟨b.1⁻,CFC.negPart_nonneg _⟩
  have hrep : (a+b).1 = p.1-q.1 := by
    change a.1+b.1 = (a.1⁺+b.1⁺)-(a.1⁻+b.1⁻)
    rw [add_sub_add_comm,CFC.posPart_sub_negPart _ a.2,CFC.posPart_sub_negPart _ b.2]
  have hpq : Commute p.1 q.1 :=
    ((commute_negPart_right (commute_posPart_left (Commute.refl a.1))).add_right
      (commute_negPart_right (commute_posPart_left h))).add_left
    ((commute_negPart_right (commute_posPart_left h.symm)).add_right
      (commute_negPart_right (commute_posPart_left (Commute.refl b.1))))
  rw [T.selfAdjointValue_sub (a+b) p q hrep hpq]
  dsimp [p,q]
  rw [T.map_add_commute _ _ (commute_posPart_right (commute_posPart_left h)),
    T.map_add_commute _ _ (commute_negPart_right (commute_negPart_left h))]
  unfold selfAdjointValue
  ring

lemma selfAdjointValue_smul_nonneg (r : ℝ≥0) (a : selfAdjoint D) :
    T.selfAdjointValue ((r : ℝ) • a) = (r : ℝ)*T.selfAdjointValue a := by
  have he := T.selfAdjointValue_sub ((r : ℝ) • a)
    (Positive.smul r ⟨a.1⁺,CFC.posPart_nonneg _⟩)
    (Positive.smul r ⟨a.1⁻,CFC.negPart_nonneg _⟩) (by
      change (r : ℝ) • a.1 = (r : ℝ) • a.1⁺-(r : ℝ) • a.1⁻
      rw [← smul_sub,CFC.posPart_sub_negPart _ a.2])
    (((commute_negPart_right (commute_posPart_left (Commute.refl a.1))).smul_left (r : ℝ)).smul_right (r : ℝ))
  rw [he,T.map_smul,T.map_smul]
  unfold selfAdjointValue
  ring

lemma selfAdjointValue_neg (a : selfAdjoint D) : T.selfAdjointValue (-a) = -T.selfAdjointValue a := by
  unfold selfAdjointValue
  change T ⟨(-a.1)⁺,_⟩-T ⟨(-a.1)⁻,_⟩ = -(T ⟨a.1⁺,_⟩-T ⟨a.1⁻,_⟩)
  simp only [CFC.posPart_neg,CFC.negPart_neg]
  ring

lemma selfAdjointValue_smul (r : ℝ) (a : selfAdjoint D) :
    T.selfAdjointValue (r • a) = r*T.selfAdjointValue a := by
  by_cases hr : 0 ≤ r
  · exact T.selfAdjointValue_smul_nonneg ⟨r,hr⟩ a
  · have he := T.selfAdjointValue_smul_nonneg ⟨-r,by linarith⟩ a
    change T.selfAdjointValue ((-r) • a) = (-r)*T.selfAdjointValue a at he
    rw [neg_smul,T.selfAdjointValue_neg] at he
    linarith

lemma selfAdjointValue_positive (a : Positive D) :
    T.selfAdjointValue ⟨a.1,a.2.isSelfAdjoint⟩ = T a := by
  have he := T.selfAdjointValue_sub ⟨a.1,a.2.isSelfAdjoint⟩ a Positive.zero
    (by simp [Positive.zero]) (Commute.zero_right _)
  simpa only [T.map_zero,sub_zero] using he

lemma selfAdjointValue_zero : T.selfAdjointValue 0 = 0 := by
  exact (T.selfAdjointValue_positive Positive.zero).trans T.map_zero
end PositiveQuasitrace
end CuntzPureness

end

end OAI
