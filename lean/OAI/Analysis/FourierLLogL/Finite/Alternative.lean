import OAI.Analysis.FourierLLogL.Finite.Mixture
/-! # Finite-dimensional separation for laws -/
open Set Function Filter
open scoped BigOperators

noncomputable section
namespace OAI

namespace FourierLLogL.Law
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} [Fintype α] [Fintype β] [Fintype γ]

lemma continuous_pdf (a : α) : Continuous (fun P : Law α => P a) :=
  (continuous_apply a).comp continuous_subtype_val

lemma continuous_entropy : Continuous (fun P : Law α => P.entropy) := by
  simp only [entropy_formula]
  exact continuous_finsetSum _ fun x _ => Real.continuous_negMulLog.comp (continuous_pdf _)

lemma continuous_Ex (f : α → ℝ) : Continuous (fun P : Law α => P.Ex f) :=
  continuous_finsetSum _ fun a _ => (continuous_pdf a).mul continuous_const

lemma continuous_prob (p : α → Prop) : Continuous (fun P : Law α => P.prob p) :=
  continuous_Ex _

lemma continuous_send_pdf (X : α → β) (b : β) : Continuous (fun P : Law α => P.send X b) := by
  simp_rw [send_apply]; exact continuous_prob _

lemma continuous_send (X : α → β) : Continuous (fun P : Law α => P.send X) := by
  refine Continuous.subtype_mk (p:=(fun f : β → ℝ => (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1)) ?_ _
  exact continuous_pi (fun x => continuous_send_pdf X x)

lemma continuous_H (X : α → β) : Continuous (fun P : Law α => P.H X) :=
  continuous_entropy.comp (continuous_send X)

lemma continuous_Hcond (X : α → β) (Z : α → γ) : Continuous (fun P : Law α => P.Hcond X Z) :=
  (continuous_H _).sub (continuous_H _)

/-- Convex minimization over finite distributions with a linear constraint g=0:
    if any dual objective (arbitrary multipliers) is at most C somewhere,
    there is a constrained law with value at most C. -/
lemma primal_feasible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Law α → ℝ) (hf : Continuous f)
    (g : Law α → E) (hg : Continuous g)
    (hfc : ∀ P Q t h0 h1, f (mixture P Q t h0 h1) ≤ t*f P+(1-t)*f Q)
    (hgc : ∀ P Q t h0 h1, g (mixture P Q t h0 h1) = t • g P+(1-t) • g Q)
    (hP : ∃ P, g P = 0)
    (C : ℝ) (hC : ∀ L : E →L[ℝ] ℝ, ∃ P, f P + L (g P) ≤ C) :
    ∃ P, f P ≤ C ∧ g P = 0 := by
  classical
  let K : Set (E×ℝ) := {x | ∃ P, g P = x.1 ∧ f P ≤ x.2}
  let S : Set ((Law α)×(E×ℝ)) := {z | g z.1 = z.2.1} ∩ {z | f z.1 ≤ z.2.2}
  have hK : K = Prod.snd '' S := by
    ext
    simp [K,S]
  have hs : IsClosed S :=
    (isClosed_eq (hg.comp continuous_fst) continuous_snd.fst).inter
      (isClosed_le (hf.comp continuous_fst) continuous_snd.snd)
  have hkc : IsClosed K := hK ▸ isClosedMap_snd_of_compactSpace _ hs
  have hkv : Convex ℝ K := by
    rintro x ⟨P,h1,h2⟩ y ⟨Q,h3,h4⟩ a b ha hb hab
    have ha' : a ≤ 1 := by linarith
    refine ⟨mixture P Q a ha ha',?_ ,?_⟩
    · rw [hgc,h1,h3,show 1-a=b by linarith]
      rfl
    · change _ ≤ a*x.2+b*y.2
      exact (hfc P Q a ha ha').trans (by rw [show 1-a=b by linarith]; gcongr)
  suffices H : (0,C) ∈ K by
    obtain ⟨P,hp,hq⟩ := H; exact ⟨P,hq,hp⟩
  by_contra hk
  obtain ⟨L,r,ha,hb⟩ := geometric_hahn_banach_point_closed hkv hkc hk
  let l := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let m := L (0,1)
  have hl (x : E) (t : ℝ) : L (x,t) = l x + t*m := by
    have heq : (x,t) = (x,(0:ℝ))+t • ((0:E),(1:ℝ)) := by simp
    rw [heq,map_add,map_smul]; rfl
  have hA : C*m < r := by simpa [hl] using ha
  have hB (P : Law α) : r < l (g P) + f P*m := hl _ _ ▸ hb (g P,f P) ⟨P,rfl,le_refl _⟩
  obtain ⟨P,hgp⟩ := hP
  have hc : C < f P := lt_of_not_ge (fun hh => hk ⟨P,hgp,hh⟩)
  have hm : 0 < m := by
    have hh := hB P
    rw [hgp,map_zero] at hh
    nlinarith
  obtain ⟨Q,hQ⟩ := hC (m⁻¹ • l)
  change f Q + m⁻¹ * l (g Q) ≤ C at hQ
  have HH := mul_le_mul_of_nonneg_right hQ hm.le
  rw [add_mul, mul_comm (m⁻¹ * _), ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at HH
  linarith [hB Q]

end FourierLLogL.Law

end OAI
