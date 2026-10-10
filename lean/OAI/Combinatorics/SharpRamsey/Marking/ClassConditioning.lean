import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.MarkingTwoEntropy

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped BigOperators Classical
noncomputable section
variable {Ω Γ α ι : Type*} [Fintype Ω] [Fintype Γ] [Fintype α] [Fintype ι]

omit [Fintype α] [Fintype ι] in
def Law.onContextEvent (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) : Law Ω where
  mass x := if θ x∈E then p.mass x/(p.map θ).event E else 0
  nonneg x := by
    split_ifs
    · exact div_nonneg (p.nonneg x) (le_of_lt hE)
    · exact le_refl 0
  total := by
    simp only [←sum_filter,←sum_div]
    change p.event (univ.filter (fun x=>θ x∈E))/(p.map θ).event E=1
    rw [←Law.event_map]
    exact div_self (ne_of_gt hE)

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_map_mass (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (z : Γ) :
    ((p.onContextEvent θ E hE).map θ).mass z =
      if z∈E then (p.map θ).mass z/(p.map θ).event E else 0 := by
  change (∑ x with θ x=z, if θ x∈E then p.mass x/(p.map θ).event E else 0)=_
  by_cases hz : z∈E
  · rw [ite_eq_left hz]
    change _=(∑ x with θ x=z,p.mass x)/(p.map θ).event E
    rw [sum_div]
    apply sum_congr rfl
    intro x hx
    rw [ite_eq_left (by simpa only [(mem_filter.mp hx).2] using hz)]
  · rw [ite_eq_right hz]
    apply sum_eq_zero
    intro x hx
    exact ite_eq_right (by simpa only [(mem_filter.mp hx).2] using hz)

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_support (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (x : Ω) (hx : (p.onContextEvent θ E hE).mass x≠0) :
    p.mass x≠0 ∧ θ x∈E := by
  change (if θ x∈E then p.mass x/(p.map θ).event E else 0)≠0 at hx
  split_ifs at hx with he
  · exact ⟨(div_ne_zero_iff.mp hx).1,he⟩
  · exact False.elim (hx rfl)

omit [Fintype α] [Fintype ι] in

lemma Law.onContextEvent_cond (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (z : Γ)
    (hz : ((p.onContextEvent θ E hE).map θ).mass z≠0) :
    (p.onContextEvent θ E hE).cond θ z=p.cond θ z := by
  have hm := p.onContextEvent_map_mass θ E hE z
  have hzE : z∈E := by by_contra hn; rw [hm,ite_eq_right hn] at hz; exact hz rfl
  have hp : (p.map θ).mass z≠0 := by
    rw [hm,ite_eq_left hzE] at hz
    exact (div_ne_zero_iff.mp hz).1
  ext x
  rw [Law.cond_mass _ _ _ hz,Law.cond_mass _ _ _ hp,hm,ite_eq_left hzE]
  by_cases hx : θ x=z
  · simp only [Law.onContextEvent,hx,ite_eq_left hzE,ite_true]
    field_simp
  · simp only [ite_eq_right hx,zero_div]

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_domination (p q : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (C : ℝ)
    (hC : ∀ x,p.mass x≤C*q.mass x) :
    ∀ x,(p.onContextEvent θ E hE).mass x≤(C/(p.map θ).event E)*q.mass x := by
  intro x
  have hh := div_le_div_of_nonneg_right (hC x) (le_of_lt hE)
  change (if θ x∈E then p.mass x/(p.map θ).event E else 0)≤_
  have hh' : p.mass x/(p.map θ).event E≤(C/(p.map θ).event E)*q.mass x := by
    calc
      _ ≤ (C*q.mass x)/(p.map θ).event E := hh
      _ = _ := by ring
  split_ifs
  · exact hh'
  · exact (div_nonneg (p.nonneg x) (le_of_lt hE)).trans hh'

omit [Fintype α] [Fintype ι] in
lemma Law.onContextEvent_expectation (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (g : Γ→ℝ)
    (hg : ∀ z,(p.map θ).mass z≠0→0≤g z) :
    (∑ z, ((p.onContextEvent θ E hE).map θ).mass z*g z) ≤
      (∑ z,(p.map θ).mass z*g z)/(p.map θ).event E := by
  rw [sum_div]
  apply sum_le_sum
  intro z _
  rw [p.onContextEvent_map_mass θ E hE]
  by_cases hz : z∈E
  · rw [ite_eq_left hz]
    apply le_of_eq
    ring
  · rw [ite_eq_right hz,zero_mul]
    apply div_nonneg _ (le_of_lt hE)
    by_cases hp : (p.map θ).mass z=0
    · simp [hp]
    · exact mul_nonneg ((p.map θ).nonneg z) (hg z hp)

theorem selectedDeficit_onContextEvent (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (F : Ω→ι→α) (S : Γ→Finset ι) (J : ℝ)
    (hδ : ∀ z,(p.map θ).mass z≠0→
      0≤(S z).card*J-entropy (((p.cond θ z).map F).restrict (S z))) :
    selectedDeficit (p.onContextEvent θ E hE) θ F S J≤
      selectedDeficit p θ F S J/(p.map θ).event E := by
  have he : selectedDeficit (p.onContextEvent θ E hE) θ F S J=
      ∑ z,((p.onContextEvent θ E hE).map θ).mass z*
        ((S z).card*J-entropy (((p.cond θ z).map F).restrict (S z))) := by
    apply sum_congr rfl
    intro z _
    by_cases hz : ((p.onContextEvent θ E hE).map θ).mass z=0
    · simp only [hz,zero_mul]
    · rw [p.onContextEvent_cond θ E hE z hz]
  rw [he]
  exact p.onContextEvent_expectation θ E hE _ hδ

theorem selectedDeficit_onContextEvent_le (p : Law Ω) (θ : Ω→Γ) (E : Finset Γ)
    (hE : 0<(p.map θ).event E) (F : Ω→ι→α) (S : Γ→Finset ι) (J B : ℝ)
    (hδ : ∀ z,(p.map θ).mass z≠0→
      0≤(S z).card*J-entropy (((p.cond θ z).map F).restrict (S z)))
    (hB : selectedDeficit p θ F S J≤B) :
    selectedDeficit (p.onContextEvent θ E hE) θ F S J≤B/(p.map θ).event E :=
  (selectedDeficit_onContextEvent p θ E hE F S J hδ).trans
    (div_le_div_of_nonneg_right hB hE.le)

end
end SharpLogRamsey.Selection

end

end OAI
