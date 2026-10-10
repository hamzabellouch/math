import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section FunctionalCoercive
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma functional_rank_one_positive
    {L V:E →L[ℝ] E →L[ℝ] ℝ} {f g:E →L[ℝ] ℝ} {e:E} {β m γ:ℝ}
    (hLs:∀d e,L d e=L e d) (hL:∀d,0 ≤ L d d)
    (hV:∀d,d≠0 → 0 < V d d)
    (hVL:∀d,V d d ≤ L d d+β*(f d)^2)
    (hker:∀d,L e d=0) (hf:f e≠0) (hg:g e≠0)
    (hm:0 < m) (hγ:0 < γ) :
    ∀d:E,d≠0 → 0 < m*L d d+γ*(g d)^2 := by
  intro d hd
  have hnon:0 ≤ m*L d d+γ*(g d)^2:=
    add_nonneg (mul_nonneg hm.le (hL d)) (mul_nonneg hγ.le (sq_nonneg _))
  by_contra H
  have hz:m*L d d+γ*(g d)^2=0:=le_antisymm (not_lt.mp H) hnon
  have hLd:L d d=0:=by
    have :m*L d d=0:=by nlinarith only [hz,mul_nonneg hm.le (hL d),mul_nonneg hγ.le (sq_nonneg (g d))]
    exact (mul_eq_zero.mp this).resolve_left hm.ne'
  have hgd:g d=0:=by
    have :γ*(g d)^2=0:=by rw [hLd,mul_zero,zero_add] at hz; exact hz
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hγ.ne')
  let a:=f d/f e
  let w:=d-a • e
  have hfw:f w=0:=by
    dsimp only [w,a]
    rw [map_sub,map_smul,smul_eq_mul,div_mul_cancel₀ _ hf,sub_self]
  have hLw:L w w=0:=by
    dsimp only [w]
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      smul_eq_mul,hker,hLs d e,hLd,mul_zero,sub_zero]
  have hw:w=0:=by
    by_contra hw
    have H:=hVL w
    rw [hfw,hLw,pow_two,mul_zero,mul_zero,add_zero] at H
    exact (not_lt_of_ge H) (hV w hw)
  have hdw:d=a • e:=sub_eq_zero.mp hw
  have ha:a=0:=by
    rw [hdw,map_smul,smul_eq_mul] at hgd
    exact (mul_eq_zero.mp hgd).resolve_right hg
  exact hd (by rw [hdw,ha,zero_smul])
end FunctionalCoercive
end WeakMTWTransport

end
end

end OAI
