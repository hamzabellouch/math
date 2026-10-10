import Mathlib
import OAI.Analysis.Commutator.ProjectionChains

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.DiffuseProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def HasNoMinimalProjections (M : VonNeumannAlgebra H) : Prop :=
  ∀ p∈M, IsStarProjection p → p≠0 →
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≠p ∧ q≤p

variable (M : VonNeumannAlgebra H) (τ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)

variable (hM : HasNoMinimalProjections M)

include hM

lemma exists_half {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) :
    ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re≤(τ p).re/2 := by
  obtain ⟨q,hqM,hq,hqn,hqp,hqle⟩ := hM p hpM hp hpn
  by_cases hsmall : (τ q).re≤(τ p).re/2
  · exact ⟨q,hqM,hq,hqn,hqle,hsmall⟩
  · have hr : IsStarProjection (p-q) := hq.sub_of_mul_eq_left hp
      ((hq.le_iff_mul_eq_left hp).mp hqle)
    refine ⟨p-q,M.sub_mem hpM hqM,hr,?_,?_,?_⟩
    · exact fun h => hqp (sub_eq_zero.mp h).symm
    · exact sub_le_self p hq.nonneg
    · rw [map_sub,Complex.sub_re]
      linarith

lemma exists_geometric {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0)
    (n : ℕ) : ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re≤(1/2:ℝ)^n*(τ p).re := by
  induction n with
  | zero => exact ⟨p,hpM,hp,hpn,le_rfl,by simp⟩
  | succ n ih =>
    obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := ih
    obtain ⟨r,hrM,hr,hrn,hrle,hrtrace⟩ := exists_half M τ hM hqM hq hqn
    refine ⟨r,hrM,hr,hrn,hrle.trans hqle,?_⟩
    rw [pow_succ]
    nlinarith

theorem exists_small {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0)
    {ε : ℝ} (hε : 0<ε) : ∃ q∈M, IsStarProjection q ∧ q≠0 ∧ q≤p ∧ (τ q).re<ε := by
  have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n*(τ p).re) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)).mul_const (τ p).re
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const hε).exists
  obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := exists_geometric M τ hM hpM hp hpn n
  exact ⟨q,hqM,hq,hqn,hqle,hqtrace.trans_lt hn⟩

theorem exists_prescribed_trace
    (hτ : Continuous (fun T : H →WOT[ℂ] H => (τ T.toCLM).re))
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    {t : ℝ} (ht : 0≤t) (hte : t≤(τ e).re) :
    ∃ p∈M, IsStarProjection p ∧ p≤e ∧ (τ p).re=t := by
  let p0 : ProjectionChains.TraceCut M τ e t :=
    ⟨0,M.zero_mem,IsStarProjection.zero _,he.nonneg,by simpa using ht⟩
  let : Nonempty (ProjectionChains.TraceCut M τ e t) := ⟨p0⟩
  obtain ⟨p,hmax⟩ := zorn_le_nonempty
    (ProjectionChains.cut_chain_upper M τ e t he hτ)
  have hpM := p.property.1
  have hp := p.property.2.1
  have hpe := p.property.2.2.1
  have hpt := p.property.2.2.2
  refine ⟨p.val,hpM,hp,hpe,?_⟩
  apply le_antisymm hpt
  by_contra! hlt
  have hres : IsStarProjection (e-p.val) := hp.sub_of_mul_eq_left he
    ((hp.le_iff_mul_eq_left he).mp hpe)
  have hresM : e-p.val∈M := M.sub_mem heM hpM
  have hresn : e-p.val≠0 := by
    intro hz
    have hpE := sub_eq_zero.mp hz
    rw [hpE] at hte
    exact (not_lt_of_ge hte) hlt
  obtain ⟨q,hqM,hq,hqn,hqle,hqtrace⟩ := exists_small M τ hM hresM hres hresn
    (sub_pos.mpr hlt)
  have hpq : p.val*q=0 := by
    have hqfix := (hq.le_iff_mul_eq_right hres).mp hqle
    have hpefix := (hp.le_iff_mul_eq_left he).mp hpe
    calc
      _=p.val*((e-p.val)*q) := by rw [hqfix]
      _=0 := by rw [←mul_assoc,mul_sub,hpefix,hp.isIdempotentElem.eq,sub_self,zero_mul]
  have hsumproj : IsStarProjection (p.val+q) := hp.add hq hpq
  have hsume : p.val+q≤e := by
    calc
      _≤p.val+(e-p.val) := add_le_add_right hqle _
      _=e := by abel
  have hsumtrace : (τ (p.val+q)).re≤t := by
    rw [map_add,Complex.add_re]
    linarith
  let r : ProjectionChains.TraceCut M τ e t :=
    ⟨p.val+q,M.add_mem hpM hqM,hsumproj,hsume,hsumtrace⟩
  have hpr : p≤r := le_add_of_nonneg_right hq.nonneg
  have heq : r=p := le_antisymm (hmax hpr) hpr
  have hval := congrArg Subtype.val heq
  change p.val+q=p.val at hval
  exact hqn (add_left_cancel (hval.trans (add_zero p.val).symm))

end Kadison.DiffuseProjection

end

end
end

end OAI
