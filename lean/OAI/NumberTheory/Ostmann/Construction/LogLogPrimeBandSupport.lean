import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBands

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

lemma primePrefix_eq_primesLE (x : ℝ) : primePrefix x=⌊x⌋₊.primesLE := by
  ext p
  simp only [primePrefix,Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩

lemma prime_loglog_le_iff {p : ℕ} (hp : p.Prime) (b : ℝ) :
    Real.log (Real.log p)≤b ↔ (p:ℝ)≤Real.exp (Real.exp b) := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ)<p := by linarith
  have hl : 0<Real.log (p:ℝ) := Real.log_pos hp1
  constructor
  · intro h
    have h₁ := Real.exp_le_exp.mpr h
    rw [Real.exp_log hl] at h₁
    have h₂ := Real.exp_le_exp.mpr h₁
    rwa [Real.exp_log hp0] at h₂
  · intro h
    have h₁ := Real.log_le_log hp0 h
    rw [Real.log_exp] at h₁
    have h₂ := Real.log_le_log hl h₁
    rwa [Real.log_exp] at h₂

theorem logLogPrimeBand_mem_iff (a b : ℝ) (p : ℕ) :
    p∈logLogPrimeBand a b ↔ p.Prime ∧ a<Real.log (Real.log p) ∧
      Real.log (Real.log p)≤b := by
  constructor
  · intro h
    obtain ⟨hhi,hlo⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hr,hp⟩ := Finset.mem_filter.mp hhi
    obtain ⟨hp0,hupper⟩ := Finset.mem_Ioc.mp hr
    have hpr : (p:ℝ)≤Real.exp (Real.exp b) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hupper
    refine ⟨hp,?_,(prime_loglog_le_iff hp b).mpr hpr⟩
    apply lt_of_not_ge
    intro hlog
    apply hlo
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hp0,?_⟩,hp⟩
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr ((prime_loglog_le_iff hp a).mp hlog)
  · rintro ⟨hp,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨hp.pos,?_⟩,hp⟩
      exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr ((prime_loglog_le_iff hp b).mp hhi)
    · intro h
      have hu := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).2
      have hle := (prime_loglog_le_iff hp a).mpr ((Nat.le_floor_iff (Real.exp_pos _).le).mp hu)
      exact (not_le_of_gt hlo) hle

end Ostmann.Construction

end

end OAI
