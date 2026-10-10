import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicHarmonic
import OAI.NumberTheory.TotientAsymptotic.TupleTotients

namespace OAI

/-! The finite dyadic counting envelope used to bootstrap the global upper bound. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def dyadicTotientEnvelope (J : ℕ) : ℝ :=
  max 1 ((Finset.range (J+1)).sup' (by simp)
    (fun k => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k))

lemma dyadicTotientEnvelope_one_le (J : ℕ) : 1 ≤ dyadicTotientEnvelope J := le_max_left _ _

lemma dyadicTotientEnvelope_mono {I J : ℕ} (hIJ : I ≤ J) :
    dyadicTotientEnvelope I ≤ dyadicTotientEnvelope J := by
  unfold dyadicTotientEnvelope
  apply max_le_max le_rfl
  exact Finset.sup'_mono (s₁ := Finset.range (I+1)) (s₂ := Finset.range (J+1))
    (fun k : ℕ => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k)
    (Finset.range_mono (Nat.add_le_add_right hIJ 1)) (by simp)

lemma dyadicTotientEnvelope_term_le {k J : ℕ} (hkJ : k ≤ J) :
    V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k ≤ dyadicTotientEnvelope J := by
  unfold dyadicTotientEnvelope
  have hs : k ∈ Finset.range (J+1) := Finset.mem_range.mpr (by omega)
  exact (Finset.le_sup' (s:=Finset.range (J+1))
    (fun k => V ((2:ℝ)^k)*(k:ℝ)/(2:ℝ)^k) hs).trans (le_max_right _ _)

lemma dyadic_totient_count_le {k J : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    V ((2:ℝ)^k) ≤ dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpow : (0:ℝ) < 2^k := by positivity
  have he := dyadicTotientEnvelope_term_le hkJ
  apply (le_div_iff₀ hk0).mpr
  exact (div_le_iff₀ hpow).mp he

lemma totient_values_subset {x y : ℝ} (hxy : x ≤ y) : totientValues x ⊆ totientValues y := by
  classical
  intro v hv
  obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hv).1,(Finset.mem_Icc.mp hv).2.trans (Nat.floor_mono hxy)⟩,ht⟩

lemma V_monotone : Monotone V := by
  intro x y hxy
  exact Nat.cast_le.mpr (Finset.card_le_card (totient_values_subset hxy))

lemma dyadic_totient_reciprocal_mass {J : ℕ} (_hJ : 1 ≤ J) (Q : Finset ℕ)
    (hQ : ∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ (2:ℝ)^J) :
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+4*dyadicTotientEnvelope J*(1+Real.log J) := by
  classical
  let E := Q.erase 1
  have hE (v : ℕ) (hv : v ∈ E) : IsTotient v ∧ 1 < v ∧ (v:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hne,hv⟩ := Finset.mem_erase.mp hv
    have h := hQ v hv
    exact ⟨h.1,by have := isTotient_pos h.1; omega,h.2⟩
  have hn : ∀ v ∈ E,Nat.clog 2 v ∈ Finset.Icc 1 J := by
    intro v hv
    have hb := dyadic_nat_bounds (hE v hv).2.1
    refine Finset.mem_Icc.mpr ⟨hb.1,?_⟩
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    exact_mod_cast (hE v hv).2.2
  have hcount (k : ℕ) (hk : k ∈ Finset.Icc 1 J) :
      ((E.filter (fun v => Nat.clog 2 v=k)).card:ℝ) ≤
      dyadicTotientEnvelope J*(2:ℝ)^k/(k:ℝ) := by
    have hsub : E.filter (fun v => Nat.clog 2 v=k) ⊆ totientValues ((2:ℝ)^k) := by
      intro v hv
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have h := hE v hv
      have hb := (dyadic_nat_bounds h.2.1).2.2
      rw [he] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨isTotient_pos h.1,Nat.le_floor hb⟩,h.1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (dyadic_totient_count_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  have hm := finite_dyadic_harmonic_mass E (Nat.clog 2) (fun v => (v:ℝ)) J
    (zero_le_one.trans (dyadicTotientEnvelope_one_le J)) hn (by
      intro v hv
      have hh := (dyadic_nat_bounds (hE v hv).2.1).2.1
      have hp : (0:ℝ) < 2^(Nat.clog 2 v) := by positivity
      linarith) hcount
  have hs : (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ 1+∑ v ∈ E,(v:ℝ)⁻¹ := by
    by_cases h1 : 1 ∈ Q
    · rw [← Finset.add_sum_erase Q _ h1]
      norm_num [E]
    · have he : E=Q := Finset.erase_eq_of_notMem h1
      rw [he]
      linarith
  exact hs.trans (add_le_add le_rfl hm)

end TotientAsymptotic

end

end OAI
