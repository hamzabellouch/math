import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # From per-attempt geometric failure to physical expected runtime -/

namespace ContingencyTables.GeometricRuntime
open scoped BigOperators

lemma block_geometric (T : ℕ) (hT : 0<T) (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ<1) :
    Summable (fun t : ℕ => ρ^(t/T)) ∧
      (∑' t : ℕ,ρ^(t/T))=(T:ℝ)/(1-ρ) := by
  let : NeZero T:=⟨hT.ne'⟩
  have hgeo:=summable_geometric_of_lt_one hρ hρ1
  have hprod : Summable (fun p : ℕ×Fin T => ρ^p.1) := by
    apply (summable_prod_of_nonneg (fun p => pow_nonneg hρ p.1)).mpr
    refine ⟨fun _ => Summable.of_finite,?_⟩
    simpa only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] using hgeo.mul_left (T:ℝ)
  have hs : Summable (fun t : ℕ => ρ^(t/T)) :=
    (Nat.divModEquiv T).summable_iff.mpr hprod
  refine ⟨hs,?_⟩
  calc
    (∑' t : ℕ,ρ^(t/T)) = ∑' p : ℕ×Fin T,ρ^p.1 :=
      (Nat.divModEquiv T).tsum_eq (fun p => ρ^p.1)
    _ = ∑' n : ℕ,∑' _j : Fin T,ρ^n := hprod.tsum_prod
    _ = ∑' n : ℕ,(T:ℝ)*ρ^n := by simp only [tsum_fintype,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = (T:ℝ)*(∑' n : ℕ,ρ^n) := tsum_mul_left
    _ = (T:ℝ)/(1-ρ) := by rw [tsum_geometric_of_lt_one hρ hρ1]; rfl

/-- A real tail is required to be summable, rather than assigning a
default value to a divergent infinite sum. -/
theorem expected_time_bound (tail : ℕ → ℝ) (T : ℕ) (hT : 0<T)
    (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ<1)
    (h0 : ∀ t,0≤tail t) (hmono : Antitone tail)
    (hstep : ∀ N,tail (N*T)≤ρ^N) :
    Summable tail ∧ (∑' t,tail t)≤(T:ℝ)/(1-ρ) := by
  obtain ⟨hg,hgs⟩:=block_geometric T hT ρ hρ hρ1
  have hb (t : ℕ) : tail t≤ρ^(t/T) := by
    have ht : (t/T)*T≤t := Nat.div_mul_le_self t T
    exact (hmono ht).trans (hstep (t/T))
  have hs:=Summable.of_nonneg_of_le h0 hb hg
  exact ⟨hs,(hs.tsum_le_tsum hb hg).trans_eq hgs⟩

theorem expected_time_half (tail : ℕ → ℝ) (T : ℕ) (hT : 0<T)
    (h0 : ∀ t,0≤tail t) (hmono : Antitone tail)
    (hstep : ∀ N,tail (N*T)≤(1/2:ℝ)^N) :
    Summable tail ∧ (∑' t,tail t)≤2*T := by
  have h:=expected_time_bound tail T hT (1/2) (by norm_num) (by norm_num) h0 hmono hstep
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

end ContingencyTables.GeometricRuntime

end OAI
