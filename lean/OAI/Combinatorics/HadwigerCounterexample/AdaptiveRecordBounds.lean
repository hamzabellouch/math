import OAI.Combinatorics.HadwigerCounterexample.IndependentTestWitnesses

namespace OAI

/-! # Adaptive Record Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

def quest (p : Shape) (r k n N : ℕ) (H ε : ℝ) :=
  ∀ x : ℕ,x≤2*r →
    bp ((x:ℝ)*N)*bp (0.51*k*N)*(H*heatRate p n N ε x k)≤bp (-0.2*N)

namespace Bazaar
variable (s : Bazaar p n r T)

set_option maxHeartbeats 800000 in
private theorem probe_event {w : Wgt (UnitType p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1) {k : ℕ}
    {q : Place p→ℕ} (R : DTuple (p:=p) q N) (F : Catalog p T r q)
    (hq : ctot p q=k) (hr : ∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*N))
    (m : Mixer p n) {ε H : ℝ} (he₀ : initCap p N m ε) (hH : 0≤H) (hZ : quest p r k n N H ε)
    (hg : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hT : num (Atlas p r T) ≤ bp (0.002*N)) :
    pr w (fun x => s.atList S j R F x ∧ glimpse p x j R) ≤ bp (-0.1*N) := by
  classical
  let P (M : Atlas p r T) (z : Batch M N) (v : DTuple (p:=p) q N) :=
    fun x => basisFrom p (x : UnitType p n N) j z ∧ glimpse p x j R ∧ thermal p x S R=v
  let L (M : Atlas p r T) (x) := standard M ∧ ∃ z,∃ v∈ F M z,P M z v x
  have he x : w x≠0 → s.atList S j R F x ∧ glimpse p x j R →
      ∃ M,L M x := by
    rintro hx ⟨hx',hy⟩
    exact ⟨s.ix x,(h x hx).1,s.bag (s.ix x) j x, thermal p x S R,hx',
      ((h x hx).2 j).1,hy,rfl⟩
  have ht (M : Atlas p r T) : pr w (L M) ≤ bp (-0.2*N) := by
    by_cases hu : standard M
    · let x := cells M
      have hb (z : Batch M N) :
          pr w (fun y => ∃ v∈F M z,P M z v y) ≤ bp (0.51*k*N)*(H*heatRate p n N ε x k) := by
        have ha v : pr w (P M z v) ≤ H*heatRate p n N ε x k := by
          rw [← hq]; exact (pr_cap hg _).trans
            (mul_le_mul_of_nonneg_left (heat_rate _ S hi R v z m he₀) hH)
        refine (pr_union_le hw.nz (F M z) (P M z)).trans ((Finset.sum_le_sum fun v _ => ha v).trans ?_)
        rw [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (hr M z)
        unfold heatRate
        exact mul_nonneg hH (mul_nonneg (bp_pos _).le (bp_pos _).le)
      simp only [L,hu,true_and]
      refine (pr_exists_le hw.nz (fun z y => ∃ v∈F M z,P M z v y)).trans
        ((Finset.sum_le_sum (fun z _ => hb z)).trans ?_)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space]
      rw [show dim (Batch M N)=x*N from tuple_dim.trans (Nat.mul_comm ..),
        Nat.cast_mul, ← mul_assoc]
      exact hZ x hu.2.1
    simp only [L,hu,false_and,pr_false]
    exact (bp_pos _).le
  refine ((pr_on_mono hw.nz he).trans (pr_exists_le hw.nz L)).trans
    ((Finset.sum_le_sum fun i _ => ht i).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hT (bp_pos _).le).trans
  rw [←bp_add]
  apply bp_le; linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]

set_option maxHeartbeats 600000 in
theorem frequent_sparse {w : Wgt (UnitType p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1)
    (k d : ℕ) (hh : k ≤ d) (l : ℝ) (hl : 0< l)
    (hC : ∀ C : Cov p N,cdim p C≤d → pr w (fun x => offsetCov (s.ix x) ≤ C) ≤ l)
    (hb : ∀ A M Z,(↑(s.bids w S j A M Z).card:ℝ) ≤ bp (0.51*N))
    (m : Mixer p n) {ε H L : ℝ} (hN : 2*num (Full p n)-N≤ -1)
    (he : initCap p N m ε)
    (hH : 0≤H) (hZ : quest p r k n N H ε)
    (hg : ∀ x,w x≤H*pairW (raw m N) (raw m N) x)
    (hL : 0 ≤ L) (hv : bySide p w m L)
    (hT : num (Atlas p r T) ≤ bp (0.002*N))
    (hk : glimpsesBill p k L+bp (-0.1*N)<l^(k+1)) :
    pr (pairW w w) (fun x => s.frequent w S j (s.ix x.1) (s.ix x.2) x.2) ≤5*l := by
  classical
  by_contra! hr
  obtain ⟨q,R,F,hq,hR,hF,hx⟩ := s.shooting hw S j k d hh l hl hr.le hC hb
  have hp := s.probe_event hw h S j hi R F hq hF m he hH hZ hg hT
  have hq' z : q z≤ k := hq ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
    (Finset.mem_univ z)
  have hu := glimpse_failure m hL hv hw.sub j hN R k hR hq'
  let T := fun (x : UnitType p n N) => glimpse p x j R
  let V := s.atList S j R F
  have hh' x : V x → ¬T x ∨ (V x ∧ T x) := fun h => by by_cases ht:T x <;> simp [ht,h]
  exact not_lt_of_ge
    (hx.trans ((pr_mono hw.nz hh').trans ((pr_or_le hw.nz).trans (add_le_add hu hp)))) hk

end Bazaar

end HadwigerCounterexample

end

end OAI
