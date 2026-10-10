import OAI.Combinatorics.PerfectMatching.MatchingCovariance

namespace OAI

/-!
The nonlinear entropy defect bound
`F - H ≤ 8m (1 - exp (-F/m))` for finite loopless multigraphs on `2m` vertices,
and the perfect matching count bound `[k exp (-8 (1 - 1/k))]^m`,
with its coarse bound `(exp (-8) k)^m`, when the entire edge set
is partitioned into `k ≥ 1` perfect matchings.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The small-entropy regime of the nonlinear barrier function. -/
theorem entropy_barrier_ge_id {t : ℝ} (ht : 0 ≤ t) (h8 : t ≤ Real.log 8) :
    t ≤ 8 * (1-Real.exp (-t)) := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have he8 : Real.exp t ≤ 8 := by
    have hh := Real.exp_le_exp.mpr h8
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh
    exact hh
  have hlog := Real.log_le_sub_one_of_pos (Real.exp_pos t)
  rw [Real.log_exp] at hlog
  have hin := Real.exp_neg t
  rw [hin]
  have hp := Real.exp_pos t
  apply (mul_le_mul_iff_right₀ hp).mp
  have hmain : t * Real.exp t ≤ 8 * (Real.exp t - 1) := by
    have : t ≤ Real.exp t - 1 := hlog
    nlinarith
  have hprod : Real.exp t * (8*(1-(Real.exp t)⁻¹)) = 8*(Real.exp t-1) := by
    field_simp [hp.ne']
  calc
    Real.exp t * t = t * Real.exp t := mul_comm _ _
    _ ≤ 8 * (Real.exp t-1) := hmain
    _ = _ := hprod.symm


/-- Entropy on s positive edge coordinates of total mass m is at most m log(s/m). -/
theorem marginal_entropy_support_bound (G : LooplessGraph V E) {m : ℕ}
    (hm : 0 < m) (hV : Fintype.card V=2*m) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x ∧ 0 < Fintype.card {e // 0 < x e} ∧
      entropy x ≤ (m:ℝ)*Real.log ((Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hmass := G.marginal_sum hV hx
  have hn : ∀ e, 0 ≤ x e := fun e => (G.coordinate_mem_Icc hx e).1
  have hz : ∀ e, ¬ 0 < x e → x e=0 := fun e he => le_antisymm (le_of_not_gt he) (hn e)
  have hsum : (∑ e : {e // 0 < x e}, x e.val)=(m:ℝ) :=
    (sum_positive_support x x hz).symm.trans hmass
  have hent : entropy (fun e : {e // 0 < x e} => x e.val)=entropy x := by
    unfold entropy
    exact (sum_positive_support x (fun e => Real.negMulLog (x e))
      (fun e he => by rw [hz e he,Real.negMulLog_zero])).symm
  have hpossum : 0 < ∑ e, x e := by rw [hmass]; exact hmR
  obtain ⟨e,_,he⟩ := (Finset.sum_pos_iff_of_nonneg (fun e _ => hn e)).mp hpossum
  have hs : 0 < Fintype.card {e // 0 < x e} := Fintype.card_pos_iff.mpr ⟨⟨e,he⟩⟩
  have hsR : (0:ℝ) < Fintype.card {e // 0 < x e} := by exact_mod_cast hs
  refine ⟨Finset.sum_nonneg (fun e _ => Real.negMulLog_nonneg (hn e) (G.coordinate_mem_Icc hx e).2),hs,?_⟩
  let c : ℝ := (Fintype.card {e // 0 < x e}:ℝ)/(m:ℝ)
  have hc : 0 < c := div_pos hsR hmR
  have hcm : c*(m:ℝ)=Fintype.card {e // 0 < x e} := div_mul_cancel₀ _ hmR.ne'
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun e : {e // 0 < x e} => fun _ =>
    Real.negMulLog_le_one_sub_self (mul_nonneg hc.le e.property.le))
  simp_rw [Real.negMulLog_mul] at hb
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hsum,
    Finset.sum_sub_distrib,← Finset.mul_sum,hsum] at hb
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  change (m:ℝ)*Real.negMulLog c+c*entropy (fun e : {e // 0 < x e} => x e.val) ≤
    (Fintype.card {e // 0 < x e}:ℝ)-c*(m:ℝ) at hb
  rw [hent,Real.negMulLog,hcm,sub_self] at hb
  change entropy x ≤ (m:ℝ)*Real.log c
  nlinarith

/-- Main entropy comparison, for every marginal in the actual matching polytope. -/
theorem entropy_main (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m)
    (hPM : Nonempty G.Matching) (y : E → ℝ) (hy : y ∈ G.polytope) :
    marginalEntropy y - maxMatchingEntropy G y ≤
      8 * (m : ℝ) * (1 - Real.exp (-marginalEntropy y / (m : ℝ))) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heven : Even (Fintype.card V) := by rw [hV]; exact even_two_mul m
  obtain ⟨x,hx,hmax⟩ := entropyDefect_attains_max G heven hPM (m:ℝ)
  by_contra htarget
  have hypos : 0 < entropyDefect G (m:ℝ) y := by
    dsimp [entropyDefect,entropyBarrier,marginalEntropy] at *
    linarith
  have hpos : 0 < entropyDefect G (m:ℝ) x := hypos.trans_le (hmax y hy)
  obtain ⟨p,hp,hopt⟩ := maxMatchingEntropy_attained G hx
  obtain ⟨hxnon,hspos,hentropy⟩ := marginal_entropy_support_bound G hm hV hx
  have hH := maxMatchingEntropy_nonneg G hx
  let s : ℝ := Fintype.card {e // 0 < x e}
  have hsR : 0 < s := by dsimp only [s]; exact_mod_cast hspos
  have hrpos : 0 < s/(m:ℝ) := div_pos hsR hmR
  have hu : entropy x/(m:ℝ) ≤ Real.log (s/(m:ℝ)) := by
    apply (div_le_iff₀ hmR).mpr
    simpa only [mul_comm] using hentropy
  have hlo : Real.log 8 < entropy x/(m:ℝ) := by
    by_contra hle
    have hb := entropy_barrier_ge_id (div_nonneg hxnon hmR.le) (le_of_not_gt hle)
    have hb' := (div_le_iff₀ hmR).mp hb
    dsimp only [entropyDefect,entropyBarrier] at hpos
    rw [neg_div] at hpos
    nlinarith
  have hs8 : 8*(m:ℝ) < s := by
    have hh := (Real.log_lt_log_iff (by norm_num : (0:ℝ)<8) hrpos).mp (hlo.trans_le hu)
    exact (lt_div_iff₀ hmR).mp hh
  have ha : 8*(m:ℝ)/s ≤ 8*Real.exp (-entropy x/(m:ℝ)) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg hu)
    rw [Real.exp_neg,Real.exp_log hrpos,inv_div] at hh
    rw [neg_div,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hrankNat := matching_covariance_rank G heven hp hopt
  rw [hV] at hrankNat
  have hrankR : s ≤ 2*(2*(m:ℝ))+(covariance p (matchingNormalized G x)).rank := by
    dsimp only [s]
    exact_mod_cast hrankNat
  have hrank : s-4*(m:ℝ) ≤ (covariance p (matchingNormalized G x)).rank := by linarith
  exact covariance_contradiction (covariance_posSemidef p (matchingNormalized G x)) hmR hs8
    hrank (matching_covariance_trace G hp hV) ha
    (matching_covariance_second_variation G hp hopt hmR hmax)


omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- An edge partition into k matchings places the exact uniform edge vector in P. -/
theorem uniform_decomposition_mem (G : LooplessGraph V E) {k : ℕ} (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hpartition : ∀ e : E, ∃! i : Fin k, e ∈ (M i).val) :
    (fun _ : E => 1/(k:ℝ)) ∈ G.polytope := by
  classical
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum : (∑ i : Fin k, (1/(k:ℝ)))=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hmean := (convex_convexHull ℝ (Set.range G.indicator)).sum_mem
    (fun (i : Fin k) _ => (one_div_pos.mpr hkR).le) hsum
    (fun i _ => subset_convexHull ℝ _ (Set.mem_range_self (M i)))
  have heq : (∑ i : Fin k, (1/(k:ℝ)) • G.indicator (M i)) = (fun _ : E => 1/(k:ℝ)) := by
    ext e
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum]
    have hi : (∑ i : Fin k, G.indicator (M i) e)=1 := by
      obtain ⟨i,hi,hu⟩ := hpartition e
      rw [Finset.sum_eq_single i]
      · simp [LooplessGraph.indicator,hi]
      · intro j _ hji
        have hj : e ∉ (M j).val := fun h => hji (hu j h)
        simp [LooplessGraph.indicator,hj]
      · simp
    rw [hi,mul_one]
  rwa [heq] at hmean

/-- The exact decomposable-graph count theorem, including its coarser bound. -/
theorem count_main (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hpartition : ∀ e : E, ∃! i : Fin k, e ∈ (M i).val) :
    ((k : ℝ) * Real.exp (-8 * (1 - 1 / (k : ℝ)))) ^ m ≤
        (Fintype.card G.Matching : ℝ) ∧
      (Real.exp (-8) * (k : ℝ)) ^ m ≤
        ((k : ℝ) * Real.exp (-8 * (1 - 1 / (k : ℝ)))) ^ m := by
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hPM : Nonempty G.Matching := ⟨M ⟨0,by omega⟩⟩
  let x : E → ℝ := fun _ => 1/(k:ℝ)
  have hx : x ∈ G.polytope := uniform_decomposition_mem G hk M hpartition
  have hh : marginalEntropy x=(m:ℝ)*Real.log (k:ℝ) := by
    have hlog : Real.negMulLog (1/(k:ℝ))=(1/(k:ℝ))*Real.log (k:ℝ) := by
      rw [one_div,Real.negMulLog,Real.log_inv]
      ring
    change (∑ e : E, Real.negMulLog (1/(k:ℝ)))=_
    simp_rw [hlog]
    rw [← Finset.sum_mul]
    exact congrArg (fun t : ℝ => t*Real.log (k:ℝ)) (G.marginal_sum hV hx)
  have hi := entropy_main G m hm hV hPM x hx
  have hH := maxMatchingEntropy_le_log_card G hx
  have hexp : Real.exp (-((m:ℝ)*Real.log (k:ℝ))/(m:ℝ))=1/(k:ℝ) := by
    have he : -((m:ℝ)*Real.log (k:ℝ))/(m:ℝ) = -Real.log (k:ℝ) := by
      field_simp
    rw [he,Real.exp_neg,Real.exp_log hkR]
    simp only [one_div]
  rw [hh,hexp] at hi
  have hlogbound : (m:ℝ)*(Real.log (k:ℝ)+(-8*(1-1/(k:ℝ)))) ≤
      Real.log (Fintype.card G.Matching:ℝ) := by nlinarith
  have hN : (0:ℝ) < Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  constructor
  · have he := Real.exp_le_exp.mpr hlogbound
    rw [Real.exp_log hN,Real.exp_nat_mul,Real.exp_add,Real.exp_log hkR] at he
    exact he
  · apply pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hkR.le)
    have he : Real.exp (-8) ≤ Real.exp (-8*(1-1/(k:ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hq := (one_div_pos.mpr hkR).le
      nlinarith
    calc
      Real.exp (-8)*(k:ℝ) = (k:ℝ)*Real.exp (-8) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left he hkR.le

end MatchingEntropy

end

end OAI
