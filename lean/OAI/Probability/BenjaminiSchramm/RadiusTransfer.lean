import OAI.Probability.BenjaminiSchramm.IntrinsicBallisticity
import OAI.Probability.BenjaminiSchramm.IntrinsicRadiusUpper
import OAI.Probability.BenjaminiSchramm.IntrinsicRadiusLower

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem extrinsicRadiusEvent_subset_intrinsic (G : BondGraph V E) (x : V) (n : ℕ) :
    extrinsicRadiusEvent G x n ⊆ intrinsicRadiusEvent G x n := by
  rintro ω ⟨y,hc,hd⟩
  refine ⟨y,hc,hd.trans ?_⟩
  have hle : openSimpleGraph G ω ≤ openSimpleGraph G Set.univ := by
    rintro a b ⟨hne,e,he,hab⟩
    exact ⟨hne,e,Set.mem_univ _,hab⟩
  exact SimpleGraph.Reachable.dist_anti hle ((conn_iff_reachable G ω x y).mp hc)

theorem intrinsicRadiusEvent_subset_extrinsic_union (G : BondGraph V E)
    (hconn : Connected G) (hloc : LocallyFinite G) (x : V) (m n : ℕ) :
    intrinsicRadiusEvent G x m ⊆ extrinsicRadiusEvent G x n ∪
      ⋃ y ∈ (finite_reachBall hloc x n).toFinset, longConnectionEvent G x y m := by
  rintro ω ⟨y,hc,hd⟩
  by_cases he : ω ∈ extrinsicRadiusEvent G x n
  · exact Or.inl he
  · right
    have hdist : graphDistance G x y ≤ n := by
      by_contra h
      exact he ⟨y,hc,(Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
    exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr
      ⟨(finite_reachBall hloc x n).mem_toFinset.mpr
        (mem_reachBall_of_graphDistance_le G hconn x y n hdist),hc,hd⟩⟩

theorem intrinsic_radius_le_extrinsic_add [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (p : unitInterval) (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (x : V) (m n : ℕ) :
    (law p).real (intrinsicRadiusEvent G x m) ≤
      (law p).real (extrinsicRadiusEvent G x n) +
        ((d+1 : ℕ) : ℝ)^n * (2 * ‖T‖ * Real.exp (-(Real.log 2/(3*‖T‖))*m)) := by
  let B := (finite_reachBall hloc x n).toFinset
  let R := 2 * ‖T‖ * Real.exp (-(Real.log 2/(3*‖T‖))*m)
  have hcard : (B.card : ℝ) ≤ ((d+1 : ℕ) : ℝ)^n := by
    have hh := reachBall_ncard_le_pow G hloc d hd x n
    rw [Set.ncard_eq_toFinset_card _ (finite_reachBall hloc x n)] at hh
    exact_mod_cast hh
  calc
    _ ≤ (law p).real (extrinsicRadiusEvent G x n ∪ ⋃ y ∈ B, longConnectionEvent G x y m) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (intrinsicRadiusEvent_subset_extrinsic_union G hconn hloc x m n))
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) +
        (law p).real (⋃ y ∈ B, longConnectionEvent G x y m) := measureReal_union_le _ _
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) + ∑ y ∈ B, (law p).real (longConnectionEvent G x y m) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le B _)
    _ ≤ (law p).real (extrinsicRadiusEvent G x n) + ∑ _y ∈ B, R := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum (fun y _ => longConnection_exponential_bound G hloc p T hT x y m)
    _ = (law p).real (extrinsicRadiusEvent G x n) + B.card * R := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (by positivity))

theorem exponential_quadratic_bound {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ 2/t^2 := by
  have hh := Real.pow_div_factorial_le_exp t ht.le 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one] at hh
  rw [Real.exp_neg,inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos t) (sq_pos_of_pos ht)).mpr
  nlinarith

theorem radius_transfer_error {a B c D : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hc : 0 < c) (hD : 0 < D) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      D^n * (B*Real.exp (-a*(K*n : ℕ))) ≤ (c/(2*K))/n := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (2*Real.log D/a) (16*B/(a^2*c)))
  have hKn : 0 < K := by
    have hh := (le_max_right (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    have : (0 : ℝ) < K := lt_trans (by positivity) hh
    exact_mod_cast this
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKn
  have hlog : 2*Real.log D ≤ a*K := by
    have hh := (le_max_left (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    exact (div_le_iff₀ ha).mp hh.le |>.trans_eq (mul_comm _ _)
  have hsize : 16*B ≤ a^2*c*K := by
    have hh := (le_max_right (2*Real.log D/a) (16*B/(a^2*c))).trans_lt hK
    have h := (div_le_iff₀ (by positivity : 0 < a^2*c)).mp hh.le
    nlinarith
  refine ⟨K,hKn,?_⟩
  intro n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 < a*K*n/2 := by positivity
  have hdecay : D^n * (B*Real.exp (-a*(K*n : ℕ))) ≤ B*Real.exp (-(a*K*n/2)) := by
    have hexp : Real.log D*n - a*K*n ≤ -(a*K*n/2) := by nlinarith
    calc
      _ = B*Real.exp (Real.log D*n-a*K*n) := by
        rw [Real.exp_sub,neg_mul,Real.exp_neg,mul_comm (Real.log D) (n : ℝ),Real.exp_nat_mul,Real.exp_log hD]
        push_cast
        rw [mul_assoc a (K : ℝ) (n : ℝ)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB.le
  have hpoly := mul_le_mul_of_nonneg_left (exponential_quadratic_bound ht) hB.le
  have hrat : B*(2/(a*K*n/2)^2) ≤ (c/(2*K))/n := by
    have hid : B*(2/(a*K*n/2)^2) = 8*B/(a^2*(K:ℝ)^2*(n:ℝ)^2) := by
      field_simp
      ring
    rw [hid,div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hsize (by positivity : (0 : ℝ) ≤ K*n)
    have hnn := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ a^2*c*K^2*n)
    nlinarith
  exact hdecay.trans (hpoly.trans hrat)

theorem extrinsic_radius_lower_of_intrinsic [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (x : V) (c : ℝ) (hc : 0 < c)
    (hint : ∀ m : ℕ, 0 < m → c/m ≤ (law p).real (intrinsicRadiusEvent G x m)) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 0 < n → b/n ≤ (law p).real (extrinsicRadiusEvent G x n) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  let a := Real.log 2/(3*‖T‖)
  have hnorm : 0 < ‖T‖ := lt_of_lt_of_le zero_lt_one (hT.norm_one_le G p T)
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) (by positivity)
  obtain ⟨K,hK,herr⟩ := radius_transfer_error ha (by positivity : 0 < 2*‖T‖) hc
    (by positivity : (0 : ℝ) < (d+1 : ℕ))
  refine ⟨c/(2*K),by positivity,?_⟩
  intro n hn
  have hKn : 0 < K*n := Nat.mul_pos hK hn
  have hlow := hint (K*n) hKn
  have hbound := intrinsic_radius_le_extrinsic_add G hconn hloc p T hT d hd x (K*n) n
  have herror := herr n hn
  have hid : c/(K*n : ℕ) = (c/(2*K))/n + (c/(2*K))/n := by
    push_cast
    field_simp
    ring
  rw [hid] at hlow
  linarith

theorem critical_radius_powerTails_of_operator [Infinite V] [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (hpc1 : (pc G : ℝ) < 1)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G (pc G) T) (x : V) :
    PowerTail (criticalTail G (intrinsicRadiusEvent G) x) 1 ∧
      PowerTail (criticalTail G (extrinsicRadiusEvent G) x) 1 := by
  obtain ⟨c,hc,hlo⟩ := critical_intrinsic_radius_lower_of_operator G hconn hloc hqt hh hpc1 T hT x
  obtain ⟨C,hC,hup⟩ := critical_intrinsic_radius_upper_of_operator G hconn hloc hqt hh hpc1 T hT
  have hint (n : ℕ) (hn : 0 < n) : criticalTail G (intrinsicRadiusEvent G) x n ≤ C/n := by
    change (law (pc G) (intrinsicRadiusEvent G x n)).toReal ≤ C/n
    simpa only [domainRadiusEvent,Set.inter_univ,Set.ofPred_mem_eq] using hup Set.univ x n hn
  obtain ⟨b,hb,hext⟩ := extrinsic_radius_lower_of_intrinsic G hconn hloc hqt (pc G) T hT x c hc hlo
  have hupper (n : ℕ) (hn : 0 < n) : criticalTail G (extrinsicRadiusEvent G) x n ≤ C/n := by
    apply le_trans _ (hint n hn)
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (extrinsicRadiusEvent_subset_intrinsic G x n))
  constructor
  · refine ⟨c,C,hc,hC,fun n hn => ?_⟩
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using And.intro (hlo n hn) (hint n hn)
  · refine ⟨b,C,hb,hC,fun n hn => ?_⟩
    have hlow : b/n ≤ criticalTail G (extrinsicRadiusEvent G) x n := hext n hn
    simpa only [Real.rpow_neg_one,div_eq_mul_inv] using And.intro hlow (hupper n hn)

theorem criticalRadiiInput_of_nonamenable [Infinite V]
    (G : BondGraph V E) (hh : 0 < hV G) : HutchcroftCriticalRadiiInput G := by
  intro hgraph hgap x
  let : Countable V := countable_vertices hgraph.locallyFinite hgraph.connected
  let : Countable E := countable_edges hgraph.locallyFinite
  have hp1 : (pc G : ℝ) < 1 :=
    (show (pc G : ℝ) < (ptwo G : ℝ) from hgap).trans_le (ptwo G).2.2
  obtain ⟨q,hq,hpq⟩ := lt_sSup_iff.mp hgap
  obtain ⟨T,hT⟩ := operatorBounded_of_le G hpq.le hq
  have hfin := critical_finite_general G hgraph.connected hgraph.locallyFinite hgraph.quasiTransitive hp1
  rw [criticalFiniteTail_eq G (intrinsicRadiusEvent G) x (hfin x),
    criticalFiniteTail_eq G (extrinsicRadiusEvent G) x (hfin x)]
  exact critical_radius_powerTails_of_operator G hgraph.connected hgraph.locallyFinite
    hgraph.quasiTransitive hh hp1 T hT x

end Percolation.BenjaminiSchramm

end OAI
