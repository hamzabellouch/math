import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.LocalizedCompression

namespace OAI

noncomputable section
namespace DirectComparison
open scoped BigOperators

def unitIntervalClamp (t : ℝ) : ℝ := max (-1) (min t 1)
lemma unitIntervalClamp_continuous : Continuous unitIntervalClamp := by
  unfold unitIntervalClamp; fun_prop
lemma unitIntervalClamp_mem (t : ℝ) : unitIntervalClamp t ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
lemma unitIntervalClamp_eq {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    unitIntervalClamp t=t := by
  rw [unitIntervalClamp,min_eq_left ht.2,max_eq_right ht.1]

theorem exists_localized_partition {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∃ μ : Fin m → ℝ, ∃ f : Fin m → ℝ → ℝ,
      (∀ j, μ j ∈ Set.Icc (-1:ℝ) 1) ∧
      (∀ j, Continuous (f j)) ∧
      (∀ j t, f j t ∈ Set.Icc 0 1) ∧
      (∀ t, ∑ j, f j t=1) ∧
      (∀ j t, t ∈ Set.Icc (-1:ℝ) 1 → f j t ≠ 0 → |t-μ j| ≤ ε) := by
  classical
  let K : Set ℝ := Set.Icc (-1) 1
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_Icc : IsCompact K).elim_finite_subcover_image
    (b := K) (c := fun c : ℝ => Metric.ball c ε) (fun _ _ => Metric.isOpen_ball) (by
      intro t ht
      exact Set.mem_iUnion₂.mpr ⟨t,ht,by simpa using hε⟩)
  let I := s
  have hI : Nonempty I := by
    have h0 := hcover (show (0:ℝ) ∈ K by constructor <;> norm_num)
    obtain ⟨c,hcs,_⟩ := Set.mem_iUnion₂.mp h0
    exact ⟨⟨c,hcs⟩⟩
  let : Fintype I := hfin.fintype
  let : Nonempty I := hI
  let m := Fintype.card I
  let e : I ≃ Fin m := Fintype.equivFin I
  let μ : Fin m → ℝ := fun j => (e.symm j).val
  have hμ (j : Fin m) : μ j ∈ K := hs (e.symm j).property
  have hc (t : ℝ) : ∃ j : Fin m, |unitIntervalClamp t-μ j| < ε := by
    obtain ⟨c,hcs,hct⟩ := Set.mem_iUnion₂.mp (hcover (unitIntervalClamp_mem t))
    refine ⟨e ⟨c,hcs⟩,?_⟩
    simpa only [μ,Equiv.symm_apply_apply,Real.dist_eq,Metric.mem_ball] using hct
  let w : Fin m → ℝ → ℝ := fun j t => max (ε-|unitIntervalClamp t-μ j|) 0
  let d : ℝ → ℝ := fun t => ∑ j, w j t
  have hwc (j : Fin m) : Continuous (w j) := by
    dsimp [w]
    exact (continuous_const.sub
      (unitIntervalClamp_continuous.sub continuous_const).abs).max continuous_const
  have hw0 (j : Fin m) (t : ℝ) : 0 ≤ w j t := le_max_right _ _
  have hd0 (t : ℝ) : 0 < d t := by
    obtain ⟨j,hj⟩ := hc t
    exact (lt_of_lt_of_le (lt_max_of_lt_left (sub_pos.mpr hj))
      (Finset.single_le_sum (fun i _ => hw0 i t) (Finset.mem_univ j)))
  have hdc : Continuous d := continuous_finsetSum _ (fun j _ => hwc j)
  let f : Fin m → ℝ → ℝ := fun j t => w j t / d t
  refine ⟨m,Fintype.card_pos,μ,f,hμ,?_,?_,?_,?_⟩
  · intro j
    exact (hwc j).div hdc (fun t => (hd0 t).ne')
  · intro j t
    exact ⟨div_nonneg (hw0 j t) (hd0 t).le,
      (div_le_one (hd0 t)).mpr (Finset.single_le_sum (fun i _ => hw0 i t) (Finset.mem_univ j))⟩
  · intro t
    dsimp [f]
    rw [←Finset.sum_div]
    exact div_self (hd0 t).ne'
  · intro j t ht hft
    by_contra hn
    have hn' : ε < |t-μ j| := lt_of_not_ge hn
    apply hft
    dsimp [f,w]
    rw [unitIntervalClamp_eq ht, max_eq_right (sub_nonpos.mpr hn'.le), zero_div]

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing D] in
lemma trace_re_mono (τ : TracialState D) {a b : D} (hab : a ≤ b) :
    (τ.functional a).re ≤ (τ.functional b).re :=
  (Complex.le_def.mp (τ.functional.monotone hab)).1
omit [StarOrderedRing D] in
lemma trace_re_nonneg (τ : TracialState D) {a : D} (ha : 0 ≤ a) :
    0 ≤ (τ.functional a).re := by simpa using trace_re_mono τ ha

def ProjectionPacking.ScalarGood {q : D} (P : ProjectionPacking q) (x : D) (ε : ℝ) : Prop :=
  ∀ i, ∃ μ ∈ Set.Icc (-1:ℝ) 1, ‖P.piece i*x*P.piece i - μ • P.piece i‖ ≤ ε

lemma ProjectionPacking.empty_good {q : D} (hq : IsStarProjection q) (x : D) (ε : ℝ) :
    (ProjectionPacking.empty hq).ScalarGood x ε := by intro i; cases i
lemma ProjectionPacking.append_good {q x : D} {ε : ℝ} (P : ProjectionPacking q)
    (hq : IsStarProjection q) (Q : ProjectionPacking P.residual)
    (hP : P.ScalarGood x ε) (hQ : Q.ScalarGood x ε) :
    (P.append hq Q).ScalarGood x ε := by
  intro i; cases i with
  | inl i => exact hP i
  | inr i => exact hQ i
omit [StarOrderedRing D] in
lemma ProjectionPacking.singleton_good {q p x : D} {ε μ : ℝ}
    (hp : IsStarProjection p) (hpq : p ≤ q) (hμ : μ ∈ Set.Icc (-1:ℝ) 1)
    (hn : ‖p*x*p-μ • p‖ ≤ ε) : (ProjectionPacking.singleton hp hpq).ScalarGood x ε :=
  fun _ => ⟨μ,hμ,hn⟩

lemma uniform_moving_corner_bound {J : Type*} [Fintype J]
    (f : J → ℝ → ℝ) (hf : ∀ j, Continuous (f j))
    {β : ℝ} (hβ : 0 < β) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ β ∧ ∀ (τ : TracialState D) (u v x : D)
      (hu : IsStarProjection u) (hv : IsStarProjection v),
      v ≤ u → IsSelfAdjoint x → ‖x‖ ≤ 1 → (τ.functional (u-v)).re < κ →
      ∀ j, ‖τ.functional (cornerCFC hu x (f j))-τ.functional (cornerCFC hv x (f j))‖ ≤ β := by
  classical
  have hp (j : J) : ∃ P : Polynomial ℝ,
      ∀ t ∈ Set.Icc (-1:ℝ) 1, |f j t-P.eval t| ≤ β/4 := by
    obtain ⟨P,hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (f j)
      (hf j).continuousOn (β/4) (by positivity)
    exact ⟨P,fun t ht => by simpa only [abs_sub_comm] using (hP t ht).le⟩
  choose P hP using hp
  let C : ℝ := 1+∑ j, cornerPolynomialConstant (P j)
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun index _ => cornerPolynomialConstant_nonneg (P index)))
  have hjC (j : J) : cornerPolynomialConstant (P j) ≤ C := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => cornerPolynomialConstant_nonneg (P j))
      (Finset.mem_univ j)
    dsimp [C]; linarith
  let κ := min β ((β/(2*C))^2)
  refine ⟨κ,lt_min hβ (sq_pos_of_pos (by positivity)),min_le_left _ _,?_⟩
  intro τ u v x hu hv hvu hx hxn ht j
  have huv : IsStarProjection (u-v) :=
    hv.sub_of_mul_eq_left hu ((hv.le_iff_mul_eq_left hu).mp hvu)
  have hn2 := traceTwoNorm_projection_sq τ huv
  have hn0 := traceTwoNorm_nonneg τ (u-v)
  have hsmall : traceTwoNorm τ (u-v) ≤ β/(2*C) := by
    have ht' : (τ.functional (u-v)).re < (β/(2*C))^2 := ht.trans_le (min_le_right _ _)
    have hb0 : 0 ≤ β/(2*C) := by positivity
    nlinarith
  have hprod : C * traceTwoNorm τ (u-v) ≤ β/2 := by
    have h := mul_le_mul_of_nonneg_left hsmall hC.le
    have he : C*(β/(2*C))=β/2 := by field_simp
    rwa [he] at h
  exact (moving_corner_modulus τ (P j) hu hv hx hxn (hf j) (by positivity) (hP j)).trans (by
    have h := mul_le_mul_of_nonneg_right (hjC j) hn0
    nlinarith)

omit [PartialOrder D] [StarOrderedRing D] in
lemma sum_cornerCFC {J : Type*} [Fintype J] {u x : D} (hu : IsStarProjection u)
    (hx : IsSelfAdjoint x) (f : J → ℝ → ℝ) (hf : ∀ j, Continuous (f j))
    (hsum : ∀ t, ∑ j, f j t=1) : (∑ j, cornerCFC hu x (f j))=u := by
  let a := ProjectionCorner.compress hu x
  have ha := compress_selfAdjoint hu hx
  have he : (∑ j, cfc (f j) a : ProjectionCorner hu)=1 := by
    rw [←cfc_sum f a Finset.univ (fun j _ => (hf j).continuousOn)]
    have hfun : (∑ j, f j) = fun _ : ℝ => 1 := by ext t; simpa using hsum t
    rw [hfun,cfc_const 1 a ha]
    simp
  have hh := congrArg (ProjectionCorner.inclusion hu) he
  rw [map_sum] at hh
  exact hh

lemma scalar_run {J I : Type*} [Fintype J] [DecidableEq J]
    (Γ : I → TracialState D) {x : D} {ε α β κ : ℝ}
    (f : J → ℝ → ℝ) (μ : J → ℝ)
    (hμ : ∀ j, μ j ∈ Set.Icc (-1:ℝ) 1)
    (hmove : ∀ (i : I) (u v : D) (hu : IsStarProjection u) (hv : IsStarProjection v),
      v ≤ u → (Γ i |>.functional (u-v)).re < κ → ∀ j,
      ‖(Γ i).functional (cornerCFC hu x (f j))-(Γ i).functional (cornerCFC hv x (f j))‖ ≤ β)
    (hsupply : ∀ (v : D) (hv : IsStarProjection v) (j : J),
      ∃ p : D, IsStarProjection p ∧ p ≤ v ∧ ‖p*x*p-μ j • p‖ ≤ ε ∧
        ∀ i, ((Γ i).functional (cornerCFC hv x (f j))).re-α ≤ ((Γ i).functional p).re)
    (u : D) (hu : IsStarProjection u) (s : Finset J) :
    ∃ P : ProjectionPacking u, P.ScalarGood x ε ∧
      ∀ i, ((Γ i).functional P.total).re < κ → ∀ j ∈ s,
        ((Γ i).functional (cornerCFC hu x (f j))).re ≤ ((Γ i).functional P.total).re+α+β := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨ProjectionPacking.empty hu,ProjectionPacking.empty_good hu x ε,by simp⟩
  | @insert j s hjs ih =>
    obtain ⟨P,hP,hbound⟩ := ih
    obtain ⟨p,hp,hpv,hpx,hpt⟩ := hsupply P.residual (P.residual_projection hu) j
    let Q := ProjectionPacking.singleton hp hpv
    let R := P.append hu Q
    have hPR : P.total ≤ R.total := P.total_le_append hu Q
    have hpR : p ≤ R.total := by
      rw [ProjectionPacking.append_total,ProjectionPacking.singleton_total]
      exact le_add_of_nonneg_left P.total_projection.nonneg
    refine ⟨R,P.append_good hu Q hP (ProjectionPacking.singleton_good hp hpv (hμ j) hpx),?_⟩
    intro i hi k hk
    have hPi : ((Γ i).functional P.total).re < κ := (trace_re_mono _ hPR).trans_lt hi
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      have he : u-P.residual=P.total := by dsimp [ProjectionPacking.residual]; abel
      have hm := hmove i u P.residual hu (P.residual_projection hu) P.residual_le (by rwa [he]) j
      have hreal := (Complex.re_le_norm ((Γ i).functional (cornerCFC hu x (f j))-
        (Γ i).functional (cornerCFC (P.residual_projection hu) x (f j)))).trans hm
      rw [Complex.sub_re] at hreal
      have hlocal := hpt i
      have hmono := trace_re_mono (Γ i) hpR
      linarith
    · exact (hbound i hPi k hk).trans (by linarith [trace_re_mono (Γ i) hPR])

end DirectComparison
end

end OAI
