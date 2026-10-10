import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierInitialPoissonBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.Cut

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialBounds_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma initial_quadratic_bound {Z r a d : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) (hd : 0 ≤ d) (hd2 : d ≤ 2*r) :
    a*d^2 ≤ Z/(20*r) := by
  have hh : d^2 ≤ (2*r)^2 := by nlinarith
  calc
    _ ≤ a*(2*r)^2 := mul_le_mul_of_nonneg_left hh ha
    _ = 4*a*r^2 := by ring
    _ ≤ _ := hs

lemma initial_branch_lower {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ (53/50)*r)
    (hp : tfPotential ρ x ≤ Z/(10*r)) :
    (7/50)*(Z/r) < initialBranch Z r a ρ x := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  have hv : (50/53)*(Z/r) ≤ Z/‖x‖ := by
    apply (le_div_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ (50/53)*(Z/r) by positivity)
    have he : (50/53)*(Z/r)*((53/50)*r) = Z := by field_simp
    exact hh.trans_eq he
  have hp' : Z/(10*r) = (1/10)*(Z/r) := by ring
  have hv' : 0 ≤ a*‖x‖^2 := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  rw [hp'] at hp
  have hzr : 0 < Z/r := div_pos hZ hr
  nlinarith

lemma initial_branch_upper {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : r ≤ ‖x‖) (hx2 : ‖x‖ ≤ 2*r) (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x ≤ 2*(Z/r) := by
  have hv := div_le_div_of_nonneg_left hZ.le hr hx
  have hq := initial_quadratic_bound hr ha hs (norm_nonneg x) hx2
  have he : Z/(20*r) = (1/20)*(Z/r) := by ring
  rw [he] at hq
  have hn : 0 ≤ Z/r := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  nlinarith

lemma initial_branch_negative {Z r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) {ρ : TFSpace → ℝ} {x : TFSpace}
    (hx : (19/10)*r < ‖x‖) (hx2 : ‖x‖ ≤ 2*r) (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x < 0 := by
  have hd : 0 < ‖x‖ := lt_trans (by positivity) hx
  have hv : Z/‖x‖ ≤ (10/19)*(Z/r) := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hx.le (show 0 ≤ (10/19)*(Z/r) by positivity)
    have he : (10/19)*(Z/r)*((19/10)*r) = Z := by field_simp
    nlinarith
  have hq := initial_quadratic_bound hr ha hs (norm_nonneg x) hx2
  have he : Z/(20*r) = (1/20)*(Z/r) := by ring
  rw [he] at hq
  have hn : 0 < Z/r := by positivity
  simp only [initialBranch,initialOffset,nuclearField,mul_div_assoc]
  nlinarith

lemma initial_outer_upper {Z B r : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hB : 0 ≤ B)
    (hsmall : B ≤ Z*r^3/10) {x : TFSpace} (hx : r ≤ ‖x‖) :
    outerBarrier B r x ≤ (1/10)*(Z/r) := by
  have hd : 0 < ‖x‖ := hr.trans_le hx
  apply (outerBarrier_bounds hB hr hx).2.trans
  calc
    _ ≤ B/r^4 := div_le_div_of_nonneg_left hB (pow_pos hr 4) (by gcongr)
    _ ≤ (Z*r^3/10)/r^4 := div_le_div_of_nonneg_right hsmall (by positivity)
    _ = _ := by field_simp

lemma initial_lower_overlap {Z B r a : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hsmall : B ≤ Z*r^3/10)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx1 : ‖x‖ ≤ (53/50)*r)
    (hp : tfPotential ρ x ≤ Z/(10*r)) :
    outerBarrier B r x < initialBranch Z r a ρ x := by
  have hu := initial_outer_upper hZ hr hB hsmall hx
  have hl := initial_branch_lower hZ hr ha hx hx1 hp
  have hn : 0 < Z/r := by positivity
  linarith

lemma initial_branch_cap {Z C r a : ℝ} (hZ : 0 < Z) (hr : 0 < r) (ha : 0 ≤ a)
    (hs : 4*a*r^2 ≤ Z/(20*r)) (hC : 32*Z*r^3 ≤ C)
    {ρ : TFSpace → ℝ} {x : TFSpace} (hx : r ≤ ‖x‖) (hx2 : ‖x‖ ≤ 2*r)
    (hp : 0 ≤ tfPotential ρ x) :
    initialBranch Z r a ρ x ≤ C/‖x‖^4 := by
  apply (initial_branch_upper hZ hr ha hs hx hx2 hp).trans
  have hd : 0 < ‖x‖ := hr.trans_le hx
  apply (le_div_iff₀ (pow_pos hd 4)).mpr
  calc
    _ ≤ (2*(Z/r))*(2*r)^4 := by gcongr
    _ = 32*Z*r^3 := by field_simp; ring
    _ ≤ C := hC

end Work_BarrierInitialBounds_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped ContDiff Topology

open CoulombAnalysis

def initializedOffset (Z B r a : ℝ) (ρ : TFSpace → ℝ) : TFSpace → ℝ :=
  cutMaximum r (2*r) (initialOffset Z r a ρ) (outerOffset Z B r)

def initializedBarrier (Z B r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  nuclearField Z x+initializedOffset Z B r a ρ x

lemma truncated_density_exterior {ρ : TFSpace → ℝ} {r : ℝ}
    (hs : Function.support ρ ⊆ ball 0 r) {x : TFSpace} (hx : r ≤ ‖x‖) : ρ x = 0 := by
  by_contra hn
  have hh := hs hn
  have hh' : ‖x‖ < r := mem_ball_zero_iff.mp hh
  linarith

lemma initialBranch_weak_reaction {Z r a k : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hsmall : 4*a*r^2 ≤ Z/(20*r))
    (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    {ρ : TFSpace → ℝ} {M : ℝ} (hm : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hb : ∀ x, ρ x ≤ M) (hs : Function.support ρ ⊆ ball 0 r) :
    WeakNuclearLowerOn {x : TFSpace | ‖x‖ < 2*r} Z (initialBranch Z r a ρ)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (initialBranch Z r a ρ x)) := by
  have hl : LocallyIntegrable (fun x => 4*Real.pi*ρ x) :=
    ((bounded_support_integrable hm hn hb hs).const_mul (4*Real.pi)).locallyIntegrable
  have hli := nuclear_source_locallyIntegrable Z k hr hl (outerCoefficient_measurable r)
    (outerCoefficient_bound r) (outerCoefficient_zero r) (initialOffset_continuous hm hn hb hs Z r a)
  apply ((initialBranch_weak_nuclear hm hn hb hs Z r a).mono_set (subset_univ _)).source_mono
    (hl.add (locallyIntegrable_const (6*a))) hli
  intro x hx
  by_cases hx' : r ≤ ‖x‖
  · simp only [outerCoefficient,ite_eq_left hx',one_mul]
    have hh := initial_branch_upper hZ hr ha hsmall hx' hx.le
      (tfPotential_nonneg (ae_of_all _ hn) x)
    have hf := (reaction_monotone hk hh).trans hreact
    change reaction k (nuclearField Z x+initialOffset Z r a ρ x) ≤ 6*a at hf
    linarith
  · simp only [outerCoefficient,ite_eq_right hx',zero_mul,add_zero]
    linarith

lemma outerOffset_weak_initial_source {Z B r k : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hk : 0 ≤ k) (hsmall : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {ρ : TFSpace → ℝ} (hs : Function.support ρ ⊆ ball 0 r) :
    WeakNuclearLowerOn {x : TFSpace | r < ‖x‖} Z
      (fun x => nuclearField Z x+outerOffset Z B r x)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (nuclearField Z x+outerOffset Z B r x)) := by
  apply (outerOffset_weak_nuclear hB hr hk hsmall Z).congr_source
  intro x hx
  change r < ‖x‖ at hx
  simp only [truncated_density_exterior hs hx.le,outerCoefficient,ite_eq_left hx.le,
    mul_zero,zero_add,one_mul]

theorem initialized_barrier_weak {Z B r a k : ℝ} (hZ : 0 < Z) (hB : 0 < B)
    (hr : 0 < r) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hquad : 4*a*r^2 ≤ Z/(20*r)) (hreact : reaction k (2*(Z/r)) ≤ 6*a)
    (hBsmall : B ≤ Z*r^3/10) (hsub : 4*Real.pi*k*Real.sqrt B ≤ 19/2)
    {ρ : TFSpace → ℝ} {M : ℝ} (hm : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (hb : ∀ x, ρ x ≤ M) (hs : Function.support ρ ⊆ ball 0 r)
    (hgood : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ (53/50)*r → tfPotential ρ x ≤ Z/(10*r)) :
    Continuous (initializedOffset Z B r a ρ) ∧
    WeakNuclearLowerOn univ Z (initializedBarrier Z B r a ρ)
      (fun x => 4*Real.pi*ρ x+outerCoefficient r x*reaction k (initializedBarrier Z B r a ρ x)) := by
  have ht : r < (53/50)*r := by linarith
  have htL : (53/50)*r < (19/10)*r := by linarith
  have hLR : (19/10)*r < 2*r := by linarith
  have hlo : ∀ x : TFSpace, r ≤ ‖x‖ → ‖x‖ < (53/50)*r →
      outerOffset Z B r x ≤ initialOffset Z r a ρ x := by
    intro x hx hx'
    have hh := initial_lower_overlap hZ hr ha hB.le hBsmall hx hx'.le (hgood x hx hx'.le)
    rw [← nuclear_outerOffset_eq (Z := Z) hx] at hh
    change nuclearField Z x+outerOffset Z B r x < nuclearField Z x+initialOffset Z r a ρ x at hh
    linarith
  have hhi : ∀ x : TFSpace, (19/10)*r < ‖x‖ → ‖x‖ < 2*r →
      initialOffset Z r a ρ x ≤ outerOffset Z B r x := by
    intro x hx hx'
    have hx0 : r ≤ ‖x‖ := by linarith
    have hh := initial_branch_negative hZ hr ha hquad hx hx'.le (tfPotential_nonneg (ae_of_all _ hn) x)
    have ho := (outerBarrier_bounds hB.le hr hx0).1
    have hp : 0 ≤ (7*B/8)/‖x‖^4 := by positivity
    rw [← nuclear_outerOffset_eq (Z := Z) hx0] at ho
    change nuclearField Z x+initialOffset Z r a ρ x < 0 at hh
    linarith
  have hu := initialOffset_continuous hm hn hb hs Z r a
  have hv := outerOffset_continuous Z B hr
  refine ⟨cutMaximum_continuous ht htL hLR hlo hhi hu hv,?_⟩
  have hwi := initialBranch_weak_reaction hZ hr ha hk hquad hreact hm hn hb hs
  have hwo := outerOffset_weak_initial_source (Z := Z) hB hr hk hsub hs
  apply cutMaximum_weak_nuclear ht htL hLR hlo hhi Z k hr hu hv
    (((bounded_support_integrable hm hn hb hs).const_mul (4*Real.pi)).locallyIntegrable)
    (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r)
  · exact hwi.mono_set (fun x hx => (show ‖x‖ < (53/50)*r from hx).trans (htL.trans hLR))
  · exact hwi.mono_set (fun _ hx => hx.2)
  · exact hwo.mono_set (fun _ hx => hx.1)
  · exact hwo.mono_set (fun x hx => (ht.trans htL).trans hx)

end CoulombBarrier

end

end OAI
