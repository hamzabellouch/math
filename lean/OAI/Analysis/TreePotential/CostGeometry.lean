import OAI.Analysis.TreePotential.Leakage

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section FiniteMassApproximation
open Filter Topology
open scoped Classical
variable {I : Type*}

abbrev FiniteMass (I : Type*) := {μ : L1Mass I // (Function.support μ).Finite}

instance : Nonempty (FiniteMass I) := ⟨⟨0, by
  change (Function.support (fun _ : I => (0:ℝ))).Finite
  simp⟩⟩

def finiteMassPartial (μ : L1Mass I) (S : Finset I) : FiniteMass I :=
  ⟨∑ i ∈ S, lp.single 1 i (μ i), S.finite_toSet.subset (by
    intro j hj
    by_contra hjs
    change j ∉ S at hjs
    apply hj
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single,
      ite_eq_right hjs])⟩

lemma tendsto_finiteMassPartial (μ : L1Mass I) :
    Tendsto (fun S => (finiteMassPartial μ S).val) atTop (𝓝 μ) :=
  lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) μ

lemma iInf_finiteMass_eq (f : L1Mass I → ℝ) (hf : Continuous f) (hn : ∀ μ, 0 ≤ f μ) :
    (⨅ μ : FiniteMass I, f μ.val) = ⨅ μ : L1Mass I, f μ := by
  have hfull : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨μ,rfl⟩; exact hn μ⟩
  have hfin : BddBelow (Set.range (fun μ : FiniteMass I => f μ.val)) :=
    ⟨0, by rintro _ ⟨μ,rfl⟩; exact hn μ.val⟩
  apply le_antisymm
  · apply le_ciInf
    intro μ
    have ht := (hf.tendsto μ).comp (tendsto_finiteMassPartial μ)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall (fun S => ciInf_le hfin (finiteMassPartial μ S)))
  · apply le_ciInf
    intro μ
    exact ciInf_le hfull μ.val

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The same linear infimum with exactly finite signed endpoint masses;
no norm attainment or optimizer is inserted. -/
theorem linearCost_finite_mass (B : L1Mass I →L[ℝ] H) (x : H) :
    linearCost B x = ⨅ μ : FiniteMass I, ‖x-B μ.val‖+‖μ.val‖ := by
  symm
  exact iInf_finiteMass_eq (fun μ : L1Mass I => ‖x-B μ‖+‖μ‖)
    (by fun_prop) (fun _ => by positivity)

/-- Truncation also preserves the quadratic normalization, rather than
replacing the Euclidean representation cost by a linear one. -/
theorem quadraticCost_finite_mass (B : L1Mass I →L[ℝ] H) (x : H) :
    quadraticCost B x = ⨅ μ : FiniteMass I, Real.sqrt (‖x-B μ.val‖^2+‖μ.val‖^2) := by
  symm
  exact iInf_finiteMass_eq (fun μ : L1Mass I => Real.sqrt (‖x-B μ‖^2+‖μ‖^2))
    (by fun_prop) (fun _ => Real.sqrt_nonneg _)

end FiniteMassApproximation

lemma sqrt_tail_shift {r R d c : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hh : r ≤ R+d) :
    Real.sqrt (c^2+r^2/16) ≤ Real.sqrt (c^2+R^2/16)+d/4 := by
  have he := sqrt_shift (r := r/4) (R := R/4) (d := d/4) (c := c^2)
    (by positivity) (by positivity) (by positivity) (sq_nonneg c) (by linarith)
  convert he using 1 <;> congr 1 <;> ring_nf

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

lemma linear_finite_center_compare (A : FiniteOuterHead) (x p y : LinearOuter)
    (hp : linearOuterHead A.nodes A.initial p = p) :
    Real.sqrt (‖x‖^2+‖y‖^2/16) ≤ max ‖x+y‖ ‖x-y‖+
      2*‖x-p‖+‖linearOuterHead A.nodes A.initial y‖/4 := by
  have hcent : ‖x‖ ≤ ‖p‖+‖x-p‖ := by linarith [norm_sub_norm_le x p]
  have htail : ‖y‖ ≤ ‖y-linearOuterHead A.nodes A.initial y‖+
      ‖linearOuterHead A.nodes A.initial y‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (y-linearOuterHead A.nodes A.initial y) (linearOuterHead A.nodes A.initial y)
  have h1 := sqrt_shift (norm_nonneg x) (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ ‖y‖^2/16 by positivity) hcent
  have h2 := sqrt_tail_shift (c := ‖p‖) (norm_nonneg y)
    (norm_nonneg (y-linearOuterHead A.nodes A.initial y))
    (norm_nonneg (linearOuterHead A.nodes A.initial y)) htail
  have he := linearOuter_midpoint A.nodes A.initial p y hp
  have hc := midpoint_center_perturbation x p y 1
  simp only [one_smul, norm_sub_rev p x] at hc
  have hmax1 := le_max_left ‖x+y‖ ‖x-y‖
  have hmax2 := le_max_right ‖x+y‖ ‖x-y‖
  linarith

/-- The center is approximated before taking the lower limit. Boundedness and
weak nullity are retained, and the norm lower limit is the ordinary real liminf. -/
theorem linear_weak_sequence_clipping (x : LinearOuter) (y : ℕ → LinearOuter)
    (hy : WeaklyNull y) (hbounded : BddAbove (Set.range (fun j => ‖y j‖))) :
    Real.sqrt (‖x‖^2+(Filter.liminf (fun j => ‖y j‖) atTop)^2/16) ≤
      Filter.liminf (fun j => max ‖x+y j‖ ‖x-y j‖) atTop := by
  obtain ⟨R,hR⟩ := hbounded
  have hn : ∀ j, ‖y j‖ ≤ R := fun j => hR (Set.mem_range_self j)
  have hbelow := Filter.isBoundedUnder_of_eventually_ge
    (Filter.Eventually.of_forall (fun j => norm_nonneg (y j))) (f := atTop)
  have habove := Filter.isBoundedUnder_of_eventually_le
    (Filter.Eventually.of_forall hn) (f := atTop)
  let L := Filter.liminf (fun j => ‖y j‖) atTop
  have hL : 0 ≤ L := Filter.le_liminf_of_le habove.isCoboundedUnder_ge
    (Filter.Eventually.of_forall (fun j => norm_nonneg (y j)))
  have hM : ∀ j, max ‖x+y j‖ ‖x-y j‖ ≤ ‖x‖+R := by
    intro j
    exact max_le ((norm_add_le x (y j)).trans (by linarith [hn j]))
      ((norm_sub_le x (y j)).trans (by linarith [hn j]))
  have hMabove := Filter.isBoundedUnder_of_eventually_le
    (Filter.Eventually.of_forall hM) (f := atTop)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p,A,hp,hA⟩ := linear_finite_head_approx x (show 0 < ε/4 by positivity)
  have hlimnorm : ∀ᶠ j in atTop, L-ε < ‖y j‖ :=
    Filter.eventually_lt_of_lt_liminf (show L-ε < L by linarith) hbelow
  have hlimhead : ∀ᶠ j in atTop, ‖linearOuterHead A.nodes A.initial (y j)‖ < ε :=
    ((tendsto_order.mp (linear_head_weaklyNull hy A)).2 ε hε)
  have hev : ∀ᶠ j in atTop,
      Real.sqrt (‖x‖^2+L^2/16)-ε ≤ max ‖x+y j‖ ‖x-y j‖ := by
    filter_upwards [hlimnorm, hlimhead] with j hj hhead
    have hs := sqrt_tail_shift (c := ‖x‖) hL (norm_nonneg (y j)) hε.le
      (show L ≤ ‖y j‖+ε by linarith)
    have hc := linear_finite_center_compare A x p (y j) hA
    linarith
  have hh := Filter.le_liminf_of_le hMabove.isCoboundedUnder_ge hev
  change Real.sqrt (‖x‖^2+L^2/16) ≤ _
  linarith

/-- Uniform bottom-up implication on the Hilbert sum; the changing finite heads
are allowed to depend on j, and no fixed-head reduction is made. -/
theorem linear_bottom_up_outer (A : ℕ → FiniteOuterHead) (x y : ℕ → LinearOuter)
    (hx : ∀ j, linearOuterHead (A j).nodes (A j).initial (x j) = x j)
    (hy : ∀ j, linearOuterHead (A j).nodes (A j).initial (y j) = 0)
    (hp : ∀ j, ‖x j+y j‖ ≤ 1) (hm : ∀ j, ‖x j-y j‖ ≤ 1)
    (hxn : Tendsto (fun j => ‖x j‖) atTop (𝓝 1)) :
    Tendsto (fun j => ‖y j‖) atTop (𝓝 0) := by
  have he (j : ℕ) : ‖y j‖ ≤ 4*Real.sqrt (1-‖x j‖^2) := by
    have hh := linearOuter_tail_four (A j) (x j) (y j) (hx j) zero_le_one (hp j) (hm j)
    simpa only [hy j, sub_zero, one_pow] using hh
  have ht : Tendsto (fun j => 4*Real.sqrt (1-‖x j‖^2)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun j => (1:ℝ)-‖x j‖^2) atTop (𝓝 (1-1^2)) :=
      tendsto_const_nhds.sub (hxn.pow 2)
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsub
    have hh := hs.const_mul 4
    simpa using hh
  exact squeeze_zero (fun j => norm_nonneg (y j)) he ht

/-- The finite head depends only on x,delta, not on the displacement. -/
theorem quadratic_relative_tail_72 (x : QuadraticOuter) (hx : x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : FiniteOuterHead, ∀ u : QuadraticOuter,
      ‖x+u‖ ≤ (1+δ)*‖x‖ → ‖x-u‖ ≤ (1+δ)*‖x‖ →
      ‖u-quadraticOuterHead A.nodes A.initial u‖ ≤ 72*Real.sqrt δ*‖x‖ := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨p,A,hp,hA⟩ := quadratic_finite_head_approx x (mul_pos hδ hxn)
  refine ⟨A, ?_⟩
  intro u hu hv
  have hpplus : ‖p+u‖ ≤ (1+2*δ)*‖x‖ := by
    have he : ‖p+u‖ ≤ ‖x+u‖+‖x-p‖ := by
      have hh := norm_sub_norm_le (p+u) (x+u)
      rw [add_sub_add_right_eq_sub, norm_sub_rev p x] at hh
      linarith
    nlinarith
  have hpminus : ‖p-u‖ ≤ (1+2*δ)*‖x‖ := by
    have he : ‖p-u‖ ≤ ‖x-u‖+‖x-p‖ := by
      have hh := norm_sub_norm_le (p-u) (x-u)
      rw [sub_sub_sub_cancel_right, norm_sub_rev p x] at hh
      linarith
    nlinarith
  have hplower : (1-δ)*‖x‖ ≤ ‖p‖ := by
    have hh := norm_sub_norm_le x p
    nlinarith
  have hplower0 : 0 ≤ (1-δ)*‖x‖ := mul_nonneg (by linarith) hxn.le
  have hplower2 : ((1-δ)*‖x‖)^2 ≤ ‖p‖^2 := by nlinarith [norm_nonneg p]
  have he := quadraticOuter_midpoint_sq A.nodes A.initial p u hA
  have hR0 : 0 ≤ (1+2*δ)*‖x‖ := by positivity
  have hb : ‖p‖^2+‖u-quadraticOuterHead A.nodes A.initial u‖^2/16 ≤ ((1+2*δ)*‖x‖)^2 := by
    nlinarith [norm_nonneg (p+u), norm_nonneg (p-u)]
  have hd2 : δ^2*‖x‖^2 ≤ δ*‖x‖^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖x‖)
    nlinarith
  have ht : ‖u-quadraticOuterHead A.nodes A.initial u‖^2 ≤ 144*δ*‖x‖^2 := by
    nlinarith
  have hs := Real.sq_sqrt hδ.le
  have hsn := Real.sqrt_nonneg δ
  have hsmall : ‖u-quadraticOuterHead A.nodes A.initial u‖ ≤ 12*Real.sqrt δ*‖x‖ := by
    nlinarith [mul_nonneg hsn hxn.le]
  nlinarith [mul_nonneg hsn hxn.le]

lemma quadratic_finite_center_compare (A : FiniteOuterHead) (x p y : QuadraticOuter)
    (hp : quadraticOuterHead A.nodes A.initial p = p) :
    Real.sqrt (‖x‖^2+‖y‖^2/16) ≤ max ‖x+y‖ ‖x-y‖+
      2*‖x-p‖+‖quadraticOuterHead A.nodes A.initial y‖/4 := by
  have hcent : ‖x‖ ≤ ‖p‖+‖x-p‖ := by linarith [norm_sub_norm_le x p]
  have htail : ‖y‖ ≤ ‖y-quadraticOuterHead A.nodes A.initial y‖+
      ‖quadraticOuterHead A.nodes A.initial y‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (y-quadraticOuterHead A.nodes A.initial y) (quadraticOuterHead A.nodes A.initial y)
  have h1 := sqrt_shift (norm_nonneg x) (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ ‖y‖^2/16 by positivity) hcent
  have h2 := sqrt_tail_shift (c := ‖p‖) (norm_nonneg y)
    (norm_nonneg (y-quadraticOuterHead A.nodes A.initial y))
    (norm_nonneg (quadraticOuterHead A.nodes A.initial y)) htail
  have he := quadraticOuter_midpoint A.nodes A.initial p y hp
  have hc := midpoint_center_perturbation x p y 1
  simp only [one_smul, norm_sub_rev p x] at hc
  have hmax1 := le_max_left ‖x+y‖ ‖x-y‖
  have hmax2 := le_max_right ‖x+y‖ ‖x-y‖
  linarith

end CostHeads

section SymmetricLenses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma lens_half_difference (x u v : E) {R : ℝ}
    (hup : ‖x+u‖ ≤ R) (hum : ‖x-u‖ ≤ R)
    (hvp : ‖x+v‖ ≤ R) (hvm : ‖x-v‖ ≤ R) :
    ‖x+(1/2:ℝ) • (u-v)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (u-v)‖ ≤ R := by
  have hp : x+(1/2:ℝ) • (u-v) = (1/2:ℝ) • ((x+u)+(x-v)) := by module
  have hm : x-(1/2:ℝ) • (u-v) = (1/2:ℝ) • ((x-u)+(x+v)) := by module
  rw [hp, hm, norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  constructor
  · nlinarith [norm_add_le (x+u) (x-v)]
  · nlinarith [norm_add_le (x-u) (x+v)]

end SymmetricLenses

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

/-- Infinite-lens obstruction using finite-rank heads and finite-center approximation.
The denominator 64 implies the weaker numerical bounds. -/

theorem quadratic_lens_sixtyfour (x : QuadraticOuter) (y : ℕ → QuadraticOuter)
    {R ε : ℝ} (hε : 0 < ε) (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖) :
    ‖x‖^2+ε^2/64 ≤ R^2 := by
  have hR : 0 ≤ R := (norm_nonneg (x+y 0)).trans (hp 0)
  have hy : ∀ j, ‖y j‖ ≤ R := by
    intro j
    have he := norm_displacement_le_avg x (y j)
    linarith [hp j, hm j]
  have hsqrt : Real.sqrt (‖x‖^2+ε^2/64) ≤ R := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨p,A,hd,hA⟩ := quadratic_finite_head_approx x (show 0 < δ/4 by positivity)
    obtain ⟨i,j,hij,hclose⟩ := finiteRank_close_pair
      (quadraticOuterHead A.nodes A.initial) y hy hδ
    let z := (1/2:ℝ) • (y i-y j)
    have hzn : ‖z‖ = ‖y i-y j‖/2 := by
      dsimp [z]
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      ring
    have hhalf : ε/2 ≤ ‖z‖ := by rw [hzn]; linarith [hsep i j hij]
    have hhead : ‖quadraticOuterHead A.nodes A.initial z‖ < δ/2 := by
      dsimp [z]
      rw [map_smul, map_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      linarith
    have hends := lens_half_difference x (y i) (y j) (hp i) (hm i) (hp j) (hm j)
    change ‖x+z‖ ≤ R ∧ ‖x-z‖ ≤ R at hends
    have hc := quadratic_finite_center_compare A x p z hA
    have hmono : Real.sqrt (‖x‖^2+ε^2/64) ≤ Real.sqrt (‖x‖^2+‖z‖^2/16) := by
      apply Real.sqrt_le_sqrt
      nlinarith [norm_nonneg z]
    have hb := max_le hends.1 hends.2
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ ‖x‖^2+ε^2/64 by positivity)
  nlinarith [Real.sqrt_nonneg (‖x‖^2+ε^2/64)]

theorem quadratic_lens_eight (x : QuadraticOuter) (y : ℕ → QuadraticOuter)
    {R ε : ℝ} (hε : 0 < ε) (hp : ∀ j, ‖x+y j‖ ≤ R) (hm : ∀ j, ‖x-y j‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖y i-y j‖) :
    ‖x‖^2+ε^2/256 ≤ R^2 := by
  have he := quadratic_lens_sixtyfour x y hε hp hm hsep
  nlinarith [sq_nonneg ε]

theorem quadratic_lens_twelve (x : QuadraticOuter) (y : ℕ → QuadraticOuter)
    {r d : ℝ} (hd : 0 < d) (hp : ∀ j, ‖x+y j‖ ≤ r) (hm : ∀ j, ‖x-y j‖ ≤ r)
    (hsep : ∀ i j, i ≠ j → 2*d ≤ ‖y i-y j‖) :
    ‖x‖^2+d^2/144 ≤ r^2 := by
  have he := quadratic_lens_sixtyfour x y (show 0 < 2*d by positivity) hp hm hsep
  nlinarith [sq_nonneg d]

theorem quadratic_lens_seven (x : QuadraticOuter) (y : ℕ → QuadraticOuter)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : ∀ j, ‖x+y j‖ ≤ 1) (hm : ∀ j, ‖x-y j‖ ≤ 1)
    (hsep : ∀ i j, i ≠ j → 2*c ≤ ‖y i-y j‖) :
    ‖x‖ ≤ 1-c^2/2000 := by
  have he := quadratic_lens_sixtyfour x y (show 0 < 2*c by positivity) hp hm hsep
  have hc2 : c^2 ≤ 1 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg x) (show 0 ≤ 1-c^2/2000 by linarith)).mp
  nlinarith [sq_nonneg (c^2)]

theorem quadratic_lens_nine (x : QuadraticOuter) {ρ γ : ℝ}
    (hρ : 0 < ρ) (hγ : 0 < γ) (hγhalf : γ < 1/2)
    (hsmall : 9*Real.sqrt ((1+γ)^2-(1-2*γ)^2) < ρ/3)
    (hx : 1-γ ≤ ‖x‖) :
    ¬ ∃ y : ℕ → QuadraticOuter, (∀ j, ‖x+y j‖ ≤ 1) ∧ (∀ j, ‖x-y j‖ ≤ 1) ∧
      ∀ i j, i ≠ j → ρ ≤ ‖y i-y j‖ := by
  rintro ⟨y,hp,hm,hsep⟩
  have he := quadratic_lens_sixtyfour x y hρ hp hm hsep
  have hd : 0 ≤ (1+γ)^2-(1-2*γ)^2 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg ((1+γ)^2-(1-2*γ)^2)
  have hx2 : (1-γ)^2 ≤ ‖x‖^2 := by nlinarith [norm_nonneg x]
  nlinarith

end CostHeads

section FurtherModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def maximumModulus (t : ℝ) : EReal :=
  ⨅ x : {x : E // ‖x‖ = 1}, ⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖},
      ((max ‖x.val+t • y.val‖ ‖x.val-t • y.val‖-1 : ℝ) : EReal)

lemma averagedModulus_le_maximum (t : ℝ) : averagedModulus E t ≤ maximumModulus E t := by
  apply iInf_mono
  intro x
  apply iSup_mono
  intro F
  apply iInf_mono
  intro y
  apply EReal.coe_le_coe_iff.mpr
  linarith [le_max_left ‖x.val+t • y.val‖ ‖x.val-t • y.val‖,
    le_max_right ‖x.val+t • y.val‖ ‖x.val-t • y.val‖]

end FurtherModuli

lemma fractional_energy_bound {e z : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hz : 0 ≤ z) (h : z^2 ≤ 48*e) :
    z^2 ≤ (519/2:ℝ)*e^(1/3:ℝ) ∧ z ≤ 17*e^(1/6:ℝ) := by
  have hem : e ≤ e^(1/3:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge he he1 (show (1/3:ℝ) ≤ 1 by norm_num)
    simpa using hh
  have he3 := Real.rpow_nonneg he.le (1/3:ℝ)
  have he6 := Real.rpow_nonneg he.le (1/6:ℝ)
  have hs : (e^(1/6:ℝ))^2 = e^(1/3:ℝ) := by
    have hh := (Real.rpow_mul_natCast he.le (1/6:ℝ) 2).symm
    norm_num at hh
    exact hh
  constructor <;> nlinarith

namespace CostHeads
open TreeCalculus BlockCalculus Filter Topology
open scoped Classical

/-- Empty heads are used exactly on zero components of the center. -/

def activeHead (A : FiniteOuterHead) (x : QuadraticOuter) : FiniteOuterHead where
  nodes n := if x n = 0 then ∅ else A.nodes n
  initial n := by
    by_cases h : x n = 0
    · simp only [h, ↓reduceIte]
      intro s r hs
      exact hs.elim
    · simpa only [h, ↓reduceIte] using A.initial n
  finite_nodes := A.finite_nodes.subset (by
    intro s hs
    change s.2.val ∈ (if x s.1 = 0 then ∅ else A.nodes s.1) at hs
    change s.2.val ∈ A.nodes s.1
    by_cases h : x s.1 = 0
    · simp only [h, ↓reduceIte, Set.mem_empty_iff_false] at hs
    · simpa only [h, ↓reduceIte] using hs)

lemma activeHead_center (A : FiniteOuterHead) (x : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) :
    quadraticOuterHead (activeHead A x).nodes (activeHead A x).initial x = x := by
  apply lp.ext
  funext n
  by_cases h : x n = 0
  · simp [quadraticOuterHead_apply, h]
  · have hh := congrArg (fun z : QuadraticOuter => z n) hx
    simpa only [quadraticOuterHead_apply, activeHead, h, ↓reduceIte] using hh

lemma mem_active_tail (A : FiniteOuterHead) (x y : QuadraticOuter) :
    y ∈ (quadraticCoordinateTail (activeHead A x)).space ↔
      ∀ n, x n ≠ 0 → quadraticHead (n+1) (A.nodes n) (A.initial n) (y n) = 0 := by
  rw [mem_quadraticCoordinateTail]
  constructor
  · intro h n hn
    have hh := congrArg (fun z : QuadraticOuter => z n) h
    simpa only [quadraticOuterHead_apply, activeHead, hn, ↓reduceIte, lp.coeFn_zero, Pi.zero_apply] using hh
  · intro h
    apply lp.ext
    funext n
    by_cases hn : x n = 0
    · apply (quadraticBlockEquiv (n+1)).injective
      ext s
      simp [quadraticOuterHead_apply, quadraticHead_equiv, activeHead, hn, head_apply]
    · simpa only [quadraticOuterHead_apply, activeHead, hn, ↓reduceIte, lp.coeFn_zero, Pi.zero_apply] using h n hn

theorem quadratic_finite_centers (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) (hxn : ‖x‖ = 1)
    (hy : ∀ n, x n ≠ 0 → quadraticHead (n+1) (A.nodes n) (A.initial n) (y n) = 0)
    {e : ℝ} (he : 0 < e) (he8 : e ≤ 1/8)
    (hp : ‖x+y‖ ≤ 1+e) (hm : ‖x-y‖ ≤ 1+e) :
    ‖y‖^2 ≤ (519/2:ℝ)*e^(1/3:ℝ) ∧ ‖y‖ ≤ 17*e^(1/6:ℝ) := by
  have hhy := (mem_quadraticCoordinateTail (activeHead A x) y).mp
    ((mem_active_tail A x y).mpr hy)
  have hh := quadraticOuter_midpoint (activeHead A x).nodes (activeHead A x).initial
    x y (activeHead_center A x hx)
  rw [hhy, sub_zero, hxn] at hh
  have hs := Real.sq_sqrt (show 0 ≤ (1:ℝ)^2+‖y‖^2/16 by positivity)
  have hb : Real.sqrt (1^2+‖y‖^2/16) ≤ 1+e := by linarith
  have hy2 : ‖y‖^2 ≤ 48*e := by
    have he1 : e ≤ 1 := by linarith
    nlinarith [Real.sqrt_nonneg (1^2+‖y‖^2/16), mul_nonneg he.le (sub_nonneg.mpr he1)]
  exact fractional_energy_bound he (by linarith) (norm_nonneg y) hy2

theorem quadratic_completed_centers (x : QuadraticOuter) (hx : ‖x‖ = 1)
    {e : ℝ} (he : 0 < e) (he16 : e ≤ 1/16) :
    ∃ F : ClosedFiniteCodim QuadraticOuter, ∀ y, y ∈ F.space →
      ‖x+y‖ ≤ 1+e → ‖x-y‖ ≤ 1+e → ‖y‖ ≤ 17*(2*e)^(1/6:ℝ) := by
  obtain ⟨p,A,hd,hA⟩ := quadratic_finite_head_approx x (show 0 < e/2 by positivity)
  refine ⟨quadraticCoordinateTail A, ?_⟩
  intro y hy hp hm
  have hh := quadratic_finite_center_compare A x p y hA
  rw [(mem_quadraticCoordinateTail A y).mp hy, norm_zero, hx] at hh
  have hb := max_le hp hm
  have hs := Real.sq_sqrt (show 0 ≤ (1:ℝ)^2+‖y‖^2/16 by positivity)
  have hsq : ‖y‖^2 ≤ 48*(2*e) := by
    have hb' : Real.sqrt (1^2+‖y‖^2/16) ≤ 1+2*e := by linarith
    have he1 : 2*e ≤ 1 := by linarith
    nlinarith [Real.sqrt_nonneg (1^2+‖y‖^2/16),
      mul_nonneg (show 0 ≤ 2*e by positivity) (sub_nonneg.mpr he1)]
  exact (fractional_energy_bound (show 0 < 2*e by positivity) (by linarith)
    (norm_nonneg y) hsq).2

theorem quadratic_maximum_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ maximumModulus QuadraticOuter t :=
  (quadratic_averaged_modulus ht).trans (averagedModulus_le_maximum QuadraticOuter t)

theorem quadratic_maximum_modulus_positive {t : ℝ} (ht : 0 < t) :
    0 < maximumModulus QuadraticOuter t := by
  have hs : 1 < Real.sqrt (1+t^2/16) := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+t^2/16 by positivity)
    nlinarith [Real.sqrt_nonneg (1+t^2/16), sq_pos_of_pos ht]
  have hp : (0:EReal) < ((Real.sqrt (1+t^2/16)-1:ℝ):EReal) := by
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  exact hp.trans_le (quadratic_maximum_modulus ht)

end CostHeads
end BoundedTreePotentials

namespace BoundedTreePotentials.BlockCalculus
open TreeCalculus

theorem quadratic_component_estimate {n : ℕ} {D : Set Node} (hD : Initial D)
    (x y : TreeHilbert n) (hx : head D x=x) (hy : head D y=0)
    (hxn : quadraticBlockCost n x=1) {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1)
    (hp : quadraticBlockCost n (x+y) ≤ 1+e) (hm : quadraticBlockCost n (x-y) ≤ 1+e) :
    quadraticBlockCost n y ≤ (6+Real.sqrt 2)*Real.sqrt ((1+e)^2-1) ∧
      (6+Real.sqrt 2)*Real.sqrt ((1+e)^2-1) ≤ 13*Real.sqrt e := by
  have hh := quadratic_midpoint_tail hD x y hx
  rw [hy, sub_zero, hxn] at hh
  have hq := quadraticCost_nonneg (pathSynthesis n) y
  change 0 ≤ quadraticBlockCost n y at hq
  have hd : 0 ≤ (1+e)^2-1 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg ((1+e)^2-1)
  have heS := Real.sq_sqrt he
  have heS0 := Real.sqrt_nonneg e
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h20 := Real.sqrt_nonneg 2
  have hb : Real.sqrt 2 ≤ 3/2 := by nlinarith
  have hy2 := Real.sq_sqrt (show 0 ≤ (1:ℝ)^2+(quadraticBlockCost n y)^2/16 by positivity)
  have hyS0 := Real.sqrt_nonneg ((1:ℝ)^2+(quadraticBlockCost n y)^2/16)
  have hyS : Real.sqrt ((1:ℝ)^2+(quadraticBlockCost n y)^2/16) ≤ 1+e := by linarith
  have hy4 : quadraticBlockCost n y ≤ 4*Real.sqrt ((1+e)^2-1) := by nlinarith
  constructor
  · nlinarith
  · have hh0 : ((1+e)^2-1) ≤ 3*e := by nlinarith [mul_nonneg he (sub_nonneg.mpr he1)]
    have hh1 : (6+Real.sqrt 2)*Real.sqrt ((1+e)^2-1) ≤ (15/2)*Real.sqrt ((1+e)^2-1) := by nlinarith
    have hh2 : (15/2)*Real.sqrt ((1+e)^2-1) ≤ 13*Real.sqrt e := by nlinarith
    exact hh1.trans hh2

end BoundedTreePotentials.BlockCalculus

end

end OAI
