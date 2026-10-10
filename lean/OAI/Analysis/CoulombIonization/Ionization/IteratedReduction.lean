import Mathlib
import OAI.Analysis.CoulombIonization.Model

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

lemma uniform_tail_of_sequential_joint (f : ℕ → ℕ → ℝ) (a : ℝ)
    (h : ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
      Tendsto m atTop atTop →
      Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
      Tendsto (fun j => f (m j) (Z j)) atTop (𝓝 a)) :
    ∀ ε > 0, ∃ K : ℕ, ∀ m Z : ℕ, 1 ≤ m → m < Z → K ≤ m →
      (K : ℝ) ≤ (Z : ℝ) / (m : ℝ) → |f m Z - a| < ε := by
  intro ε hε
  by_contra hn
  push Not at hn
  choose m Z hm hZ hKm hKZ he using fun j : ℕ => hn (j + 1)
  have hmTop : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hKm j)) tendsto_id
  have hratio : Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    have hj : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ j
    exact hj.trans (hKZ j)
  have hc := h m Z (fun j => ⟨hm j, hZ j⟩) hmTop hratio
  have hev : ∀ᶠ j in atTop, |f (m j) (Z j) - a| < ε :=
    (Metric.tendsto_nhds.mp hc ε hε).mono fun j hj => by simpa [Real.dist_eq] using hj
  obtain ⟨j, hj⟩ := hev.exists
  exact (not_lt_of_ge (he j)) hj

lemma eventual_Z_band_of_joint (f : ℕ → ℕ → ℝ) (a : ℝ)
    (h : ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
      Tendsto m atTop atTop →
      Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
      Tendsto (fun j => f (m j) (Z j)) atTop (𝓝 a)) :
    ∀ ε > 0, ∀ᶠ m in (atTop : Filter ℕ), ∀ᶠ Z in (atTop : Filter ℕ),
      |f m Z - a| < ε := by
  intro ε hε
  obtain ⟨K, hK⟩ := uniform_tail_of_sequential_joint f a h ε hε
  filter_upwards [eventually_ge_atTop (max K 1)] with m hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmK : K ≤ m := (le_max_left _ _).trans hm
  filter_upwards [eventually_ge_atTop (max (m + 1) (K * m))] with Z hZ
  apply hK m Z hm1 (Nat.lt_of_succ_le ((le_max_left _ _).trans hZ)) hmK
  apply (le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm1 : (0 : ℝ) < m)).mpr
  exact_mod_cast (le_max_right (m + 1) (K * m)).trans hZ

lemma liminf_limsup_bounded_by_eventual {u : ℕ → ℝ} {l r : ℝ}
    (h : ∀ᶠ n in atTop, l ≤ u n ∧ u n ≤ r) :
    l ≤ liminf u atTop ∧ liminf u atTop ≤ limsup u atTop ∧ limsup u atTop ≤ r := by
  have hl : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u := ⟨l, h.mono fun _ hh => hh.1⟩
  have hr : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) u := ⟨r, h.mono fun _ hh => hh.2⟩
  exact ⟨le_liminf_of_le hr.isCoboundedUnder_ge (h.mono fun _ hh => hh.1),
    liminf_le_limsup hr hl, limsup_le_of_le hl.isCoboundedUnder_le (h.mono fun _ hh => hh.2)⟩

theorem iteratedLimits_of_jointLimit {a : ℝ} (h : JointLimit a) : IteratedLimits a := by
  have hband := eventual_Z_band_of_joint
    (fun m Z => ionization m Z / (m : ℝ) ^ (7 / 3 : ℝ)) a h
  have main : ∀ ε > 0, ∀ᶠ m in (atTop : Filter ℕ),
      |(limsup (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ) - a| < ε ∧
      |(liminf (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ) - a| < ε := by
    intro ε hε
    filter_upwards [hband (ε / 2) (by positivity), eventually_ge_atTop 1] with m hm hm1
    have hw : 0 < (m : ℝ) ^ (7 / 3 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm1) _
    have he : ∀ᶠ Z in (atTop : Filter ℕ),
        (a - ε / 2) * (m : ℝ) ^ (7 / 3 : ℝ) ≤ ionization m Z ∧
        ionization m Z ≤ (a + ε / 2) * (m : ℝ) ^ (7 / 3 : ℝ) := by
      filter_upwards [hm] with Z hZ
      obtain ⟨hl, hr⟩ := abs_lt.mp hZ
      constructor
      · apply (le_div_iff₀ hw).mp
        linarith
      · apply (div_le_iff₀ hw).mp
        linarith
    obtain ⟨hl, hm', hr⟩ := liminf_limsup_bounded_by_eventual he
    have hsL := (le_div_iff₀ hw).mpr (hl.trans hm')
    have hsR := (div_le_iff₀ hw).mpr hr
    have hiL := (le_div_iff₀ hw).mpr hl
    have hiR := (div_le_iff₀ hw).mpr (hm'.trans hr)
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (main ε hε).mono fun m hm => by simpa [Real.dist_eq] using hm.1
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact (main ε hε).mono fun m hm => by simpa [Real.dist_eq] using hm.2


open Filter
open scoped Topology InnerProductSpace

section

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace V] in

lemma positive_map_eq_zero_of_inner (B : V →L[ℂ] V) (hB : B.IsPositive)
    {F : V} (hF : (⟪F, B F⟫_ℂ).re = 0) : B F = 0 := by
  let f : ℝ → V := fun t => F + t • B F
  have hf : HasDerivAt f (B F) 0 := by
    simpa [f] using ((hasDerivAt_id (0 : ℝ)).smul_const (B F)).const_add F
  have hg : HasDerivAt (fun t => B (f t)) (B (B F)) 0 :=
    (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hf.inner ℂ hg)
  have hmin : IsLocalMin (fun t => (⟪f t, B (f t)⟫_ℂ).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (⟪f 0, B (f 0)⟫_ℂ).re ≤ (⟪f t, B (f t)⟫_ℂ).re
    have hf0 : f 0 = F := by simp [f]
    rw [hf0, hF]
    exact hB.re_inner_nonneg_right (f t)
  have he := hmin.hasDerivAt_eq_zero hd
  have hs := hB.isSymmetric F (B F)
  change ⟪B F, B F⟫_ℂ = ⟪F, B (B F)⟫_ℂ at hs
  simp only [f, zero_smul, add_zero, Complex.reCLM_apply, Complex.add_re] at he
  rw [← hs] at he
  have hzero : ‖B F‖ ^ 2 = 0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change (⟪B F, B F⟫_ℂ).re = 0
    linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)

theorem ground_form_equation (j : V →L[ℂ] H) (A : V →L[ℂ] V)
    (hs : IsSelfAdjoint A) {E : ℝ}
    (hlow : ∀ G : V, E * ‖j G‖ ^ 2 ≤ (⟪G, A G⟫_ℂ).re)
    {F : V} (hF : (⟪F, A F⟫_ℂ).re = E * ‖j F‖ ^ 2) :
    ∀ G : V, ⟪G, A F⟫_ℂ = (E : ℂ) * ⟪j G, j F⟫_ℂ := by
  let B : V →L[ℂ] V := A - (E : ℂ) • (j.adjoint.comp j)
  have hBs : IsSelfAdjoint B := by
    apply IsSelfAdjoint.sub (R := V →L[ℂ] V) hs
    exact IsSelfAdjoint.smul (R := ℂ) (A := V →L[ℂ] V)
      (Complex.conj_ofReal E) j.isPositive_adjoint_comp_self.isSelfAdjoint
  have hinner (G : V) : (⟪G, B G⟫_ℂ).re = (⟪G, A G⟫_ℂ).re - E * ‖j G‖ ^ 2 := by
    simp only [B, sub_apply, smul_apply,
      inner_sub_right, inner_smul_right, ContinuousLinearMap.comp_apply,
      j.adjoint_inner_right, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl
  have hBp : B.IsPositive := by
    refine ⟨hBs.isSymmetric, ?_⟩
    intro G
    change 0 ≤ (⟪B G, G⟫_ℂ).re
    rw [show (⟪B G, G⟫_ℂ).re = (⟪G, B G⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) _ _]
    rw [hinner]
    exact sub_nonneg.mpr (hlow G)
  have hzero : B F = 0 := positive_map_eq_zero_of_inner B hBp (by rw [hinner, hF, sub_self])
  intro G
  have he : A F = (E : ℂ) • (j.adjoint (j F)) := sub_eq_zero.mp hzero
  rw [he, inner_smul_right, j.adjoint_inner_right]

end

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace

lemma complex_ims_identity (p d : ℝ) (a b : ℂ) :
    ‖(p : ℂ) * a + (d : ℂ) * b‖ ^ 2 -
      (⟪(p : ℂ) * ((p : ℂ) * a + (d : ℂ) * b) +
        (d : ℂ) * ((p : ℂ) * b), a⟫_ℂ).re = d ^ 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

end CoulombAtom

end

end OAI
