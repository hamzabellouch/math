import OAI.RepresentationTheory.KazhdanLusztig.SimultaneousInvariance

namespace OAI

/-!
Genuine KL invariance, finite-parabolic transport and unrestricted finite interval models; the main theorem for two arbitrary Coxeter systems in four independent universes.
-/

section

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a b : W} {a' b' : W'}
noncomputable section

 theorem rankDifference_subinterval_lt (x z : Interval cs a b) (hxz : x≤z)
    (hne : x.val≠a ∨ z.val≠b) :
    rankDifference cs x.val z.val<rankDifference cs a b := by
  have ha := length_le_of_bruhat cs x.property.1
  have hb := length_le_of_bruhat cs z.property.2
  have hm := length_le_of_bruhat cs hxz
  dsimp only [rankDifference]
  rcases hne with h|h
  · have := length_lt_of_bruhat_ne cs x.property.1 h.symm
    omega
  · have := length_lt_of_bruhat_ne cs z.property.2 h
    omega

 theorem rTilde_transport_all (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b')
    (hr : Hecke.rTilde cs a b=Hecke.rTilde cs' a' b')
    (hsmall : ∀ (x z : Interval cs a b), x≤z →
      rankDifference cs x.val z.val<rankDifference cs a b →
      Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val) :
    ∀ x z : Interval cs a b, Hecke.rTilde cs x.val z.val=
      Hecke.rTilde cs' (φ x).val (φ z).val := by
  intro x z
  by_cases hxz : x≤z
  · by_cases hxa : x.val=a
    · by_cases hzb : z.val=b
      · have hx : x=intervalBottom cs hab := Subtype.ext hxa
        have hz : z=intervalTop cs hab := Subtype.ext hzb
        rw [hx,hz,intervalIso_bottom cs cs' hab hab' φ,intervalIso_top cs cs' hab hab' φ]
        exact hr
      · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inr hzb))
    · exact hsmall x z hxz (rankDifference_subinterval_lt x z hxz (Or.inl hxa))
  · have hnot : ¬BruhatLE cs' (φ x).val (φ z).val := fun h => hxz (φ.le_iff_le.mp h)
    rw [Hecke.rTilde_zero cs x.val z.val hxz,Hecke.rTilde_zero cs' _ _ hnot]

end
end KLInvariance

end


section

/-! One rank-induction step for genuine R invariance. All inputs concern strictly
smaller intervals in the eventual induction; no KL character theorem is assumed. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
  {a b : W} {a' b' : W'} (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
  (φ : Interval cs a b ≃o Interval cs' a' b')
noncomputable section

 theorem actual_target_freeness
    (hupper : ∀ y : Interval cs a b, y.val≠a →
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y)) :
    ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hab).sheaf.upwardSubmodule (target cs a b e)
          (remainingConditions cs a b q (target cs a b e))) := by
  intro e q hq
  apply target_free_of_upper_suffixes basis hab φ hq
  apply hupper
  have hle := length_le_of_bruhat cs (source cs a b e).property.1
  have hlt := e.property.1
  change cs.length (source cs a b e).val<cs.length (target cs a b e).val at hlt
  intro heq
  rw [heq] at hlt
  omega

include hab hab' in
 theorem rTilde_eq_of_smaller_data
    (hrow : ∀ z : Interval cs a b, z.val≠b →
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val)
    (hrow' : ∀ z : Interval cs' a' b', z.val≠b' →
      Hecke.rTilde cs' a' z.val=Hecke.rTilde cs a (φ.symm z).val)
    (hupper : ∀ y : Interval cs a b, y.val≠a →
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y))
    (hupper' : ∀ y : Interval cs' a' b', y.val≠a' →
      FreeSuffixes basis' y.property.2 (upperIntervalIso φ.symm y)) :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' := by
  apply Comparison.polynomial_eq_of_transfer_eval_eq
  intro t ht ht1
  apply le_antisymm
  · exact rTilde_eval_le_of_upper_freeness basis hab hab' φ hrow
      (actual_target_freeness basis hab φ hupper) ht ht1
  · exact rTilde_eval_le_of_upper_freeness basis' hab' hab φ.symm hrow'
      (actual_target_freeness basis' hab' φ.symm hupper') ht ht1

end
end KLInvariance.BruhatGraph

end


section

/-! Unconditional genuine R-tilde invariance and transported terminal freeness.
Induction is over arbitrary interval rank, with both endpoints varying. Actual
BMP characters are only test vectors for the edge inequalities. Their genuine
R-reciprocity and top1 are enough; strict halfdegree is NOT assumed. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
noncomputable section

 theorem rTilde_freeness_of_below
    (a b : W) (a' b' : W') (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') (n : ℕ) (hn : rankDifference cs a b=n)
    (hbelow : ∀ (c d : W) (c' d' : W') (hcd : BruhatLE cs c d) (hcd' : BruhatLE cs' c' d')
      (ψ : Interval cs c d ≃o Interval cs' c' d'), rankDifference cs c d<n →
      Hecke.rTilde cs c d=Hecke.rTilde cs' c' d' ∧
        FreeSuffixes basis hcd ψ ∧ FreeSuffixes basis' hcd' ψ.symm) :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' ∧
      FreeSuffixes basis hab φ ∧ FreeSuffixes basis' hab' φ.symm := by
  have hn' : rankDifference cs' a' b'=n :=
    (intervalIso_full_rankDifference cs cs' hab hab' φ).symm.trans hn
  have hsmall (x z : Interval cs a b) (hxz : x≤z)
      (hlt : rankDifference cs x.val z.val<rankDifference cs a b) :
      Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val :=
    (hbelow x.val z.val (φ x).val (φ z).val hxz (φ.monotone hxz)
      (intervalIso_restrict cs cs' φ x z) (hn ▸ hlt)).1
  have hrow (z : Interval cs a b) (hz : z.val≠b) :
      Hecke.rTilde cs a z.val=Hecke.rTilde cs' a' (φ z).val := by
    have h := hsmall (intervalBottom cs hab) z z.property.1
      (rankDifference_subinterval_lt (intervalBottom cs hab) z z.property.1 (Or.inr hz))
    rw [intervalIso_bottom cs cs' hab hab' φ] at h
    exact h
  have hrow' (z : Interval cs' a' b') (hz : z.val≠b') :
      Hecke.rTilde cs' a' z.val=Hecke.rTilde cs a (φ.symm z).val := by
    let x := intervalBottom cs' hab'
    have hxz : x≤z := z.property.1
    have hlt : rankDifference cs (φ.symm x).val (φ.symm z).val<n := by
      rw [←intervalIso_rankDifference cs' cs φ.symm hxz]
      exact hn' ▸ rankDifference_subinterval_lt x z hxz (Or.inr hz)
    have h := (hbelow (φ.symm x).val (φ.symm z).val x.val z.val
      (φ.symm.monotone hxz) hxz (intervalIso_restrict cs' cs φ.symm x z).symm hlt).1.symm
    dsimp only [x] at h
    rw [intervalIso_bottom cs' cs hab' hab φ.symm] at h
    exact h
  have hupper (y : Interval cs a b) (hy : y.val≠a) :
      FreeSuffixes basis y.property.2 (upperIntervalIso φ y) := by
    exact (hbelow y.val b (φ y).val b' y.property.2 (φ y).property.2
      (upperIntervalIso φ y)
      (hn ▸ rankDifference_subinterval_lt y (intervalTop cs hab) y.property.2 (Or.inl hy))).2.1
  have hupper' (y : Interval cs' a' b') (hy : y.val≠a') :
      FreeSuffixes basis' y.property.2 (upperIntervalIso φ.symm y) := by
    let ψ := (upperIntervalIso φ.symm y).symm
    have hlt : rankDifference cs (φ.symm y).val b<n := by
      rw [intervalIso_full_rankDifference cs cs' (φ.symm y).property.2 y.property.2 ψ]
      exact hn' ▸ rankDifference_subinterval_lt y (intervalTop cs' hab') y.property.2 (Or.inl hy)
    exact (hbelow (φ.symm y).val b y.val b' (φ.symm y).property.2 y.property.2 ψ hlt).2.2
  have hr := rTilde_eq_of_smaller_data basis basis' hab hab' φ hrow hrow' hupper hupper'
  have hrall := rTilde_transport_all hab hab' φ hr hsmall
  refine ⟨hr,actual_freeSuffixes_of_rTilde_eq basis hab φ hrall
    (actual_target_freeness basis hab φ hupper),?_⟩
  apply actual_freeSuffixes_of_rTilde_eq basis' hab' φ.symm
    (fun x z => by simpa only [φ.apply_symm_apply] using (hrall (φ.symm x) (φ.symm z)).symm)
    (actual_target_freeness basis' hab' φ.symm hupper')

 theorem rTilde_invariance_and_freeness
    (a b : W) (a' b' : W') (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') :
    Hecke.rTilde cs a b=Hecke.rTilde cs' a' b' ∧
      FreeSuffixes basis hab φ ∧ FreeSuffixes basis' hab' φ.symm := by
  have hp : ∀ n, ∀ (c d : W) (c' d' : W') (hcd : BruhatLE cs c d) (hcd' : BruhatLE cs' c' d')
      (ψ : Interval cs c d ≃o Interval cs' c' d'), rankDifference cs c d=n →
      Hecke.rTilde cs c d=Hecke.rTilde cs' c' d' ∧
        FreeSuffixes basis hcd ψ ∧ FreeSuffixes basis' hcd' ψ.symm := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c d c' d' hcd hcd' ψ hn
      apply rTilde_freeness_of_below basis basis' c d c' d' hcd hcd' ψ n hn
      intro e f e' f' hef hef' θ hlt
      exact ih _ hlt e f e' f' hef hef' θ rfl
  exact hp _ a b a' b' hab hab' φ rfl

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance
open Polynomial
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem scaledKL_eq_scaledPolynomial (t : ℝ) {x b : W} (hxb : BruhatLE cs x b) :
    scaledKL cs t x b = Comparison.scaledPolynomial t (rankDifference cs x b)
      (klPolynomial cs x b) := by
  have hh := length_le_of_bruhat cs hxb
  have he : (cs.length x : ℤ)-cs.length b = -(rankDifference cs x b : ℤ) := by
    unfold rankDifference
    omega
  simp only [scaledKL,Comparison.scaledPolynomial,he]

variable {I' : Type u'} {M' : CoxeterMatrix I'} {W' : Type v'} [Group W']
  (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
  (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
  (φ : Interval cs u b ≃o Interval cs' u' b')

include hub hub'

 theorem intervalIso_upper_rankDifference (x : Interval cs u b) :
    rankDifference cs x.val b = rankDifference cs' (φ x).val b' := by
  have h := intervalIso_rankDifference cs cs' φ
    (show x ≤ intervalTop cs hub from x.property.2)
  rw [intervalIso_top cs cs' hub hub' φ] at h
  exact h

 theorem scaledKL_transport (t : ℝ) (x : Interval cs u b)
    (hx : klPolynomial cs x.val b=klPolynomial cs' (φ x).val b') :
    scaledKL cs t x.val b=scaledKL cs' t (φ x).val b' := by
  rw [scaledKL_eq_scaledPolynomial cs t x.property.2,
    scaledKL_eq_scaledPolynomial cs' t (φ x).property.2,
    intervalIso_upper_rankDifference cs cs' hub hub' φ x,hx]

end
end KLInvariance

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem comparison_of_source02
    [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
    (d : SectionDuality cs 1 b basis (one_bruhat cs b)
      (boundarySheaf cs 1 b basis (one_bruhat cs b)))
    (hd : ∀ i j (m n : (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ),
      m ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece i →
      n ∈ ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.sections Set.univ).piece j →
      d.pairing m n ∈ polynomialGrading ℝ σ (i+j-(cs.length b : ℤ)))
    (hc : StalkCharacterObligation cs 1 b basis (one_bruhat cs b))
    (hfree : ∀ e q, e::q <:+ chronologicalSchedule φ →
      Module.Free (Coefficient (σ := σ))
        ((intervalBoundary basis hub).sheaf.upwardSubmodule (target cs u b e)
          (remainingConditions cs u b q (target cs u b e))))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (fun x : Interval cs u b => scaledKL cs t x.val b) ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun x => scaledKL cs t⁻¹ x.val b) (transportedSchedule φ) := by
  classical
  have h := schedule_comparison_of_upper_freeness basis hub φ hfree ht ht1
  have hf : scheduleState cs u b basis hub (intervalBoundary basis hub) t [] =
      fun x => scaledKL cs t x.val b :=
    funext (schedule_final_of_character basis hub hc ht ht1)
  have hi : scheduleState cs u b basis hub (intervalBoundary basis hub) t (chronologicalSchedule φ) =
      fun x => scaledKL cs t⁻¹ x.val b :=
    funext (schedule_initial_of_duality_character basis hub φ d hd hc ht ht1)
  rwa [hf,hi] at h

omit [Fintype I] in
include hub in
 theorem comparison_difference_le (hub' : BruhatLE cs' u' b')
    (x : Interval cs u b)
    (hother : ∀ y : Interval cs u b, y ≠ x →
      klPolynomial cs y.val b=klPolynomial cs' (φ y).val b')
    {t : ℝ} (ht : t ≠ 0)
    (hcomp : scaledKL cs t x.val b ≤
      dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) x) :
    scaledKL cs t x.val b-scaledKL cs' t (φ x).val b' ≤
      scaledKL cs t⁻¹ x.val b-scaledKL cs' t⁻¹ (φ x).val b' := by
  classical
  let := interval_finite cs u b
  let := Fintype.ofFinite (Interval cs u b)
  have hp' := transported_reciprocal_vector φ t ht x
  rw [transported_dispatch_matrix φ _ (Int.castRingHom ℝ),finsum_eq_sum_of_fintype] at hcomp hp'
  exact Comparison.matrix_difference_le _ _ _ x _ _ (by simp)
    (fun y hy => scaledKL_transport cs cs' hub hub' φ t⁻¹ y (hother y hy)) hcomp hp'

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem bottom_eq_of_comparisons (hne : u ≠ b)
    (hupper : ∀ y : Interval cs u b, y.val ≠ u →
      klPolynomial cs y.val b=klPolynomial cs' (φ y).val b')
    (hforward : ∀ t : ℝ, 0<t → t<1 →
      scaledKL cs t u b ≤ dispatch (source cs u b) (target cs u b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) (intervalBottom cs hub))
    (hbackward : ∀ t : ℝ, 0<t → t<1 →
      scaledKL cs' t u' b' ≤ dispatch (source cs' u' b') (target cs' u' b') (t⁻¹-t)
        (fun y => scaledKL cs' t⁻¹ y.val b') (transportedSchedule φ.symm)
          (intervalBottom cs' hub')) : klPolynomial cs u b=klPolynomial cs' u' b' := by
  have hr := intervalIso_full_rankDifference cs cs' hub hub' φ
  have hne' : u' ≠ b' := by
    intro h
    have hp := length_lt_of_bruhat_ne cs hub hne
    unfold rankDifference at hr
    simp only [h,Nat.sub_self] at hr
    omega
  apply Comparison.eq_of_scaled_difference_reciprocal
    (klPolynomial cs u b) (klPolynomial cs' u' b') (rankDifference cs u b)
    ((klFamilies_spec cs).P_degree u b hub hne)
  · rw [hr]
    exact (klFamilies_spec cs').P_degree u' b' hub' hne'
  intro t ht ht1
  have hf := comparison_difference_le hub φ hub' (intervalBottom cs hub)
    (fun y hy => hupper y (fun he => hy (Subtype.ext he))) ht.ne' (hforward t ht ht1)
  have hb := comparison_difference_le hub' φ.symm hub (intervalBottom cs' hub')
    (fun y hy => by
      have hyy : (φ.symm y).val ≠ u := by
        intro he
        have he' : φ.symm y=intervalBottom cs hub := Subtype.ext he
        apply hy
        have hh := congrArg φ he'
        rw [φ.apply_symm_apply,intervalIso_bottom cs cs' hub hub' φ] at hh
        exact hh
      simpa only [φ.apply_symm_apply] using (hupper (φ.symm y) hyy).symm)
    ht.ne' (hbackward t ht ht1)
  rw [intervalIso_bottom cs cs' hub hub' φ] at hf
  rw [intervalIso_bottom cs' cs hub' hub φ.symm] at hb
  change scaledKL cs t u b-scaledKL cs' t u' b' ≤
    scaledKL cs t⁻¹ u b-scaledKL cs' t⁻¹ u' b' at hf
  change scaledKL cs' t u' b'-scaledKL cs t u b ≤
    scaledKL cs' t⁻¹ u' b'-scaledKL cs t⁻¹ u b at hb
  have he : scaledKL cs t u b-scaledKL cs' t u' b' =
      scaledKL cs t⁻¹ u b-scaledKL cs' t⁻¹ u' b' := by linarith
  simpa only [scaledKL_eq_scaledPolynomial cs _ hub,
    scaledKL_eq_scaledPolynomial cs' _ hub',hr] using he

end
end KLInvariance.BruhatGraph

end


section

/-! Closing the main theorem in finite generator rank. The actual BMP sheaves
are used only to prove the genuine R-kernel invariance. Canonical KL degree
bounds and reciprocity now identify the genuine KL polynomials; no BMP stalk
character identification or strict halfdegree assumption is used. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace SchedulePaths
universe u u'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] {cs : CoxeterSystem M W}
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type u'} [Group W'] {cs' : CoxeterSystem M' W'}
  {σ' : Type u'} [Fintype σ'] (basis' : Basis σ' ℝ (Extended M'))
noncomputable section
include basis basis'

 theorem rTilde_invariance_all_entries {a b : W} {a' b' : W'}
    (φ : Interval cs a b ≃o Interval cs' a' b') (x z : Interval cs a b) :
    Hecke.rTilde cs x.val z.val=Hecke.rTilde cs' (φ x).val (φ z).val := by
  by_cases h : x≤z
  · exact (rTilde_invariance_and_freeness basis basis' x.val z.val (φ x).val (φ z).val
      h (φ.monotone h) (intervalIso_restrict cs cs' φ x z)).1
  · rw [Hecke.rTilde_zero cs _ _ h, Hecke.rTilde_zero cs' _ _ (fun h' => h (φ.le_iff_le.mp h'))]

 theorem scaledKL_eq_transported {a b : W} {a' b' : W'}
    (φ : Interval cs a b ≃o Interval cs' a' b')
    {C : Type*} [Field C] (t : C) (ht : t≠0) (x : Interval cs a b) :
    scaledKL cs t x.val b =
      dispatch (source cs a b) (target cs a b) (t⁻¹-t)
        (fun y => scaledKL cs t⁻¹ y.val b) (transportedSchedule φ) x := by
  rw [transported_dispatch_matrix φ _ (Int.castRingHom C),
    scaledKL_reciprocity_upper cs t ht a b x]
  apply finsum_congr
  intro z
  rw [rTilde_invariance_all_entries basis basis' φ x z]

 theorem klPolynomial_invariance_finite (a b : W) (a' b' : W')
    (hab : BruhatLE cs a b) (hab' : BruhatLE cs' a' b')
    (φ : Interval cs a b ≃o Interval cs' a' b') :
    klPolynomial cs a b=klPolynomial cs' a' b' := by
  have hp : ∀ n, ∀ (c : W) (c' : W')
      (hcb : BruhatLE cs c b) (hcb' : BruhatLE cs' c' b')
      (ψ : Interval cs c b ≃o Interval cs' c' b'), rankDifference cs c b=n →
      klPolynomial cs c b=klPolynomial cs' c' b' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c c' hcb hcb' ψ hn
      by_cases hne : c=b
      · have hne' : c'=b' := by
          by_contra h
          have hp := length_lt_of_bruhat_ne cs' hcb' h
          have hr := intervalIso_full_rankDifference cs cs' hcb hcb' ψ
          unfold rankDifference at hr
          rw [hne,Nat.sub_self] at hr
          omega
        simp only [hne,hne',klPolynomial,(klFamilies_spec cs).P_diagonal,(klFamilies_spec cs').P_diagonal]
      · apply bottom_eq_of_comparisons hcb hcb' ψ hne
        · intro y hy
          apply ih (rankDifference cs y.val b)
            (hn ▸ rankDifference_subinterval_lt y (intervalTop cs hcb) y.property.2 (Or.inl hy))
            y.val (ψ y).val y.property.2 (ψ y).property.2 (upperIntervalIso ψ y) rfl
        · intro t ht _ht1
          exact (scaledKL_eq_transported basis basis' ψ t ht.ne' (intervalBottom cs hcb)).le
        · intro t ht _ht1
          exact (scaledKL_eq_transported basis' basis ψ.symm t ht.ne' (intervalBottom cs' hcb')).le
  exact hp _ a a' hab hab' φ rfl

end
end KLInvariance.BruhatGraph

end


section

/-! The finite-rank reduction of the exact main target.  The model's interval
and genuine KL polynomial are identified with those of the unrestricted
ambient Coxeter system, not with an order-theoretically defined invariant. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)
noncomputable section

structure FiniteIntervalModel where
  indices : Set I
  finite : indices.Finite
  lower : (StandardParabolic.matrix (M := M) indices).Group
  upper : (StandardParabolic.matrix (M := M) indices).Group
  lower_eq : StandardParabolic.inclusion cs indices lower = u
  upper_eq : StandardParabolic.inclusion cs indices upper = b

 theorem exists_finiteIntervalModel (hub : BruhatLE cs u b) :
    Nonempty (FiniteIntervalModel cs u b) := by
  obtain ⟨J,hJ,hJgen⟩ := lower_ideal_finite_generator_support cs b
  obtain ⟨v,hv,hvu⟩ := hJgen u hub
  obtain ⟨w,hw,hwb⟩ := hJgen b (bruhat_refl cs b)
  obtain ⟨v',hv'⟩ := StandardParabolic.lift_word J hv
  obtain ⟨w',hw'⟩ := StandardParabolic.lift_word J hw
  refine ⟨⟨J,hJ,(StandardParabolic.system (M := M) J).wordProd v',
    (StandardParabolic.system (M := M) J).wordProd w',?_,?_⟩⟩
  · rw [StandardParabolic.inclusion_word,hv',hvu]
  · rw [StandardParabolic.inclusion_word,hw',hwb]

def intervalEndpointCongr {a b a' b' : W} (ha : a = a') (hb : b = b') :
    Interval cs a b ≃o Interval cs a' b' := by
  subst a'
  subst b'
  exact OrderIso.refl _

namespace FiniteIntervalModel
variable {cs u b} (F : FiniteIntervalModel cs u b)

 def orderIso : Interval (StandardParabolic.system (M := M) F.indices) F.lower F.upper ≃o
    Interval cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  have h := StandardParabolic.intervalIso cs F.indices F.lower F.upper
  exact h.trans (intervalEndpointCongr cs F.lower_eq F.upper_eq)

 theorem bruhat (hub : BruhatLE cs u b) :
    BruhatLE (StandardParabolic.system (M := M) F.indices) F.lower F.upper := by
  let _ : Fintype F.indices := F.finite.fintype
  apply (StandardParabolic.bruhat_inclusion_iff cs F.indices F.lower F.upper).mp
  simpa only [F.lower_eq,F.upper_eq] using hub

 theorem kl_eq : klPolynomial (StandardParabolic.system (M := M) F.indices) F.lower F.upper =
    klPolynomial cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  simpa only [F.lower_eq,F.upper_eq] using
    (StandardParabolic.klPolynomial_inclusion cs F.indices F.lower F.upper).symm

 theorem rank_eq : rankDifference (StandardParabolic.system (M := M) F.indices) F.lower F.upper =
    rankDifference cs u b := by
  let _ : Fintype F.indices := F.finite.fintype
  simpa only [F.lower_eq,F.upper_eq] using
    (StandardParabolic.rankDifference_inclusion cs F.indices F.lower F.upper).symm

end FiniteIntervalModel
end
end KLInvariance

end


section

/-! Exact unrestricted main theorem. Finite parabolic restriction preserves
actual intervals and genuine equal-parameter KL polynomials. Bases used in
the temporary finite realization are selected here, not added as hypotheses. -/
namespace KLInvariance
open Module TitsSpace BruhatGraph
universe u v u' v'
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
noncomputable section

 theorem combinatorial_invariance
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    klPolynomial cs u b = klPolynomial cs' u' b' := by
  obtain ⟨F⟩ := exists_finiteIntervalModel cs u b hub
  obtain ⟨F'⟩ := exists_finiteIntervalModel cs' u' b' hub'
  let : Fintype F.indices := F.finite.fintype
  let : Fintype F'.indices := F'.finite.fintype
  let basis := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M) F.indices))
  let basis' := Module.Free.chooseBasis ℝ (Extended (StandardParabolic.matrix (M := M') F'.indices))
  rw [←F.kl_eq,←F'.kl_eq]
  exact klPolynomial_invariance_finite basis basis' F.lower F.upper F'.lower F'.upper
    (F.bruhat hub) (F'.bruhat hub') ((F.orderIso.trans ι).trans F'.orderIso.symm)

end
end KLInvariance

end


-- Recursive standard-axiom closure of the exact unrestricted exported main.

end OAI
