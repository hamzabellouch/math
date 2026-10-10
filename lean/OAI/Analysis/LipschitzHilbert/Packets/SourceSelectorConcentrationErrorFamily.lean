import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorPhysical
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorBudget

namespace OAI

/-! One physical exceptional set controls the original selector error
and its first covariant jet for every top. Local multiplicity is charged
before convolution; there is no count of all available labels. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_selector_error_family_concentration
    (rate aWeight p M Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p)
    (hM : 0 ≤ M) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
      (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (T : τ → SlopeBox),
      (∀ top, SourceLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
      (∀ top j l k, Measurable (b top j l k)) →
      (∀ top j l k s, ‖b top j l k s‖ ≤ M) →
      (∀ top j l k s, b top j l k s ≠ 0 →
        |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b top j l k s-b top j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b top j l k s = 0) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
      ∀ top lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
        let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
          0 lower upper x y
        ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
          ‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
            (z.2-(T top).slope*z.1+shift)‖ ≤
              L^(2*p+7)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  obtain ⟨Lt,_hLt,hthreshold⟩ := exists_selector_error_top_threshold
    (rate+1) aWeight p D (by linarith) haWeight hp
  filter_upwards [LabeledAngularErrorFamily.eventually_sourceAmplitude_le K H M Lip p,
    LabeledAngularErrorFamily.eventually_source_error_budgets (p+1) J₀,
    eventually_ge_atTop (max 2 Lt)] with L hAmp hBudget hlarge
  have hL : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hLpos : 0 < L := by linarith
  have hKw : 0 < L^aWeight := Real.rpow_pos_of_pos hLpos _
  have hKw1 : 1 ≤ L^aWeight := Real.one_le_rpow (by linarith) haWeight
  intro τ κ _ _ N Label Item _ P hP horder alt hAlt T G angle small wide radius E J
    hangle hsmall hsmall1 hwide hwide1 hradius hlocal b hb hbM hsupport hnear hfar v hv
    g hg hg1 hJ hE
  classical
  let Err := fun top => (P top).angularErrorFamily (by have := horder top; omega)
    (T top).slope (angle top) small wide M Lip radius E J K H
    (hangle top) hsmall hsmall1 hwide hwide1 hM hLip hradius (hlocal top)
    (b top) (hb top) (hbM top) (hsupport top) (hnear top) (hfar top)
    (v top) (hv top) (g top) (hg top) (hg1 top)
  have hsource (top : τ) (y : ℝ) :
      ((Err top).sources y).sourceBound ≤ L^(p+4) ∧
      ((Err top).sources y).sumBound ≤ L^(p+4) := by
    have hA : (Err top).sourceAmplitude ≤ L^(p+1) :=
      hAmp (N top) (fun j => (P top).labels j) κ (fun j l => Item top j l) (Err top)
        le_rfl le_rfl le_rfl le_rfl (hP top)
    simpa only [show (p+1)+3 = p+4 by ring] using
      hBudget (N top) (fun j => (P top).labels j) κ (fun j l => Item top j l)
        (Err top) hA hJ hE y
  have hexists (top : τ) (i : Fin 2) : ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-(rate+1)*L)*(T top).area) ∧
      ∀ lower upper z shift, |shift| ≤ (T top).width → z ∉ bad →
        ‖((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalAngularErrorCoefficient (T top).slope (angle top) (b top) (v top) (g top))
          (i.castLE (by decide)) lower upper z.1 (z.2-(T top).slope*z.1+shift)‖ ≤
            L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
    obtain ⟨B,hB,harea,hpoint⟩ := (P top).selector_error_top_neighborhood
      (by have := horder top; omega) (T top).slope (angle top) small wide M Lip radius E J K H
      (hangle top) hsmall hsmall1 hwide hwide1 hM hLip hradius (hlocal top)
      (b top) (hb top) (hbM top) (hsupport top) (hnear top) (hfar top)
      (v top) (hv top) (g top) (hg top) (hg1 top) (alt top) (hAlt top)
      (T top) (L^aWeight) D hKw (G top) rfl (horder top) (L^(p+4))
      (Real.rpow_nonneg hLpos.le _) i (rate+1) L
      (fun y => (hsource top y).1) (fun y => (hsource top y).2)
    refine ⟨B,hB,harea,?_⟩
    intro lower upper z shift hs hz
    apply (hpoint lower upper z shift
      (hs.trans (le_mul_of_one_le_left (T top).width_pos.le hKw1)) hz).trans
    exact mul_le_mul_of_nonneg_right
      (hthreshold L ((le_max_right _ _).trans hlarge) (P top).absoluteConstant (L^(p+4))
        (P top).absoluteConstant_pos.le (Real.rpow_nonneg hLpos.le _) (hP top) le_rfl)
      (pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le _)
  choose bad hbad using hexists
  let exceptional := ⋃ top, ⋃ i, bad top i
  have hexceptional : MeasurableSet exceptional :=
    MeasurableSet.iUnion fun top => MeasurableSet.iUnion fun i => (hbad top i).1
  refine ⟨exceptional,hexceptional,?_,?_⟩
  · have hm := measure_iUnion_fintype_le (volume.prod volume) (fun top => ⋃ i, bad top i)
    apply hm.trans
    calc
      _ ≤ ∑ top, ∑ i : Fin 2, (volume.prod volume) (bad top i) :=
        Finset.sum_le_sum fun top _ => measure_iUnion_fintype_le (volume.prod volume) _
      _ ≤ ∑ top, ∑ _i : Fin 2,
          ENNReal.ofReal (Real.exp (-(rate+1)*L)*(T top).area) :=
        Finset.sum_le_sum fun top _ => Finset.sum_le_sum fun i _ => (hbad top i).2.1
      _ = ENNReal.ofReal (2*Real.exp (-(rate+1)*L)*(∑ top, (T top).area)) := by
        simp only [Fin.sum_univ_two]
        simp_rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (T _).area_pos.le)
          (mul_nonneg (Real.exp_pos _).le (T _).area_pos.le)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun top _ =>
          add_nonneg (mul_nonneg (Real.exp_pos _).le (T top).area_pos.le)
            (mul_nonneg (Real.exp_pos _).le (T top).area_pos.le))]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
        have hs : 0 ≤ ∑ top : τ, (T top).area :=
          Finset.sum_nonneg (fun top _ => (T top).area_pos.le)
        have hexp : 2*Real.exp (-(rate+1)*L) ≤ Real.exp (-rate*L) := by
          calc
            _ ≤ Real.exp L*Real.exp (-(rate+1)*L) :=
              mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
            _ = _ := by rw [← Real.exp_add]; congr 1; ring
        exact mul_le_mul_of_nonneg_right hexp hs
  · intro top lower upper z shift hs hout
    dsimp only
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := (P top).physicalAngularErrorCoefficient
      (T top).slope (angle top) (b top) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    have hjet (i : Fin 2) : ‖Q.rawInterval coeff (i.castLE (by decide)) lower upper z.1 y‖ ≤
        L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 :=
      (hbad top i).2.2 lower upper z shift hs (fun hi => hout
        (mem_iUnion.mpr ⟨top,mem_iUnion.mpr ⟨i,hi⟩⟩))
    have hscale : (T top).width ≤ |Q.scale| := by
      change (T top).width ≤ |(P top).scale|
      rw [(G top).scale_eq,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<4)
        (mul_pos hKw (T top).width_pos))]
      nlinarith [(T top).width_pos]
    have hc := congrArg norm (Q.rawInterval_scaled_covariant coeff lower upper z.1 y)
    rw [norm_smul,Real.norm_eq_abs] at hc
    have hd : (T top).width*‖covariantSignal (P top).frequency
        (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ ≤
          L^(2*p+6)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
      calc
        _ ≤ |Q.scale| * ‖covariantSignal Q.frequency
            (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ :=
          mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
        _ = _ := hc
        _ ≤ _ := hjet 1
    apply (add_le_add (hjet 0) hd).trans
    have hpow : 2*L^(2*p+6) ≤ L^(2*p+7) := by
      calc
        _ ≤ L*L^(2*p+6) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLpos.le _)
        _ = L^(1:ℝ)*L^(2*p+6) := by rw [Real.rpow_one]
        _ = L^(1+(2*p+6)) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring
    nlinarith [pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le 8,
      mul_le_mul_of_nonneg_right hpow (pow_nonneg ((T top).weight_pos hKw (D:ℝ) z).le 8)]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
