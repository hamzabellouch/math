import OAI.Dynamics.ThreeTorus.CyclicPrediction

namespace OAI

/-! Physical signal and derivative control through actual repeated blocks, cyclic prediction, and tag selection. -/

section

/-! The concrete signal producer with physical smooth restrictions. The first
passage integer is chosen only after the refresh family and all earlier
coordinates are fixed; the second is selected after the first output. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Symmetric actual refresh--signal pairs, retaining the complete good arc
with arbitrarily small excluded measure. -/
theorem exists_colored_controlled_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
      ∀ τR : R → R, C.Reflection τR →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
      ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
      ∀ (Q : PhysicalJetData) (F : PhysicalFrame) (ζ : ℝ), 0 < ζ →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧
        s.output.Reflection τR ∧
        (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ s.final.GoodArc δ) ∧
        Q.Close ζ F C.packets.V (s.nextFrame F) s.final.V ∧
        ∀ r,
        physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
        (∫ z, |s.output.density r z-C.density r z*
          colorFactor a (refreshedStrength (signalPrimeProduct L) γ) (N:ℤ) r z| ∂phaseHaar) <
            2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε := by
  classical
  obtain ⟨L,γ₀,hL,hLD,hγ₀,hfamily⟩ := exists_refresh_transmit_reflected_state hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγ hγs
  obtain ⟨hsmall,hpair⟩ := hfamily γ hγ hγs
  refine ⟨hsmall,?_⟩
  intro R inst C τR hrC margin hmargin hband a ha ω hω hmatch Q F ζ hζ ε η κ hε hη hκ
  obtain ⟨τ,hr,hτ⟩ := hrC
  obtain ⟨e,he,hecard,hecard2⟩ := finite_card_error_budget C.Index hε
  obtain ⟨g,S,hG⟩ := hpair C.Index C.packets C.injective C.spare τ hr C.scale C.scale_pos
    margin hmargin hband (fun i => a (C.color i)) (fun i => ha (C.color i))
    ω hω hmatch e η κ he hη hκ
  obtain ⟨n₀,hn₀⟩ := hG.exists
  obtain ⟨hn₀p,G₀,_hG₀i,_hG₀mod,hG₀V,_hG₀m,_tail⟩ := hn₀
  have hgJ := g.smooth_jitter_of_output G₀ hn₀p hG₀V
  obtain ⟨n,hn,hjetn⟩ := (hG.and (Q.eventually_next F g C.packets.smooth_speed hgJ (half_pos hζ))).exists
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,g',T,hK⟩ := hn
  let F₁ := F.next g C.packets.smooth_speed n
  have hjetG : Q.Close (ζ/2) F C.packets.V F₁ G.V := by
    rw [hGV]
    exact hjetn
  obtain ⟨N₀,hN₀⟩ := hK.exists
  obtain ⟨hN₀p,K₀,_hK₀i,_hK₀mod,hK₀V,_hK₀m,_tail₀⟩ := hN₀
  have hg'J := g'.smooth_jitter_of_output K₀ hN₀p hK₀V
  filter_upwards [hK,Q.eventually_next F₁ g' G.smooth_speed hg'J (half_pos hζ)] with N hN hjetN
  obtain ⟨hNp,K,hKi,hKmod,hKV,hKm,herror,htrack,τK,hτK,hrK,hgoodK⟩ := hN
  let s : ColoredPair C N :=
    ⟨g,S n,n,hnp,G,hGi,hGmod,hGV,hGm,g',T N,hNp,K,hKi,hKmod,hKV,hKm⟩
  refine ⟨s,htrack,⟨τK,hrK,?_⟩,hgoodK,?_,?_⟩
  · intro i
    change C.color ((τK i).1.1) = τR (C.color i.1.1)
    exact (congrArg C.color (hτK i)).trans (hτ i.1.1)
  · have hh : Q.Close (ζ/2) F₁ G.V (F₁.next g' G.smooth_speed N) K.V := by
      rw [hKV]
      exact hjetN
    have ht := hjetG.trans hh
    rw [add_halves] at ht
    exact ht
  · exact color_pair_errors C.packets K C.color a ha (g.Hcontinuous n) (g'.Hcontinuous N)
      N (refreshedStrength (signalPrimeProduct L) γ) he hecard hecard2 herror

end ThreeTorus
end
end

section

/-! Concrete finite colored iteration. The cofinal-frequency tree is built
from actual neutral--signal pairs. The error budget is fixed before the
initial anchor state and before any future packet index type is known. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def ColoredSignalControlledRealizes (b D : ℝ) (d : ℝ → ℂ) (γ ell : ℝ) : Prop :=
  ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
    ∀ τR : R → R, C.Reflection τR →
    ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
    ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
    ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
    ∀ (Q : PhysicalJetData) (F : PhysicalFrame) (ζ : ℝ), 0 < ζ →
    ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
    ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧
      s.output.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ s.final.GoodArc δ) ∧ Q.Close ζ F C.packets.V (s.nextFrame F) s.final.V ∧ ∀ r,
      physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
      (∫ z, |s.output.density r z-C.density r z*colorFactor a ell (N:ℤ) r z| ∂phaseHaar) <
        2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε

/-- The interface is discharged by the actual geometric construction. -/
theorem exists_concrete_colored_controlled_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ColoredSignalControlledRealizes b D d γ (refreshedStrength (signalPrimeProduct L) γ) :=
  exists_colored_controlled_signal hb hbD hd hdc hdr hd0 hds

/-- Fixed data and a small coefficient tolerance first; the threshold tree is
chosen on the actual initial state; ALL diagonals above that tree are realized
with small product-model and physical errors. No independence of the diagonal,
modeled next state, or unproved packet producer is used. -/
theorem ColoredSignalControlledRealizes.iterate {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalControlledRealizes b D d γ ell)
    (hd : Continuous d) (hdc : HasCompactSupport d) (hγ : 0 < γ)
    (hell : 0 ≤ ell) (hells : 6*ell ≤ 1)
    (m n : ℕ) (τR : Fin m → Fin m) (a : Fin m → UnitAddCircle → ℂ)
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    (Q : PhysicalJetData) {M ε κ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ C : ColoredState (Fin m), C.Reflection τR →
      colorMass C.density ≤ M → ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d a ω → ∀ F : PhysicalFrame,
      ∃ B : (j : ℕ) → (Fin j → ℤ) → ℤ, ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) →
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          colorL1Distance (colorModel C.density a ell L) E.density < ε ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ∃ μ : ℝ, 0 < μ ∧ E.InBand b D μ ∧ E.Matches d a (((n:ℝ)+1)*ω) ∧ E.Reflection τR ∧
            (0 < n → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
            ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close ε F C.packets.V F' E.packets.V := by
  classical
  obtain ⟨t,ω,U,ht,hω,hU,hfinal,hmassBound,hsubstitution⟩ := finite_iteration_budget n hM hγ hε
  obtain ⟨e,he,het,hem⟩ := finite_color_tolerance m ht
  refine ⟨ω,hω,?_⟩
  intro C hrC hmass margin hmargin hband hmatch F
  let Reach (k : ℕ) (L : Fin k → ℤ) : Prop :=
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ μ : ℝ,
      0 < μ ∧ ColoredPath C L E α ∧ E.InBand b D μ ∧
      E.Matches d a (((k:ℝ)+1)*ω) ∧
      colorL1Distance (colorModel C.density a ell L) E.density ≤ iterationError t k ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) ≤ iterationError t k) ∧
      E.Reflection τR ∧
      (0 < k → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close (iterationError t k) F C.packets.V F' E.packets.V
  have hzero : Reach 0 (fun i => Fin.elim0 i) := by
    refine ⟨C,Equiv.refl _,margin,hmargin,ColoredPath.nil,hband,?_,?_,?_,hrC,(by intro h; omega),F,rfl,?_⟩
    · simpa using hmatch
    · rw [colorModel_zero]
      simpa [colorL1Distance,iterationError] using ht.le
    · intro r
      simpa [physicalError,iterationError] using ht.le
    · exact (Q.close_refl F C.packets.V).mono (by simp [iterationError]; exact ht.le)
  have hstep : ∀ k (L : Fin k → ℤ), k < n → Reach k L →
      ∀ᶠ N : ℤ in atTop, Reach (k+1) (Fin.snoc L N) := by
    intro k L hk hreach
    obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herror,hphysical,hrE,_hgoodE,F',hF',hjets⟩ := hreach
    have hmassE : colorMass E.density ≤ U := by
      have hmodel := colorModel_mass_bound C.density_continuous C.density_nonneg ha ha3 hell hells L
      have hbase := mul_le_mul_of_nonneg_right hmass (show (0:ℝ) ≤ 2^k by positivity)
      exact (colorMass_le_add_distance
        (continuous_colorModel C.density_continuous ha ell L) E.density_continuous).trans
        ((add_le_add (hmodel.trans hbase) herror).trans (hmassBound k hk.le))
    obtain ⟨η₀,hη₀,hcoeff⟩ := core_coefficient_drift_budget E.packets hd hdc
      (fun i => a (E.color i)) (fun i => ha (E.color i)) hω hmatchE
    let η := min η₀ (μ/2)
    have hη : 0 < η := lt_min hη₀ (half_pos hμ)
    have hωk : 0 ≤ ((k:ℝ)+1)*ω := by positivity
    have hready := hsignal (Fin m) E τR hrE μ hμ hbandE a ha (((k:ℝ)+1)*ω) hωk hmatchE Q F' t ht e η κ he hη hκ
    apply eventually_int_of_eventually_nat
    filter_upwards [hready] with N hN
    obtain ⟨s,htrack,hrNext,hgoodNext,hjetStep,hcolor⟩ := hN
    have hbandNext : s.output.InBand b D (μ/2) :=
      htrack.band_margin hbandE (min_le_right _ _)
    have hcoeffNext : s.output.Matches d a ((((k+1:ℕ):ℝ)+1)*ω) := by
      intro i y _hy
      have hh := hcoeff _ s.final (Sigma.fst ∘ Sigma.fst) s.output.scale
        (htrack.mono (min_le_left _ _)) i y
      change ‖d ((s.final.m i:ℝ)/s.output.scale)-
        a (E.color ((Sigma.fst ∘ Sigma.fst) i))
          ((s.final.m i:ℝ)*s.final.V y:UnitAddCircle)‖ ≤ _
      have heq : ((((k+1:ℕ):ℝ)+1)*ω) = ((k:ℝ)+1)*ω+ω := by push_cast; ring
      rw [heq]
      exact hh
    have hdensityStep : colorL1Distance
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) s.output.density ≤ t := by
      rw [colorL1Distance_symm]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hcolor r).2.le)
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
      change colorL1Distance s.output.density
        (fun r z => E.density r z*colorFactor a ell (N:ℤ) r z) ≤
          2*γ*(((k:ℝ)+1)*ω)*colorMass E.density+(m:ℝ)*e at hh
      have hb := mul_le_mul_of_nonneg_left hmassE (show 0 ≤ 2*γ*(((k:ℝ)+1)*ω) by positivity)
      have hs := hsubstitution k hk.le
      linarith
    refine ⟨s.output,α.trans s.chart,μ/2,half_pos hμ,hpath.snoc s,hbandNext,hcoeffNext,?_,?_,hrNext,(fun _ => hgoodNext),s.nextFrame F',?_,?_⟩
    · have hh := colorModel_step_error C.density_continuous E.density_continuous
        s.output.density_continuous ha ha3 hell hells L (N:ℤ)
      have hs := iterationError_step ht.le k
      linarith
    · intro r
      have htwo := hpath.physicalError_eq (E.vector r) (s.output.vector r ∘ s.chart)
      have hh := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        ((s.output.vector_continuous r).comp (s.chart_continuous.comp hpath.continuous))
      change physicalError (C.vector r) (s.output.vector r ∘ (α.trans s.chart)) ≤
        2*physicalError (C.vector r) (E.vector r ∘ α)+
          2*physicalError (E.vector r ∘ α) ((s.output.vector r ∘ s.chart) ∘ α) at hh
      rw [htwo] at hh
      have hs := iterationError_step ht.le k
      have hp := hphysical r
      have hp' := (hcolor r).1
      linarith
    · rw [s.nextFrame_chart,hF']
      rfl
    · exact (hjets.trans hjetStep).mono (by
        have hs := iterationError_step ht.le k
        have hn := iterationError_nonneg ht.le k
        linarith)
  obtain ⟨B,hB⟩ := finite_frequency_tree Reach hzero hstep
  refine ⟨B,?_⟩
  intro L hL
  obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herr,hphys,hrE,hgoodE,F',hF',hjets⟩ := hB L hL
  exact ⟨E,α,hpath,herr.trans_lt hfinal,fun r => (hphys r).trans_lt hfinal,
    μ,hμ,hbandE,hmatchE,hrE,hgoodE,F',hF',hjets.mono hfinal.le⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Accuracy requirements for the actual anchor are fixed BEFORE that anchor
is made. Given any such actual anchor, the two block tests are achieved on one
actual endpoint of a sequence of neutral/signal pairs. -/
theorem ColoredSignalControlledRealizes.block {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalControlledRealizes b D d γ ell)
    (hdc : Continuous d) (hds : HasCompactSupport d) (hγ : 0 < γ)
    {m n : ℕ} {p : Fin m → UnitAddCircle → ℝ}
    (hp : ∀ r z, 0 ≤ p r z) (hc : ∀ r, Continuous (p r)) (tags : Fin m → ℂ)
    (htags : ∀ r, ‖tags r‖ ≤ 1) {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqB : ∀ z, ‖q z‖ ≤ 2) (hA : Continuous A) (k : ℕ)
    {delta nu ε : ℝ} (hell : 0 < ell) (hells : 6*ell ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1/100)
    (hn0 : delta/2 ≤ (n:ℝ)*ell^2) (hn1 : (n:ℝ)*ell^2 ≤ delta)
    (hmass : (∫ z, blockTotal p z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal p z)*‖blockTagMean p tags z-q z‖^2 ∂phaseHaar) ≤ delta)
    (hnu : 0 < nu) (hε : 0 < ε)
    (τR : Fin m → Fin m) (Q : PhysicalJetData) {κ : ℝ} (hκ : 0 < κ) :
    ∃ e ω : ℝ, 0 < e ∧ 0 < ω ∧
      ∀ C : ColoredState (Fin m), C.Reflection τR → colorL1Distance p C.density ≤ e →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d (fun r z => tags r-q z) ω → ∀ F : PhysicalFrame,
      ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ((∫ z, Real.sqrt (blockTotal p z) ∂phaseHaar)-300*delta^2-nu ≤
            ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
          ((∑ r, ∫ z, E.density r z*
            ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
            (∫ z, blockPreviousError p tags A k z ∂phaseHaar)+4/delta+nu) ∧
          E.Reflection τR ∧
          (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
          ∃ F' : PhysicalFrame, F'.chart = F.chart.trans α ∧ Q.Close ε F C.packets.V F' E.packets.V := by
  obtain ⟨e0,he0,htests⟩ := block_diagonal_transfer hp hc tags htags hq hqB hA k
    hell hells hd hd1 hn0 hn1 hmass hcenter hnu
  let a : Fin m → UnitAddCircle → ℂ := fun r z => tags r-q z
  have ha : ∀ r, Continuous (a r) := fun r => continuous_const.sub hq
  have ha3 : ∀ r z, ‖a r z‖ ≤ 3 := fun r z =>
    (norm_sub_le _ _).trans (by linarith [htags r,hqB z])
  obtain ⟨ω,hω,hiteration⟩ := hsignal.iterate hdc hds hγ hell.le hells m n τR a ha ha3
    Q (M := 3) (by norm_num) (lt_min (half_pos he0) hε) hκ
  let e : ℝ := min 1 (e0/(2*2^n))
  have he : 0 < e := lt_min zero_lt_one (div_pos he0 (by positivity))
  refine ⟨e,ω,he,hω,?_⟩
  intro C hrC hclose margin hmargin hband hmatch F
  have hmassC : colorMass C.density ≤ 3 := by
    have h0 := colorMass_le_add_distance hc C.density_continuous
    rw [colorMass_eq_integral_total hc] at h0
    have he1 : e ≤ 1 := min_le_left _ _
    linarith
  obtain ⟨B,hB⟩ := hiteration C hrC hmassC margin hmargin hband hmatch F
  obtain ⟨L,hL,hLB,htest⟩ := htests B
  obtain ⟨E,α,hpath,hdensity,hphysical,_μ,_hμ,_hbandE,_hmatchE,hrE,hgoodE,F',hF',hjets⟩ := hB L hLB
  have hinitial := colorModel_initial_error hc C.density_continuous ha ha3 hell.le hells L
  have hsmall : 2^n*colorL1Distance p C.density ≤ e0/2 := by
    have he2 : e ≤ e0/(2*2^n) := min_le_right _ _
    have hprod := (le_div_iff₀ (show (0:ℝ) < 2*2^n by positivity)).1 (hclose.trans he2)
    nlinarith
  have hmodels := colorL1Distance_triangle (continuous_colorModel hc ha ell L)
    (continuous_colorModel C.density_continuous ha ell L) E.density_continuous
  have herr : colorL1Distance (blockModelColors p tags q ell L) E.density ≤ e0 := by
    rw [← colorModel_eq_blockModelColors]
    change colorL1Distance (colorModel p a ell L) E.density ≤ e0
    have hi := hinitial.trans hsmall
    have hd' := lt_of_lt_of_le hdensity (min_le_left (e0/2) ε)
    linarith
  obtain ⟨hsqrt,hpred⟩ := htest E.density E.density_continuous E.density_nonneg herr
  have hnpos : 0 < n := by
    by_contra hh
    have hn : n = 0 := by omega
    rw [hn] at hn0
    norm_num at hn0
    linarith
  exact ⟨L,hL,E,α,hpath,(fun r => (hphysical r).trans_le (min_le_right _ _)),hsqrt,hpred,hrE,hgoodE hnpos,F',hF',hjets.mono (min_le_right _ _)⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace ColoredAnchor
variable {R : Type} {C : ColoredState R} {n : ℕ} (s : ColoredAnchor C n)

def nextFrame (F : PhysicalFrame) : PhysicalFrame :=
  F.next s.geometry C.packets.smooth_speed n

lemma nextFrame_chart (F : PhysicalFrame) : (s.nextFrame F).chart = F.chart.trans s.chart := rfl
end ColoredAnchor

/-- The carrier precedes the block signal and every block accuracy requirement.
The output retains the literal actual geometry and finite amplitudes. -/
theorem eventually_colored_controlled_anchor {m : ℕ} (C : ColoredState (Fin m))
    {τR : Fin m → Fin m} (hrC : C.Reflection τR) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (tags : Fin m → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ C.packets.core i → ∀ s,
        |s-(C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)| < τ →
        d s = tags (C.color i)-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ (Q : PhysicalJetData) (F : PhysicalFrame) (ζ : ℝ), 0 < ζ →
      ∀ ε e ω κ : ℝ, 0 < ε → 0 < e → 0 < ω → 0 < κ →
      ∀ᶠ n : ℕ in atTop, ∃ s : ColoredAnchor C n,
        Q.Close ζ F C.packets.V (s.nextFrame F) s.final.V ∧
        s.geometry.c = c ∧
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        (∀ r, physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε) ∧
        colorL1Distance C.density s.output.density < e ∧
        s.output.InBand b D margin ∧
        s.output.Matches d (fun r z => tags r-q z) ω ∧
        s.output.Reflection τR ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < κ ∧ s.final.GoodArc δ := by
  classical
  obtain ⟨τref,hr,hτref⟩ := hrC
  filter_upwards [eventually_reflected_anchor_state C.packets C.injective C.spare hr] with c hc
  intro d q tags hq b D margin τ hτ hroom Q F ζ hζ ε e ω κ hε he hω hκ
  let K : ℝ := Fintype.card C.Index
  have hK : 0 ≤ K := Nat.cast_nonneg _
  let e' : ℝ := min (ε/(K^2+1)) (e/((m:ℝ)*K+1))
  have he' : 0 < e' := lt_min (div_pos hε (by positivity)) (div_pos he (by positivity))
  have hphysicalBudget : K^2*e' < ε := by
    have he1 : e' ≤ ε/(K^2+1) := min_le_left _ _
    have hp := (le_div_iff₀ (show 0 < K^2+1 by positivity)).1 he1
    nlinarith
  have hdensityBudget : (m:ℝ)*K*e' < e := by
    have he1 : e' ≤ e/((m:ℝ)*K+1) := min_le_right _ _
    have hp := (le_div_iff₀ (show 0 < (m:ℝ)*K+1 by positivity)).1 he1
    nlinarith
  obtain ⟨g,hgc,δ,cut,L,hδ,hδκ,hL,hgJ,S,hready⟩ := hc d q (tags ∘ C.color) hq
    b D margin τ hτ hroom e' ω κ he' hω hκ
  obtain ⟨n₀,hn₀⟩ := hready.exists
  obtain ⟨hn₀p,G₀,_hG₀i,_hG₀mod,hG₀V,_hG₀m,_tail⟩ := hn₀
  have hgJs := g.smooth_jitter_of_output G₀ hn₀p hG₀V
  filter_upwards [hready,Q.eventually_next F g C.packets.smooth_speed hgJs hζ] with n hn hjet
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herror,hband,hmatch,τG,hτG,hrG,hgoodG⟩ := hn
  let s : ColoredAnchor C n := ⟨g,S n,hnp,G,hGi,hGmod,hGV,hGm⟩
  refine ⟨s,?_,hgc,⟨δ,cut,L,hδ,hδκ,hL,hgJ⟩,?_,?_,hband,?_,⟨τG,hrG,?_⟩,⟨δ,hδ,hδκ,hgoodG⟩⟩
  · change Q.Close ζ F C.packets.V (F.next g C.packets.smooth_speed n) G.V
    rw [hGV]
    exact hjet
  · intro r
    have hh := colored_physical_bound
      (fun i => continuous_packet (C.packets.continuous_amplitude i))
      (fun i => (continuous_outputVector G i).comp (continuous_passageChart (g.Hcontinuous n)))
      C.color r he'.le (fun i => (herror i).1.le) hphysicalBudget
    change physicalError (C.vector r) _ < ε at hh
    have heq : (s.output.vector r ∘ s.chart) =
        (fun x => ∑ i, if C.color i = r then outputVector G i (passageChart (g.H n) x) else 0) := by
      funext x
      exact colorVector_output G C.color r _
    rw [heq]
    exact hh
  · have hcolor r : (∫ z, |C.density r z-s.output.density r z| ∂phaseHaar) ≤ K*e' := by
      have hh := colored_density_bound
        (fun i => continuous_outputDensity G i) C.packets.density_continuous C.color r
        (fun _ => 0) (γ := 0) (ω := 0) he'.le (fun i => by simpa using (herror i).2.le)
      simp only [zero_mul,zero_add] at hh
      have heq : (fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) =
          s.output.density r := by
        funext z
        exact (colorDensity_output G C.color r z).symm
      change (∫ z, |(fun z => ∑ i, if C.color i = r then outputDensity G i z else 0) z-
        C.density r z| ∂phaseHaar) ≤ K*e' at hh
      rw [heq] at hh
      simpa only [abs_sub_comm] using hh
    apply (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hcolor r)).trans_lt
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hdensityBudget
  · intro i y _hy
    exact (hmatch i y).le
  · intro i
    change C.color ((τG i).1) = τR (C.color i.1)
    exact (congrArg C.color (hτG i)).trans (hτref i.1)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- All signal parameters and tolerances are fixed before the anchor. The
endpoint is a genuine actual state linked by its anchor and finite passage
path, and satisfies both prescribed source block inequalities. The input
reflection hypotheses are the ordinary packet reality conditions needed to
construct the real-symmetric band signal. -/
theorem actual_controlled_block_of_center {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {q A : UnitAddCircle → ℂ} (hq : Continuous q)
    (hqs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (hqr : ∀ z, q (-z) = conj (q z)) (hqB : ∀ z, ‖q z‖ ≤ 2)
    (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2)
    (hcenter : (∫ z, Real.sqrt (blockTotal C.density z)*
      ‖blockTagMean C.density tags z-q z‖^2 ∂phaseHaar) ≤ delta) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ n : ℕ, ∃ ell : ℝ, 0 < n ∧ 0 < ell ∧ 6*ell ≤ 1 ∧
      delta/2 ≤ (n:ℝ)*ell^2 ∧ (n:ℝ)*ell^2 ≤ delta ∧
      ∃ N : ℕ, ∃ s : ColoredAnchor C N,
        (∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ K : ℝ,
          0 < δ ∧ δ < κ ∧ 0 < K ∧ s.geometry.J₀ = neutralJitterReal cut K 0) ∧
        ∃ L : Fin n → ℤ, (∀ j, 0 < L j) ∧
          ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
            ColoredPath s.output L E α ∧
            (∀ r, physicalError (C.vector r) (E.vector r ∘ s.chart.trans α) < ε) ∧
            ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
              ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
            ((∑ r, ∫ z, E.density r z*
              ‖A z+blockDiagonalEstimator q ell L z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
              (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) ∧
            E.Reflection τR ∧
            (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
            ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans (s.chart.trans α) ∧
              Q.Close ε F₀ C.packets.V F' E.packets.V := by
  classical
  obtain ⟨τ,hr,hτ⟩ := hrC
  have hmr := hr.index
  have hcore i : C.packets.core i ⊆ C.packets.core (τ i) := by rw [hr.core]
  have htr i : tags (C.color (τ i)) = conj (tags (C.color i)) := by rw [hτ,htrR]
  obtain ⟨c,hsep,hanchor⟩ := ((eventually_integral_speed_separation C.packets.m
    C.packets.periodic.lift C.packets.nonzero C.packets.speed_continuous).and
    (eventually_colored_controlled_anchor C ⟨τ,hr,hτ⟩)).exists
  let K : C.Index → Set ℝ := fun i =>
    (fun x => (C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)) '' C.packets.core i
  have hK i : IsCompact (K i) := (C.packets.core_compact i).image
    (continuous_const.mul (continuous_const.add C.packets.smooth_speed.continuous))
  have hK0 i : 0 ∉ K i := by
    rintro ⟨x,_hx,he⟩
    exact hsep.2.1 i (x:UnitAddCircle) he
  have hKd : Pairwise (Disjoint on K) := by
    intro i j hij
    change Disjoint (K i) (K j)
    rw [Set.disjoint_left]
    rintro z ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (C.injective (hsep.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  have hKr i x (hx : x ∈ K i) : -x ∈ K (τ i) := by
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨y,hcore i hy,?_⟩
    simp only [hmr,Int.cast_neg,neg_mul]
  obtain ⟨d,hds,hdcompact,hd0,hdr,hdlocal⟩ := exists_symmetric_anchor_band K hK hKd hK0
    τ hKr (tags ∘ C.color) htr hqs hqr
  obtain ⟨b,D,μ,t,hb,hbD,hμ,ht,hdsupport,hroom⟩ := anchor_uniform_room K hK hK0 hdcompact
    (fun i y => tags (C.color i)-q (y:UnitAddCircle)) hdlocal
  obtain ⟨P,γ₀,_hP,_hPD,hγ₀,hsignal⟩ := exists_concrete_colored_controlled_signal hb hbD hds hdcompact hdr hd0 hdsupport
  let γ : ℝ := min γ₀ (delta/2)/2
  have hγ : 0 < γ := half_pos (lt_min hγ₀ (half_pos hd))
  have hγ₀' : γ ≤ γ₀ := by
    have hh := min_le_left γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  have hγd : γ ≤ delta/2 := by
    have hh := min_le_right γ₀ (delta/2)
    dsimp [γ]
    linarith [lt_min hγ₀ (half_pos hd)]
  let ell := refreshedStrength (signalPrimeProduct P) γ
  have hell : 0 < ell := refreshedStrength_pos _ hγ
  have helg : ell ≤ γ := refreshedStrength_le _ hγ.le
  have hells : 6*ell ≤ 1 := by linarith
  have helld : ell^2 ≤ delta/2 := by
    have hel1 : ell ≤ 1 := by linarith
    nlinarith
  obtain ⟨n,hn,hn0,hn1⟩ := exists_block_length hell hd helld
  obtain ⟨_hbound,hsig⟩ := hsignal γ hγ hγ₀'
  obtain ⟨e,ω,he,hω,hblock⟩ := hsig.block hds.continuous hdcompact hγ C.density_nonneg
    C.density_continuous tags htags hq hqB hA k hell hells hd hd1 hn0 hn1 hmass hcenter hnu
    (show 0 < ε/4 by positivity) τR Q hκ
  have hanchorReady := hanchor d q tags hq b D μ t ht
    (fun i x hx s hs => hroom i _ ⟨x,hx,rfl⟩ s hs)
    Q F₀ (ε/4) (by positivity) (ε/4) e ω κ (by positivity) he hω hκ
  obtain ⟨N,s,hjetAnchor,_hsc,hjitter,hphysical,hclose,hband,hmatch,hrAnchor,_hgoodAnchor⟩ := hanchorReady.exists
  obtain ⟨L,hL,E,α,hpath,hmovement,hsqrt,hpred,hrE,hgoodE,F',hF',hjets⟩ := hblock s.output hrAnchor hclose.le μ hμ hband hmatch (s.nextFrame F₀)
  refine ⟨n,ell,hn,hell,hells,hn0,hn1,N,s,hjitter,L,hL,E,α,hpath,?_,hsqrt,hpred,hrE,hgoodE,F',?_,?_⟩
  · intro r
    have hmove : physicalError (s.output.vector r ∘ s.chart)
        ((E.vector r ∘ α) ∘ s.chart) < ε/4 := by
      change physicalError (s.output.vector r ∘ passageChart (s.geometry.H N))
        ((E.vector r ∘ α) ∘ passageChart (s.geometry.H N)) < ε/4
      rw [physicalError_chart (s.geometry.Hcontinuous N).measurable]
      exact hmovement r
    have htriangle := physicalError_triangle (C.vector_continuous r)
      ((s.output.vector_continuous r).comp s.chart_continuous)
      (((E.vector_continuous r).comp hpath.continuous).comp s.chart_continuous)
    change physicalError (C.vector r) ((E.vector r ∘ α) ∘ s.chart) < ε
    have hfirst := hphysical r
    linarith
  · rw [hF',s.nextFrame_chart]
    rfl
  · exact (hjetAnchor.trans hjets).mono (by linarith)

end ThreeTorus
end
end

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
theorem actual_controlled_block {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {A : UnitAddCircle → ℂ} (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ β : Equiv.Perm TripleTorus, ∃ D : UnitAddCircle → ℂ,
      ActualColoredBlock C E β D ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ β) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖A z+D z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
        (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) ∧
      E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans β ∧ Q.Close ε F₀ C.packets.V F' E.packets.V := by
  obtain ⟨q,hq,hqs,hqB,hqr,hcenter⟩ := C.exists_center hrC hτR htags htrR hd
  obtain ⟨n,ell,hn,hell,_hells,_hn0,_hn1,N,s,_hjitter,L,_hL,E,α,hpath,hphys,hsqrt,hpred,hr,hgood,F',hF',hjets⟩ :=
    actual_controlled_block_of_center C τR hrC tags htags htrR hq hqs hqr hqB hA k
      hd hd1 hnu hε hκ hmass hcenter.le Q F₀
  exact ⟨E,s.chart.trans α,blockDiagonalEstimator q ell L,
    ⟨n,ell,hn,hell,q,hq,hqs,hqr,N,s,L,α,hpath,rfl,rfl⟩,
    hphys,hsqrt,hpred,hr,hgood,F',hF',hjets⟩

end ThreeTorus
end
end

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
theorem actual_controlled_repeated_blocks {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {delta ε κ : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (K : ℕ) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ A : UnitAddCircle → ℂ,
      ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-400*(K:ℝ)*delta^2 ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∫ z, blockPreviousError E.density tags A K z ∂phaseHaar) ≤ (K:ℝ)*(5/delta)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (0 < K → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close ε F₀ C.packets.V F' E.packets.V := by
  induction K generalizing ε with
  | zero =>
    refine ⟨C,Equiv.refl _,fun _ => 0,ActualColoredBlocks.nil,?_,?_,?_,hmass,hrC,?_,F₀,rfl,?_⟩
    · intro r
      simpa [physicalError] using hε
    · simp
    · simp [blockPreviousError]
    · omega
    · exact (Q.close_refl F₀ C.packets.V).mono hε.le
  | succ K ih =>
    obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,_hgoodE,F₁,hF₁,hjet₁⟩ := ih (show 0 < ε/4 by positivity)
    obtain ⟨η,hη,hmassBudget⟩ := E.mass_transport_tolerance hmassE
    let e : ℝ := min η (ε/4)
    have he : 0 < e := lt_min hη (by positivity)
    obtain ⟨F,β,D,hblock,hphysB,hsqrtB,hpredB,hrF,hgoodF,F₂,hF₂,hjet₂⟩ := actual_controlled_block E
      τR hτR hrE tags htags htrR hpath.estimator_continuous K hd hd1
      (sq_pos_of_pos hd) he hκ hmassE.le Q F₁
    have hsmall r : physicalError (E.vector r) (F.vector r ∘ β) < η :=
      (hphysB r).trans_le (min_le_left _ _)
    have hmassF := hmassBudget F β D hblock hsmall
    refine ⟨F,α.trans β,fun z => A z+D z,hpath.snoc hblock,?_,?_,?_,hmassF,hrF,(fun _ => hgoodF),F₂,?_,?_⟩
    · intro r
      have hmove : physicalError (E.vector r ∘ α) ((F.vector r ∘ β) ∘ α) < ε/4 := by
        rw [hpath.physicalError_eq]
        exact (hphysB r).trans_le (min_le_right _ _)
      have htriangle := physicalError_triangle (C.vector_continuous r)
        ((E.vector_continuous r).comp hpath.continuous)
        (((F.vector_continuous r).comp hblock.continuous).comp hpath.continuous)
      change physicalError (C.vector r) ((F.vector r ∘ β) ∘ α) < ε
      have hh := hphys r
      linarith
    · push_cast
      nlinarith [sq_nonneg delta]
    · rw [integral_blockPreviousError_eq (A := fun z => A z+D z) F.density_continuous tags
        (hpath.estimator_continuous.add hblock.estimator_continuous) (K+1)]
      simp only [Nat.cast_add,Nat.cast_one] at *
      have hinc := block_increment_budget hd hd1
      nlinarith

    · rw [hF₂,hF₁]
      rfl
    · exact (hjet₁.trans hjet₂).mono (by have hh : e ≤ ε/4 := min_le_right _ _; linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The source prediction estimate, for actual reflected packet passages.
Every finite family of physical smooth restrictions is imposed in the actual
passage selections, in the required quantifier order. -/
theorem actual_controlled_density_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ Ψ : UnitAddCircle → ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧ Ψ = (fun z => A z/(K:ℂ)) ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖Ψ z-tags r‖^2 ∂phaseHaar) < ε^2) ∧
      Continuous Ψ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => Ψ (x:UnitAddCircle)) ∧
      (∀ z, Ψ (-z) = conj (Ψ z)) ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close η F₀ C.packets.V F' E.packets.V := by
  obtain ⟨δ,hd,hd1,hK,hloss,hbudget⟩ := exists_prediction_budget hε hτ
  let K := ⌈10/(ε^2*δ)⌉₊
  change 0 < K at hK
  obtain ⟨E,α,A,hpath,hphys,hsqrt,hpred,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_repeated_blocks C τR hτR hrC tags htags htrR hd hd1 hη hκ hmass K Q F₀
  refine ⟨E,α,fun z => A z/(K:ℂ),K,A,hK,hpath,rfl,hphys,?_,?_,
    hpath.estimator_continuous.div_const _,hpath.estimator_smooth.div_const _,?_,
    hmassE,hrE,hgood hK,F',hF',hjets⟩
  · change 400*(K:ℝ)*δ^2 < τ at hloss
    linarith
  · rw [averaged_prediction_identity E.density_continuous tags hpath.estimator_continuous hK]
    have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
    have he : (K:ℝ)*(5/δ)/(K:ℝ)^2 = 5/((K:ℝ)*δ) := by field_simp
    exact (div_le_div_of_nonneg_right hpred (sq_nonneg _)).trans_lt (he ▸ hbudget)
  · intro z
    simp only [hpath.estimator_reflection]
    simp

end ThreeTorus
end
end

section
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
/-- Actual finite Laurent approximation to the OLD tagged packet sum after
reflected signal blocks. Neither a cyclic-space oracle nor a formal spectral
operator is used: the witness is a literal finite sum of twist iterates. -/
theorem actual_controlled_cyclic_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ c : ℤ →₀ ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      physicalError (fun x => ∑ r, tags r*C.vector r x) (E.laurent c ∘ α) < ε^2 ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧ Q.Close η F₀ C.packets.V F' E.packets.V := by
  let e := min η (ε^2/(16*((m:ℝ)+1)^2))
  have he : 0 < e := lt_min hη (div_pos (sq_pos_of_pos hε) (by positivity))
  obtain ⟨E,α,Ψ,K,A,hK,hpath,hΨdef,hphys,hsqrt,hpred,hΨ,_,_,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_density_prediction C τR hτR hrC tags htags htrR (show 0 < ε/8 by positivity)
      hτ he hκ hmass Q F₀
  obtain ⟨c,hc⟩ := E.exists_laurent_approx hΨ (show 0 < ε^2/64 by positivity)
  refine ⟨E,α,c,K,A,hK,hpath,fun r => (hphys r).trans_le (min_le_left _ _),hsqrt,?_,hmassE,hrE,hgood,F',hF',hjets.mono (min_le_left _ _)⟩
  let G : TripleTorus → ℂ := fun x => ∑ r, tags r*E.vector r x
  let F : TripleTorus → ℂ := fun x => ∑ r, tags r*C.vector r x
  let W := E.weightedVector (fun _ => Ψ)
  have hG : Continuous G := continuous_finsetSum _ (fun r _ => continuous_const.mul (E.vector_continuous r))
  have hF : Continuous F := continuous_finsetSum _ (fun r _ => continuous_const.mul (C.vector_continuous r))
  have hW : Continuous W := E.weightedVector_continuous (fun _ => hΨ)
  have hp : physicalError G W < (ε/8)^2 := by
    rw [physicalError_symm]
    exact (E.physical_prediction_energy tags hΨ).trans_lt hpred
  have ht := physicalError_triangle hG hW (E.laurent_continuous c)
  have heL : physicalError G (E.laurent c) < ε^2/16 := by linarith
  have htag : physicalError F (G ∘ α) ≤ (m:ℝ)^2*e :=
    physicalError_tagged_sum C.vector_continuous
      (fun r => (E.vector_continuous r).comp hpath.continuous) tags htags
      (fun r => (hphys r).le)
  have hsmall : (m:ℝ)^2*e < ε^2/16 := by
    have he' : e ≤ ε^2/(16*((m:ℝ)+1)^2) := min_le_right _ _
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    have hden : 0 < 16*((m:ℝ)+1)^2 := by positivity
    have hmul : e*(16*((m:ℝ)+1)^2) ≤ ε^2 := (le_div_iff₀ hden).1 he'
    nlinarith [sq_nonneg (m:ℝ)]
  have hlast := physicalError_triangle hF (hG.comp hpath.continuous)
    ((E.laurent_continuous c).comp hpath.continuous)
  rw [hpath.physicalError_eq] at hlast
  change physicalError F (E.laurent c ∘ α) < ε^2
  linarith [sq_pos_of_pos hε]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma ColoredState.laurent_smul {m : ℕ} (C : ColoredState (Fin m)) (b : ℂ)
    (c : ℤ →₀ ℂ) (x : TripleTorus) : C.laurent (b • c) x = b * C.laurent c x := by
  change (b • c).sum (fun k z => z * C.totalVector
    (twistIter (fun u => (C.packets.periodic.lift u:UnitAddCircle)) k x)) = _
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, ColoredState.laurent, mul_assoc, Finset.mul_sum]

/-- Arbitrary finite reflected tags, rescaled before any signal/jet choices. -/
theorem actual_controlled_tagged_prediction {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htrR : ∀ r, tags (τR r) = conj (tags r))
    {ε τ η κ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) (hη : 0 < η) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) < 2)
    (Q : PhysicalJetData) (F₀ : PhysicalFrame) :
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
      ∃ c : ℤ →₀ ℂ, ∃ K : ℕ, ∃ A : UnitAddCircle → ℂ,
      0 < K ∧ ActualColoredBlocks C E K α A ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < η) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-τ <
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      physicalError (fun x => ∑ r, tags r*C.vector r x) (E.laurent c ∘ α) < ε^2 ∧
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 ∧ E.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) ∧
      ∃ F' : PhysicalFrame, F'.chart = F₀.chart.trans α ∧
        Q.Close η F₀ C.packets.V F' E.packets.V := by
  let M : ℝ := 1 + ∑ r, ‖tags r‖
  have hM : 0 < M := by dsimp [M]; positivity
  have ht (r : Fin m) : ‖tags r‖ ≤ M := by
    have hs : ‖tags r‖ ≤ ∑ s, ‖tags s‖ :=
      Finset.single_le_sum (fun s _ => norm_nonneg (tags s)) (Finset.mem_univ r)
    dsimp [M]; linarith
  let b : Fin m → ℂ := fun r => tags r / (M:ℂ)
  have hb (r : Fin m) : ‖b r‖ ≤ 1 := by
    simp only [b, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
    exact (div_le_one hM).2 (ht r)
  have hbr (r : Fin m) : b (τR r) = conj (b r) := by
    simp only [b,htrR,map_div₀,Complex.conj_ofReal]
  obtain ⟨E,α,c,K,A,hK,hpath,hphys,hsqrt,hpred,hmassE,hrE,hgood,F',hF',hjets⟩ :=
    actual_controlled_cyclic_prediction C τR hτR hrC b hb hbr (div_pos hε hM)
      hτ hη hκ hmass Q F₀
  refine ⟨E,α,(M:ℂ) • c,K,A,hK,hpath,hphys,hsqrt,?_,hmassE,hrE,hgood,F',hF',hjets⟩
  have he : (fun x => ∑ r, tags r*C.vector r x) =
      (fun x => (M:ℂ) * ∑ r, b r*C.vector r x) := by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [b]
    field_simp [show (M:ℂ) ≠ 0 by exact_mod_cast hM.ne']
  rw [he]
  have hl : E.laurent ((M:ℂ) • c) ∘ α = fun x => (M:ℂ) * E.laurent c (α x) := by
    funext x
    exact E.laurent_smul _ _ _
  rw [hl,physicalError_const_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  have hi := mul_lt_mul_of_pos_left hpred (sq_pos_of_pos hM)
  have hid : M^2 * (ε/M)^2 = ε^2 := by field_simp
  exact hi.trans_eq hid

end ThreeTorus
end
end

end OAI
