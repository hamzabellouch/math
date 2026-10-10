import OAI.Dynamics.ThreeTorus.ColorBlocks
import OAI.Dynamics.ThreeTorus.Prediction
import OAI.Dynamics.ThreeTorus.SymmetricPackets

namespace OAI

/-! Symmetric anchored blocks, unconditional block production, physical mass, and estimator regularity. -/

section

/-! Concrete finite colored iteration. The cofinal-frequency tree is built
from actual neutral--signal pairs. The error budget is fixed before the
initial anchor state and before any future packet index type is known. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def ColoredSignalReflectedRealizes (b D : ℝ) (d : ℝ → ℂ) (γ ell : ℝ) : Prop :=
  ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
    ∀ τR : R → R, C.Reflection τR →
    ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
    ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
    ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
    ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
    ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧
      s.output.Reflection τR ∧
      (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ s.final.GoodArc δ) ∧ ∀ r,
      physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
      (∫ z, |s.output.density r z-C.density r z*colorFactor a ell (N:ℤ) r z| ∂phaseHaar) <
        2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε

/-- The interface is discharged by the actual geometric construction. -/
theorem exists_concrete_colored_reflected_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ColoredSignalReflectedRealizes b D d γ (refreshedStrength (signalPrimeProduct L) γ) :=
  exists_colored_reflected_signal hb hbD hd hdc hdr hd0 hds

/-- Fixed data and a small coefficient tolerance first; the threshold tree is
chosen on the actual initial state; ALL diagonals above that tree are realized
with small product-model and physical errors. No independence of the diagonal,
modeled next state, or unproved packet producer is used. -/
theorem ColoredSignalReflectedRealizes.iterate {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalReflectedRealizes b D d γ ell)
    (hd : Continuous d) (hdc : HasCompactSupport d) (hγ : 0 < γ)
    (hell : 0 ≤ ell) (hells : 6*ell ≤ 1)
    (m n : ℕ) (τR : Fin m → Fin m) (a : Fin m → UnitAddCircle → ℂ)
    (ha : ∀ r, Continuous (a r)) (ha3 : ∀ r z, ‖a r z‖ ≤ 3)
    {M ε κ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ C : ColoredState (Fin m), C.Reflection τR →
      colorMass C.density ≤ M → ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d a ω →
      ∃ B : (j : ℕ) → (Fin j → ℤ) → ℤ, ∀ L : Fin n → ℤ,
        (∀ j : Fin n, B j (fun i => L ⟨i.val,i.isLt.trans j.isLt⟩) < L j) →
        ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus,
          ColoredPath C L E α ∧
          colorL1Distance (colorModel C.density a ell L) E.density < ε ∧
          (∀ r, physicalError (C.vector r) (E.vector r ∘ α) < ε) ∧
          ∃ μ : ℝ, 0 < μ ∧ E.InBand b D μ ∧ E.Matches d a (((n:ℝ)+1)*ω) ∧ E.Reflection τR ∧
            (0 < n → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ) := by
  classical
  obtain ⟨t,ω,U,ht,hω,hU,hfinal,hmassBound,hsubstitution⟩ := finite_iteration_budget n hM hγ hε
  obtain ⟨e,he,het,hem⟩ := finite_color_tolerance m ht
  refine ⟨ω,hω,?_⟩
  intro C hrC hmass margin hmargin hband hmatch
  let Reach (k : ℕ) (L : Fin k → ℤ) : Prop :=
    ∃ E : ColoredState (Fin m), ∃ α : Equiv.Perm TripleTorus, ∃ μ : ℝ,
      0 < μ ∧ ColoredPath C L E α ∧ E.InBand b D μ ∧
      E.Matches d a (((k:ℝ)+1)*ω) ∧
      colorL1Distance (colorModel C.density a ell L) E.density ≤ iterationError t k ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ α) ≤ iterationError t k) ∧
      E.Reflection τR ∧
      (0 < k → ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ)
  have hzero : Reach 0 (fun i => Fin.elim0 i) := by
    refine ⟨C,Equiv.refl _,margin,hmargin,ColoredPath.nil,hband,?_,?_,?_,hrC,(by intro h; omega)⟩
    · simpa using hmatch
    · rw [colorModel_zero]
      simpa [colorL1Distance,iterationError] using ht.le
    · intro r
      simpa [physicalError,iterationError] using ht.le
  have hstep : ∀ k (L : Fin k → ℤ), k < n → Reach k L →
      ∀ᶠ N : ℤ in atTop, Reach (k+1) (Fin.snoc L N) := by
    intro k L hk hreach
    obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herror,hphysical,hrE,_hgoodE⟩ := hreach
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
    have hready := hsignal (Fin m) E τR hrE μ hμ hbandE a ha (((k:ℝ)+1)*ω) hωk hmatchE e η κ he hη hκ
    apply eventually_int_of_eventually_nat
    filter_upwards [hready] with N hN
    obtain ⟨s,htrack,hrNext,hgoodNext,hcolor⟩ := hN
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
    refine ⟨s.output,α.trans s.chart,μ/2,half_pos hμ,hpath.snoc s,hbandNext,hcoeffNext,?_,?_,hrNext,(fun _ => hgoodNext)⟩
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
  obtain ⟨B,hB⟩ := finite_frequency_tree Reach hzero hstep
  refine ⟨B,?_⟩
  intro L hL
  obtain ⟨E,α,μ,hμ,hpath,hbandE,hmatchE,herr,hphys,hrE,hgoodE⟩ := hB L hL
  exact ⟨E,α,hpath,herr.trans_lt hfinal,fun r => (hphys r).trans_lt hfinal,
    μ,hμ,hbandE,hmatchE,hrE,hgoodE⟩

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
theorem ColoredSignalReflectedRealizes.block {b D γ ell : ℝ} {d : ℝ → ℂ}
    (hsignal : ColoredSignalReflectedRealizes b D d γ ell)
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
    (τR : Fin m → Fin m) {κ : ℝ} (hκ : 0 < κ) :
    ∃ e ω : ℝ, 0 < e ∧ 0 < ω ∧
      ∀ C : ColoredState (Fin m), C.Reflection τR → colorL1Distance p C.density ≤ e →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      C.Matches d (fun r z => tags r-q z) ω →
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
          ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ := by
  obtain ⟨e0,he0,htests⟩ := block_diagonal_transfer hp hc tags htags hq hqB hA k
    hell hells hd hd1 hn0 hn1 hmass hcenter hnu
  let a : Fin m → UnitAddCircle → ℂ := fun r z => tags r-q z
  have ha : ∀ r, Continuous (a r) := fun r => continuous_const.sub hq
  have ha3 : ∀ r z, ‖a r z‖ ≤ 3 := fun r z =>
    (norm_sub_le _ _).trans (by linarith [htags r,hqB z])
  obtain ⟨ω,hω,hiteration⟩ := hsignal.iterate hdc hds hγ hell.le hells m n τR a ha ha3
    (M := 3) (by norm_num) (lt_min (half_pos he0) hε) hκ
  let e : ℝ := min 1 (e0/(2*2^n))
  have he : 0 < e := lt_min zero_lt_one (div_pos he0 (by positivity))
  refine ⟨e,ω,he,hω,?_⟩
  intro C hrC hclose margin hmargin hband hmatch
  have hmassC : colorMass C.density ≤ 3 := by
    have h0 := colorMass_le_add_distance hc C.density_continuous
    rw [colorMass_eq_integral_total hc] at h0
    have he1 : e ≤ 1 := min_le_left _ _
    linarith
  obtain ⟨B,hB⟩ := hiteration C hrC hmassC margin hmargin hband hmatch
  obtain ⟨L,hL,hLB,htest⟩ := htests B
  obtain ⟨E,α,hpath,hdensity,hphysical,_μ,_hμ,_hbandE,_hmatchE,hrE,hgoodE⟩ := hB L hLB
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
  exact ⟨L,hL,E,α,hpath,(fun r => (hphysical r).trans_le (min_le_right _ _)),hsqrt,hpred,hrE,hgoodE hnpos⟩

end ThreeTorus
end
end

section

/-! The correctly ordered anchor constructs the literal finite output state,
with coefficient matching valid on every next packet core. -/
noncomputable section
open Set Function Filter MeasureTheory Complex
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Carrier first; signal, band and all block tolerances afterwards; anchor
integer last and still arbitrarily large. No modeled next densities occur. -/
theorem eventually_reflected_anchor_state {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (a : ι → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ F.core i → ∀ s,
        |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ →
        d s = a i-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ ε ω κ : ℝ, 0 < ε → 0 < ω → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, g.c = c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
        0 < δ ∧ δ < κ ∧ 0 < L ∧ g.J₀ = neutralJitterReal cut L 0 ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε) ∧
          (∀ i, b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin) ∧
          (∀ i y, ‖d ((G.m i:ℝ)/n)-
            (a i.1-q ((G.m i:ℝ)*G.V y:UnitAddCircle))‖ < ω) ∧
          ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
            (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  filter_upwards [eventually_neutral_anchor_reflected_family F hi hmod hr] with c hc
  intro d q a hq b D margin τ hτ hroom ε ω κ hε hω hκ
  obtain ⟨hcp,δ,cut,L,χ,Δ,H,hδ,_hδ',hδκ,hL,hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc 1 (by norm_num) ε τ κ hε hτ hκ
  let g : PassageGeometryFamily F.V :=
    ⟨c,hcp,Δ,H,neutralJitter cut L 0,neutralJitterReal cut L 0,(fun _ => rfl),
      continuous_neutralJitter cut L 0,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (neutralJitterReal_smooth cut L 0).continuous
    (neutralJitterReal_periodic cut L 0)
  have hbudget := anchor_coefficient_budget (d := d) (D := D-margin) hq a hω R
  refine ⟨g,rfl,δ,cut,L,hδ,hδκ,hL,rfl,S,?_⟩
  filter_upwards [hgood,hbudget] with n hn hnω
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup,hreflect⟩ := hn
  have hloc (i : PassageOutputIndex (S n)) :
      d ((G.m i:ℝ)/n) = a i.1-q (((G.m i:ℝ)/(n:ℝ)):UnitAddCircle) ∧
      b+margin ≤ |(G.m i:ℝ)/n| ∧ |(G.m i:ℝ)/n| ≤ D-margin := by
    obtain ⟨x,hx,hx'⟩ := (hχ i.1).2.2.2.2 _
      (subset_tsupport _ ((hS n hnp i.1 _).mp i.2.property))
    rw [hGm]
    exact hroom i.1 x hx _ hx'
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,fun i => (hloc i).2,?_,hreflect⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i y
    rw [hGV]
    exact hnω.2 (G.m i) i.1 (neutralJitterReal cut L 0 y) (hloc i).2.2 (hRJ y) (hloc i).1

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The carrier precedes the block signal and every block accuracy requirement.
The output retains the literal actual geometry and finite amplitudes. -/
theorem eventually_colored_reflected_anchor {m : ℕ} (C : ColoredState (Fin m))
    {τR : Fin m → Fin m} (hrC : C.Reflection τR) :
    ∀ᶠ c : ℕ in atTop,
      ∀ (d : ℝ → ℂ) (q : UnitAddCircle → ℂ) (tags : Fin m → ℂ), Continuous q →
      ∀ b D margin τ : ℝ, 0 < τ →
      (∀ i x, x ∈ C.packets.core i → ∀ s,
        |s-(C.packets.m i:ℝ)*((c:ℝ)+C.packets.V x)| < τ →
        d s = tags (C.color i)-q (s:UnitAddCircle) ∧ b+margin ≤ |s| ∧ |s| ≤ D-margin) →
      ∀ ε e ω κ : ℝ, 0 < ε → 0 < e → 0 < ω → 0 < κ →
      ∀ᶠ n : ℕ in atTop, ∃ s : ColoredAnchor C n,
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
  intro d q tags hq b D margin τ hτ hroom ε e ω κ hε he hω hκ
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
  filter_upwards [hready] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herror,hband,hmatch,τG,hτG,hrG,hgoodG⟩ := hn
  let s : ColoredAnchor C n := ⟨g,S n,hnp,G,hGi,hGmod,hGV,hGm⟩
  refine ⟨s,hgc,⟨δ,cut,L,hδ,hδκ,hL,hgJ⟩,?_,?_,hband,?_,⟨τG,hrG,?_⟩,⟨δ,hδ,hδκ,hgoodG⟩⟩
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
theorem actual_reflected_block_of_center {m : ℕ} (C : ColoredState (Fin m))
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
      ‖blockTagMean C.density tags z-q z‖^2 ∂phaseHaar) ≤ delta) :
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
            ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ := by
  classical
  obtain ⟨τ,hr,hτ⟩ := hrC
  have hmr := hr.index
  have hcore i : C.packets.core i ⊆ C.packets.core (τ i) := by rw [hr.core]
  have htr i : tags (C.color (τ i)) = conj (tags (C.color i)) := by rw [hτ,htrR]
  obtain ⟨c,hsep,hanchor⟩ := ((eventually_integral_speed_separation C.packets.m
    C.packets.periodic.lift C.packets.nonzero C.packets.speed_continuous).and
    (eventually_colored_reflected_anchor C ⟨τ,hr,hτ⟩)).exists
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
  obtain ⟨P,γ₀,_hP,_hPD,hγ₀,hsignal⟩ := exists_concrete_colored_reflected_signal hb hbD hds hdcompact hdr hd0 hdsupport
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
    (show 0 < ε/4 by positivity) τR hκ
  have hanchorReady := hanchor d q tags hq b D μ t ht
    (fun i x hx s hs => hroom i _ ⟨x,hx,rfl⟩ s hs)
    (ε/4) e ω κ (by positivity) he hω hκ
  obtain ⟨N,s,_hsc,hjitter,hphysical,hclose,hband,hmatch,hrAnchor,_hgoodAnchor⟩ := hanchorReady.exists
  obtain ⟨L,hL,E,α,hpath,hmovement,hsqrt,hpred,hrE,hgoodE⟩ := hblock s.output hrAnchor hclose.le μ hμ hband hmatch
  refine ⟨n,ell,hn,hell,hells,hn0,hn1,N,s,hjitter,L,hL,E,α,hpath,?_,hsqrt,hpred,hrE,hgoodE⟩
  intro r
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

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- An actual finite block, centered using its ACTUAL input packet densities.
The finite chain contains the anchor and every signal/refresh pair. -/
structure ActualColoredBlock {m : ℕ} (C E : ColoredState (Fin m))
    (β : Equiv.Perm TripleTorus) (D : UnitAddCircle → ℂ) : Prop where
  witness : ∃ n : ℕ, ∃ ell : ℝ, 0 < n ∧ 0 < ell ∧
    ∃ q : UnitAddCircle → ℂ, Continuous q ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)) ∧
      (∀ z, q (-z) = conj (q z)) ∧
      ∃ N : ℕ, ∃ s : ColoredAnchor C N, ∃ L : Fin n → ℤ,
      ∃ α : Equiv.Perm TripleTorus, ColoredPath s.output L E α ∧
        β = s.chart.trans α ∧ D = blockDiagonalEstimator q ell L

namespace ActualColoredBlock
variable {m : ℕ} {C E : ColoredState (Fin m)} {β : Equiv.Perm TripleTorus}
    {D : UnitAddCircle → ℂ} (h : ActualColoredBlock C E β D)
include h
lemma continuous : Continuous β := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,_,hp,rfl,_⟩ := h.witness
  exact hp.continuous.comp s.chart_continuous
lemma preserves : MeasurePreserving β tripleVolume tripleVolume := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,_,hp,rfl,_⟩ := h.witness
  exact hp.preserves.comp s.chart_preserves
lemma physicalError_eq (f g : TripleTorus → ℂ) :
    physicalError (f ∘ β) (g ∘ β) = physicalError f g := by
  obtain ⟨_,_,_,_,_,_,_,_,_,s,_,α,hp,rfl,_⟩ := h.witness
  change physicalError ((f ∘ α) ∘ passageChart (s.geometry.H _))
    ((g ∘ α) ∘ passageChart (s.geometry.H _)) = _
  rw [physicalError_chart (s.geometry.Hcontinuous _).measurable,hp.physicalError_eq]
lemma estimator_continuous : Continuous D := by
  obtain ⟨_,_,_,_,_,hq,_,_,_,_,_,_,_,_,rfl⟩ := h.witness
  exact continuous_blockPhaseEstimator_diagonal hq _ _
end ActualColoredBlock

theorem actual_reflected_block {m : ℕ} (C : ColoredState (Fin m))
    (τR : Fin m → Fin m) (hτR : Involutive τR) (hrC : C.Reflection τR)
    (tags : Fin m → ℂ) (htags : ∀ r, ‖tags r‖ ≤ 1)
    (htrR : ∀ r, tags (τR r) = conj (tags r))
    {A : UnitAddCircle → ℂ} (hA : Continuous A) (k : ℕ) {delta nu ε κ : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1/100) (hnu : 0 < nu) (hε : 0 < ε) (hκ : 0 < κ)
    (hmass : (∫ z, blockTotal C.density z ∂phaseHaar) ≤ 2) :
    ∃ E : ColoredState (Fin m), ∃ β : Equiv.Perm TripleTorus, ∃ D : UnitAddCircle → ℂ,
      ActualColoredBlock C E β D ∧
      (∀ r, physicalError (C.vector r) (E.vector r ∘ β) < ε) ∧
      ((∫ z, Real.sqrt (blockTotal C.density z) ∂phaseHaar)-300*delta^2-nu ≤
        ∫ z, Real.sqrt (blockTotal E.density z) ∂phaseHaar) ∧
      ((∑ r, ∫ z, E.density r z*‖A z+D z-((k:ℂ)+1)*tags r‖^2 ∂phaseHaar) ≤
        (∫ z, blockPreviousError C.density tags A k z ∂phaseHaar)+4/delta+nu) ∧
      E.Reflection τR ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ E.packets.GoodArc δ := by
  obtain ⟨q,hq,hqs,hqB,hqr,hcenter⟩ := C.exists_center hrC hτR htags htrR hd
  obtain ⟨n,ell,hn,hell,_hells,_hn0,_hn1,N,s,_hjitter,L,_hL,E,α,hpath,hphys,hsqrt,hpred,hr,hgood⟩ :=
    actual_reflected_block_of_center C τR hrC tags htags htrR hq hqs hqr hqB hA k
      hd hd1 hnu hε hκ hmass hcenter.le
  exact ⟨E,s.chart.trans α,blockDiagonalEstimator q ell L,
    ⟨n,ell,hn,hell,q,hq,hqs,hqr,N,s,L,α,hpath,rfl,rfl⟩,
    hphys,hsqrt,hpred,hr,hgood⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

def physicalEnergy (f : TripleTorus → ℂ) : ℝ := ∫ x, ‖f x‖^2 ∂tripleVolume
lemma physicalEnergy_nonneg (f : TripleTorus → ℂ) : 0 ≤ physicalEnergy f :=
  integral_nonneg (fun _ => sq_nonneg _)
lemma physicalEnergy_integrable {f : TripleTorus → ℂ} (hf : Continuous f) :
    Integrable (fun x => ‖f x‖^2) tripleVolume :=
  (hf.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma scalar_energy_comparison {a b t : ℝ} (ht : 0 < t) :
    (a+b)^2 ≤ (1+t)*a^2+(1+1/t)*b^2 := by
  have he : ((1+t)*a^2+(1+1/t)*b^2-(a+b)^2)*t = (t*a-b)^2 := by
    field_simp
    ring
  have hh := sq_nonneg (t*a-b)
  nlinarith

lemma physicalEnergy_comparison {f g : TripleTorus → ℂ}
    (hf : Continuous f) (hg : Continuous g) {t : ℝ} (ht : 0 < t) :
    physicalEnergy g ≤ (1+t)*physicalEnergy f+(1+1/t)*physicalError f g := by
  have hp x : ‖g x‖^2 ≤ (1+t)*‖f x‖^2+(1+1/t)*‖f x-g x‖^2 := by
    calc
      _ ≤ (‖f x‖+‖f x-g x‖)^2 := by
        gcongr
        simpa only [dist_eq_norm,sub_zero,norm_sub_rev,add_comm] using dist_triangle (g x) (f x) 0
      _ ≤ _ := scalar_energy_comparison ht
  unfold physicalEnergy physicalError
  calc
    _ ≤ ∫ x, (1+t)*‖f x‖^2+(1+1/t)*‖f x-g x‖^2 ∂tripleVolume :=
      integral_mono (physicalEnergy_integrable hg)
        (((physicalEnergy_integrable hf).const_mul _).add ((physicalError_integrable hf hg).const_mul _)) hp
    _ = _ := by
      rw [integral_add ((physicalEnergy_integrable hf).const_mul _)
        ((physicalError_integrable hf hg).const_mul _),integral_const_mul,integral_const_mul]

lemma exists_physical_mass_tolerance {f : TripleTorus → ℂ} (hf : Continuous f)
    (hm : physicalEnergy f < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : TripleTorus → ℂ, Continuous g →
      physicalError f g < ε → physicalEnergy g < 2 := by
  let M := physicalEnergy f
  have hM : 0 ≤ M := physicalEnergy_nonneg f
  let t := (2-M)/(2*(M+1))
  have ht : 0 < t := div_pos (sub_pos.mpr hm) (by positivity)
  have htM : t*(2*(M+1)) = 2-M := div_mul_cancel₀ _ (by positivity)
  have hgap : 0 < 2-(1+t)*M := by nlinarith
  let ε := (2-(1+t)*M)/(2*(1+1/t))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have heq : ε*(2*(1+1/t)) = 2-(1+t)*M := div_mul_cancel₀ _ (by positivity)
  refine ⟨ε,hε,?_⟩
  intro g hg he
  have hc := physicalEnergy_comparison hf hg ht
  have hmul : (1+1/t)*physicalError f g < (1+1/t)*ε :=
    mul_lt_mul_of_pos_left he (by positivity)
  dsimp only [M] at *
  nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma ActualColoredBlock.physicalEnergy_eq {m : ℕ} {C E : ColoredState (Fin m)}
    {β : Equiv.Perm TripleTorus} {D : UnitAddCircle → ℂ}
    (h : ActualColoredBlock C E β D) (f : TripleTorus → ℂ) :
    physicalEnergy (f ∘ β) = physicalEnergy f := by
  have he := h.physicalError_eq (fun _ => 0) f
  simpa [physicalError,physicalEnergy,Function.comp_def] using he

lemma ColoredState.mass_transport_tolerance {m : ℕ} (C : ColoredState (Fin m))
    (hm : (∫ z, blockTotal C.density z ∂phaseHaar) < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : ColoredState (Fin m)) (β : Equiv.Perm TripleTorus)
      (D : UnitAddCircle → ℂ), ActualColoredBlock C E β D →
      (∀ r, physicalError (C.vector r) (E.vector r ∘ β) < ε) →
      (∫ z, blockTotal E.density z ∂phaseHaar) < 2 := by
  rw [C.total_mass_energy] at hm
  obtain ⟨η,hη,hclose⟩ := exists_physical_mass_tolerance C.totalVector_continuous hm
  let ε : ℝ := η/((m:ℝ)+1)^2
  have hm1 : 0 < (m:ℝ)+1 := by positivity
  have hε : 0 < ε := div_pos hη (sq_pos_of_pos hm1)
  have heq : ε*((m:ℝ)+1)^2 = η := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hm1))
  refine ⟨ε,hε,?_⟩
  intro E β D hblock herrors
  have hs := physicalError_sum C.vector_continuous (fun r => (E.vector_continuous r).comp hblock.continuous)
  simp only [Fintype.card_fin] at hs
  have hsum : (∑ r, physicalError (C.vector r) (E.vector r ∘ β)) ≤ (m:ℝ)*ε := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun r _ => (herrors r).le)
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hsmall : (m:ℝ)*((m:ℝ)*ε) < η := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have herr : physicalError C.totalVector (E.totalVector ∘ β) < η :=
    hs.trans_lt (hmul.trans_lt hsmall)
  have henergy := hclose _ (E.totalVector_continuous.comp hblock.continuous) herr
  rw [hblock.physicalEnergy_eq] at henergy
  rw [E.total_mass_energy]
  exact henergy

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma fourier_diagonal_smooth_lift (n : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => fourier 1 (n • (x:UnitAddCircle))) := by
  have he (x : ℝ) : fourier 1 (n • (x:UnitAddCircle)) = fourier n (x:UnitAddCircle) := by
    simp only [fourier_apply,one_zsmul]
  simp_rw [he,fourier_coe_apply]
  exact Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)

lemma blockDiagonalEstimator_smooth {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => q (x:UnitAddCircle)))
    (ell : ℝ) (L : Fin n → ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => blockDiagonalEstimator q ell L (x:UnitAddCircle)) := by
  unfold blockDiagonalEstimator blockPhaseEstimator
  exact hq.add (contDiff_const.mul (ContDiff.sum (fun i _ => fourier_diagonal_smooth_lift (L i))))
lemma blockDiagonalEstimator_reflection {n : ℕ} {q : UnitAddCircle → ℂ}
    (hq : ∀ z, q (-z) = conj (q z)) (ell : ℝ) (L : Fin n → ℤ)
    (z : UnitAddCircle) :
    blockDiagonalEstimator q ell L (-z) = conj (blockDiagonalEstimator q ell L z) := by
  have hf (x : UnitAddCircle) : fourier 1 (-x) = conj (fourier 1 x) := by
    simpa only [fourier_apply,zsmul_neg] using (fourier_neg' (n := 1) (x := x))
  unfold blockDiagonalEstimator blockPhaseEstimator
  simp only [hq,zsmul_neg,hf,map_add,map_mul,map_sum,map_inv₀,
    map_natCast,Complex.conj_ofReal]

namespace ActualColoredBlock
variable {m : ℕ} {C E : ColoredState (Fin m)} {β : Equiv.Perm TripleTorus}
    {D : UnitAddCircle → ℂ} (h : ActualColoredBlock C E β D)
include h
lemma estimator_smooth :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => D (x:UnitAddCircle)) := by
  obtain ⟨_,_,_,_,_,_,hqs,_,_,_,_,_,_,_,rfl⟩ := h.witness
  exact blockDiagonalEstimator_smooth hqs _ _
lemma estimator_reflection (z : UnitAddCircle) : D (-z) = conj (D z) := by
  obtain ⟨_,_,_,_,_,_,_,hqr,_,_,_,_,_,_,rfl⟩ := h.witness
  exact blockDiagonalEstimator_reflection hqr _ _ _
end ActualColoredBlock
end ThreeTorus
end
end

end OAI
