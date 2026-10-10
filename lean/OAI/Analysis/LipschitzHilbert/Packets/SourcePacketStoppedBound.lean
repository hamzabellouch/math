import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketPathProduct
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathCostBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedStop

namespace OAI

/-! The original stopped packet product has the source's uniform path
bound once its two reference residual norms have polynomial control. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_packet_stopped_bound
    (Cmarked Cunary q Cmass A_M : ℝ) (hAM : 0 < A_M)
    (hchoice : 4*(max Cmarked (Cunary+6)+3/2) ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ σ X : Type*) (κ : Type) [Fintype κ],
    ∀ (Kb : ℕ) (F : Type*) [NormedAddCommGroup F]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ), (∀ t ∈ tops, 0 ≤ precision t) →
      (∀ t x, 0 < weight t x) →
    ∀ (K : ℕ), 0 < K → ∀ (gap : ℕ → ℝ)
      (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a α μ : ℝ),
      (∀ k, 0 ≤ (phase k).re) → Real.sqrt L*μ = α-1 →
      (∀ z ∈ packets, assigned z ∈ tops) →
      (∀ z ∈ packets, g.eligible cutoff (precision (assigned z)) (stop z)) →
    ∀ (_hKb : 0 < Kb) (tag : Fin Kb) (top : τ), top ∈ tops →
    ∀ (x : X) (count H : ℕ), ShiftedBlocks.endpoint tag count ≤ H →
      (¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) →
    ∀ (marked : ℕ → Prop) (profile : ℕ → F) (Cex : ℝ),
      1 ≤ α → α ≤ Real.sqrt L → (α-1)/Real.sqrt L ≤ 1/12 → 0 ≤ Cex →
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let finish := firstMassStop n count (L^A_M)
    let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let level := ShiftedBlocks.endpoint tag
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let residual := fun j => g.packetResidual packets (fun z => slope (assigned z)) stop base
      transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let keep := fun j z => assigned z ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) (slope top))
    let U := fun j => g.packetResidual (packets.filter (keep j)) (fun z => slope (assigned z))
      stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let W := fun j => g.packetAmplitude (packets.filter fun z => ¬keep j z)
      (fun z => slope (assigned z)) stop base transition (level j) (g.index (level j) (slope top))
    let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
    Real.log (n 0) ≤ 3*L →
    (∀ j < count, marked j → L^A_M < n j) →
    (∀ j < finish, marked j → (1/4:ℝ) ≤ n j-n (j+1)) →
    (∑ j ∈ (Finset.range finish).filter marked, ‖residual j‖^2) ≤ (L^Cmarked)^2 →
    (∀ j < finish, n j^((α-1)/Real.sqrt L) ≤ Real.exp (Cmass*Real.sqrt L)) →
    finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤ (L^Cunary)^3 →
    (∀ j < finish, ¬marked j → n j-n (j+1) < 1 →
      ‖W j‖ ≤ (L^q*Real.exp (-L*Real.log L))*(n j-n (j+1))) →
    (∀ e f, e < f → f ≤ finish → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f, ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
        L^6*intervalOscillation profile H (level e) (level f)) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ L^A_M) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ L^A_M+1) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α (Real.sqrt L) (L^A_M) tag top count x ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, if marked j then
          g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
            value phase a (Real.sqrt L) μ tag top x j else 1 := by
  filter_upwards [eventually_source_path_cost_budget Cmarked Cunary q Cmass A_M hAM.le hchoice,
    (tendsto_rpow_atTop hAM).eventually_ge_atTop 4,eventually_ge_atTop (1:ℝ)]
    with L hbudget hM hL
  intro τ σ X κ _ Kb F _ g tops slope precision cutoff weight hp hw K hK gap packets assigned stop
    value phase a α μ hphase hrelation hassigned heligible hKb tag top htop x count H hH
    hterminal marked profile Cex hα hαp hμ hCex
  dsimp only
  let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
  let finish := firstMassStop n count (L^A_M)
  intro hlog hmarkActive hmarkDrop hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hroot : 1 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL0.le).mpr (by simpa using hL)
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from g.shiftedPathMass_terminal_zero tops slope precision cutoff
      weight tag top count hterminal x]
    exact Real.rpow_nonneg hL0.le _
  have hs := firstMassStop_spec n count (L^A_M) hnlast
  have hnanti : Antitone n := g.shiftedPathMass_antitone tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) hKb tag top htop x
  have hfinish : ShiftedBlocks.endpoint tag finish ≤ H :=
    ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone hs.1).trans hH
  have hprod := g.source_active_packet_prefix_product tops slope precision cutoff weight hp hw
    hK gap packets assigned stop value phase a α (Real.sqrt L) μ hphase hrelation hassigned
    heligible hKb tag top htop x finish H hfinish marked profile (1/4) (L^A_M)
    (L^Cmarked) (L^Cunary) (L^6) (L^q*Real.exp (-L*Real.log L))
    (Real.exp (Cmass*Real.sqrt L)) Cex hroot hα hαp (by norm_num) (by norm_num) hM hμ
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _) (by positivity)
    (by positivity) hCex hs.2.2 hmarkDrop hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have hcost := hbudget n finish
    ((Finset.range finish).filter fun j => ¬marked j ∧ n j-n (j+1) < 1)
    (Finset.filter_subset ..) hnanti (L^Cmarked) (L^Cunary)
    (L^q*Real.exp (-L*Real.log L)) (Real.exp (Cmass*Real.sqrt L))
    ((α-1)/Real.sqrt L) (Real.rpow_nonneg hL0.le _) le_rfl
    (Real.rpow_nonneg hL0.le _) le_rfl (by positivity) le_rfl (by positivity) le_rfl
    hμ hs.2.2 (g.shiftedPathMass_nonneg tops slope precision cutoff weight
      (fun t z => (hw t z).le) tag top x finish) hlog
  norm_num only at hprod
  let pred := fun j => g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
    packets assigned stop value phase a (Real.sqrt L) μ tag top x j
  have hpred : 0 ≤ ∏ j ∈ Finset.range finish, if marked j then pred j else 1 := by
    apply Finset.prod_nonneg
    intro j hj
    split_ifs
    · apply (g.sourceShiftedPathPrediction_pos tops slope precision cutoff weight hw
        K gap packets assigned stop value phase a (Real.sqrt L) μ tag top htop x j _).le
      exact g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x j
        (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (hM.trans (hs.2.2 j (Finset.mem_range.mp hj)).le)))
    · exact zero_le_one
  have hCpos : 0 < 1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1) := by positivity
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) K gap packets assigned stop value phase a α (Real.sqrt L)
    (L^A_M) (Real.rpow_nonneg hL0.le _) hKb tag top htop count hterminal x]
  apply hprod.trans
  rw [Real.exp_add,Real.exp_log hCpos]
  have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hCpos.le
  have hm := mul_le_mul_of_nonneg_right he hpred
  have hstop := source_marked_product_stop n pred marked count (L^A_M) hnlast hnanti hmarkActive
  calc
    _ ≤ (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        (∏ j ∈ Finset.range finish, if marked j then pred j else 1) := hm
    _ = _ := congrArg (fun z => (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*z) hstop

end LipschitzHilbert.AngularGrid

end

end OAI
