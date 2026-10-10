import OAI.Probability.DilutedSpin.RegularCovarianceLimit

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance regularCovarianceConvergenceDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

lemma grid_inverse_tendsto : Tendsto (fun L : ℕ => ((L+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)

lemma eventually_large_grid {η : ℝ} (hη : 0<η) :
    ∀ᶠ L : ℕ in atTop, 4<η*((L+1:ℕ):ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (4/η)
  filter_upwards [eventually_ge_atTop n] with L hL
  have hc : (n:ℝ)≤((L+1:ℕ):ℝ) := by exact_mod_cast (show n≤L+1 by omega)
  have hd := (div_lt_iff₀ hη).mp (hn.trans_le hc)
  simpa only [mul_comm] using hd

/-- Structural, finite-topology closure of the covariance recursion. The
same physical selection is used for every child, with N taken to infinity
before the mesh is refined. -/
theorem physicalShapeLimsup_tendsto (M : Model p) (θB hB : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, ScheduledControl M θB hB L (Ns L) (us L))
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) :
    Tendsto (fun L => physicalShapeLimsup M θB hB L (Ns L) (us L) S η) atTop (𝓝 0) := by
  induction S generalizing η with
  | leaf =>
    apply squeeze_zero (fun L => physicalShapeLimsup_nonneg M θB hB L (Ns L) (us L) .leaf η)
      (fun L => physicalShapeLimsup_leaf (hcontrol L) hη)
    simpa using grid_inverse_tendsto.div_const η
  | node k hk C ih =>
    let B := 4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ)
    let RHS (L : ℕ) := (4*((L+1:ℕ):ℝ)⁻¹+
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ))+
      B*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeLimsup M θB hB L (Ns L) (us L) (C j) (η/2))))/η
    have hsum : Tendsto (fun L => ∑ j, Real.sqrt
        (physicalShapeLimsup M θB hB L (Ns L) (us L) (C j) (η/2))) atTop (𝓝 0) := by
      have hh := tendsto_finsetSum (Finset.univ : Finset (Fin k)) (fun j _ =>
        (ih j (half_pos hη)).sqrt)
      simpa using hh
    have hshift : Tendsto (fun L : ℕ => Real.sqrt (nodeShiftBudget k C/(L+1:ℕ))) atTop (𝓝 0) := by
      have hh := (grid_inverse_tendsto.const_mul (nodeShiftBudget k C)).sqrt
      simpa [div_eq_mul_inv] using hh
    have hR : Tendsto RHS atTop (𝓝 0) := by
      have hh := (((grid_inverse_tendsto.const_mul 4).add
        (hshift.const_mul (2*nodeChargeConstant k hk C η))).add
        (((hsum.const_mul (k:ℝ)).sqrt).const_mul B)).div_const η
      simpa [RHS] using hh
    apply squeeze_zero' (Eventually.of_forall (fun L =>
      physicalShapeLimsup_nonneg M θB hB L (Ns L) (us L) (.node k hk C) η)) _ hR
    filter_upwards [eventually_large_grid hη] with L hL
    apply (le_div_iff₀ hη).mpr
    rw [mul_comm]
    exact physicalShapeLimsup_node (hcontrol L) k hk C hη hL

/-- A model-produced common controlling sequence for covariance concentration,
including the low cavity increment required by the lower comparison. No
concentration or selection hypothesis is added to the bounded model. -/
theorem physical_regular_covariance_selection (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ),
      (∀ L, StrictMono (Ns L)) ∧
      (∀ L n i, us L n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ L n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns L n) (us L n)≤
        liminf (pressure M) atTop+ε) ∧
      (∀ L, ScheduledControl M C H L (Ns L) (us L)) ∧
      (∀ S η, 0<η → Tendsto (fun L => physicalShapeLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0)) := by
  classical
  have hx (L : ℕ) := scheduled_joint_selection (L := L) M hC hH hθ hh hθi hhi hε
  choose Ns us hNs hus hinc hsingle hmatrix using hx
  have hcontrol (L : ℕ) : ScheduledControl M C H L (Ns L) (us L) :=
    ⟨hsingle L,hmatrix L⟩
  exact ⟨Ns,us,hNs,hus,hinc,hcontrol,fun S η hη =>
    physicalShapeLimsup_tendsto M C H Ns us hcontrol S hη⟩

end DilutedSpinGlass.UniversalDictionary

end

end OAI
