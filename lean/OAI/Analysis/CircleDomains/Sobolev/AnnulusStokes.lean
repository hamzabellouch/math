import OAI.Analysis.CircleDomains.Topology.RoundCollarPeriod
import OAI.Analysis.CircleDomains.Selection.OffsetRegions

namespace OAI

/-! The zero-offset Stokes estimate on a finite circularly punctured
Jordan region. Actual small-collar real lifts supply the nonsingular
boundary data; the distinguished period is constructed on the annulus. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finite_annulus_stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, closedBall (c i) (r i)) ⊆ O)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (A : Fin n → ℝ) (hA : ∀ i ≠ b, 0 ≤ A i)
    (hcollars : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ,
      ∃ v : Fin n → ℝ → ℝ, ∀ i ≠ b,
        Continuous (v i) ∧
        (∀ t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i + ρ) t)) ∧
        v i 1 = v i 0 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i + ε) :
    |circleFormIntegral (fun z => infDist z (closedBall (c b) (r b))) u γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ∑ i ∈ Finset.univ.erase b, 2 * Real.pi * r i * A i := by
  classical
  obtain ⟨δG, hδG, hgeom⟩ := exists_common_round_hole_offset c r hr hd
    (jordanInterior_isOpen H) hin
  have hcircle (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) δG) (i : Fin n) (t : ℝ) :
      unitCircleParam (c i) (r i + ρ) t ∈ O := by
    obtain ⟨hinside, hdisj⟩ := hgeom ρ ⟨hρ.1, hρ.2.le⟩
    exact circle_boundary_mem_smooth_region H c (fun j => r j + ρ)
      (fun j => by linarith [hr j, hρ.1]) hdisj hinside
      ((offset_closed_region_subset H c r hρ.1).trans hsub) i t
  obtain ⟨vB, k, hB⟩ := exists_constant_period_round_collars hu.continuousOn (c b) (r b) hδG
    (fun ρ hρ => hcircle ρ hρ b)
  apply zero_offset_stokes_bound_of_period (Finset.univ.erase b) r A
    (fun i hi => hA i (Finset.mem_erase.mp hi).1) _ _ k
  intro ε hε
  obtain ⟨δC, hδC, hC⟩ := hcollars ε hε
  let ρ := min (ε / 2) (min (δG / 2) (δC / 2))
  have hρ : 0 < ρ := lt_min (half_pos hε) (lt_min (half_pos hδG) (half_pos hδC))
  have hρε : ρ ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hρG : ρ < δG :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hδG)
  have hρC : ρ < δC :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hδC)
  obtain ⟨v₀, hv₀⟩ := hC ρ ⟨hρ, hρC⟩
  let v : Fin n → ℝ → ℝ := fun i => if i = b then vB ρ else v₀ i
  have hv (i : Fin n) : Continuous (v i) := by
    by_cases hi : i = b
    · subst i
      simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).1
    · simpa only [v, ite_eq_right hi] using (hv₀ i hi).1
  have hvp (i : Fin n) (t : ℝ) :
      (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i + ρ) t) := by
    by_cases hi : i = b
    · subst i
      simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).2.1 t
    · simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.1 t
  have hvzero (i : Fin n) (hi : i ≠ b) : v i 1 = v i 0 := by
    simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.2.1
  have hvosc (i : Fin n) (hi : i ≠ b) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |v i t - v i 0| ≤ (fun j => A j + ε) i := by
    simpa only [v, ite_eq_right hi] using (hv₀ i hi).2.2.2 t ht
  have hvb : v b 1 - v b 0 = k := by
    simpa only [v, ite_eq_left rfl] using (hB ρ ⟨hρ, hρG⟩).2.2
  let Oρ := O ∩ (closedBall (c b) (r b))ᶜ
  have hOρ : IsOpen Oρ := hO.inter isClosed_closedBall.isOpen_compl
  have hsubρ : closure (jordanInterior H) \ ⋃ i, ball (c i) (r i + ρ) ⊆ Oρ := by
    intro z hz
    have hbase := offset_closed_region_subset H c r hρ hz
    exact ⟨hsub hbase, fun hm => hbase.2 (mem_iUnion.mpr ⟨b, hm⟩)⟩
  have hregion := offset_open_region_subset H c r hρ.le
  have henergyρ : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i + ρ))) :=
    MemLp.mono_measure (Measure.restrict_mono hregion le_rfl) henergy
  obtain ⟨hinside, hdisj⟩ := hgeom ρ ⟨hρ, hρG.le⟩
  have he := finite_offset_stokes_bound_with_period hgreen H γ hγ n c (fun i => r i + ρ)
    (fun i => by linarith [hr i]) hdisj hinside Oρ hOρ hsubρ
    (fun z => infDist z (closedBall (c b) (r b)))
    ((contDiffOn_infDist_closedBall (c b) (hr b)).mono inter_subset_right)
    (lipschitz_infDist_pt _) u (fun z hz => hu z hz.1) hL
    (fun z hz => hbounded hz.1) henergyρ b ρ hρ.le v hv hvp
    (fun t _ => infDist_closedBall_unitCircle_offset (c b) (hr b) hρ t) hvzero
    (fun i => A i + ε) hvosc
  rw [hvb] at he
  have hE := mul_le_mul_of_nonneg_left (circle_energy_mono hregion u henergy)
    (mul_nonneg (Real.sqrt_nonneg Real.pi) hL)
  refine ⟨ρ, hρ, hρε, ?_⟩
  linarith

end CircleDomainRigidity

end

end OAI
