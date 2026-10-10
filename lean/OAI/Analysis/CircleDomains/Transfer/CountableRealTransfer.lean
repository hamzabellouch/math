import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.RealTransferStage
import OAI.Analysis.CircleDomains.Selection.CountableMarks

namespace OAI

/-!
# Countably many real tests and mandatory marked ends

Every finite prefix is transferred by the actual assembled construction.
An increasing sequence of finite mandatory sets puts each fixed mark in
all sufficiently late models. Prescribed neighborhoods and source cores
are retained at each stage.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure CountableRealCoordinates {S : Type*}
    (G : Set Sphere) (π : Sphere → Sphere) (σ : S → Sphere) where
  source : Set Sphere
  source_open : IsOpen source
  coordinate : ℕ → Sphere → ℝ
  coordinate_continuous : ∀ l, ContinuousOn (coordinate l) source
  bound : ℕ → ℝ
  coordinate_bounded : ∀ l x, x ∈ source → |coordinate l x| ≤ bound l
  physical : ℕ → (ℝ × ℝ) → ℝ
  physical_measurable : ∀ l, Measurable (physical l)
  physical_smooth : ∀ l, ContDiffOn ℝ ∞ (physical l) (realChartDomain G)
  physical_energy : ∀ l, MemLp (planarGradient (physical l)) 2 (volume.restrict (realChartDomain G))
  source_map : ∀ z : ℂ, (z : Sphere) ∈ G → π z ∈ source
  pullback : ∀ l (z : ℂ), (z : Sphere) ∈ G → physical l (Complex.equivRealProdCLM z) = coordinate l (π z)
  labels_injective : Injective σ
  labels_dust : ∀ s, σ s ∈ π '' Gᶜ
  labels_closure : ∀ s, σ s ∈ closure source
  lower : ℕ → S → ℝ
  upper : ℕ → S → ℝ
  width_nonneg : ∀ l s, 0 ≤ upper l s - lower l s
  width_summable : ∀ l, Summable (fun s => (upper l s - lower l s) ^ 2)
  band : ∀ l s, {t : ℝ | (σ s, t) ∈ intervalFiberHull (clusterGraph source (coordinate l))} =
    Icc (lower l s) (upper l s)
  free_trace : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
    ∃ v : ℝ, {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph source (coordinate l))} = {v}

def CountableRealCoordinates.NaturalCompatibility {S : Type*}
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) : Prop :=
  ∀ (j n : ℕ) (labels : Fin n → ℕ), (∀ i, labels i < j) →
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure ((π '' Gᶜ) \ range σ) (circleBandGraph d.source (d.coordinate j))
        (fun k => circleBandGraph d.source (d.coordinate k)) labels) = 0

abbrev CountableRealCoordinates.Stage {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (n : ℕ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε : ℝ) :=
  RealTransferStage G π σ (fun l : Fin (n + 1) => d.physical l)
    (fun l => d.lower l) (fun l => d.upper l) Flag O K₀ ε

theorem CountableRealCoordinates.nonempty_stage
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {π : Sphere → Sphere} (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {S : Type*} [Countable S] {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (hcompat : d.NaturalCompatibility)
    (n : ℕ) (Flag : Set S) (hFlag : Flag.Finite)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (d.Stage n Flag O K₀ ε) := by
  apply exists_real_transfer_stage hsard hsch hcompact hfinite hG hinf
    π hπ hclosed hsurj hr hTD hK₀ hK₀G (Nat.succ_pos n)
    (fun l : Fin (n + 1) => d.physical l) (fun l => d.physical_measurable l)
    (fun l => d.physical_smooth l) (fun l => d.physical_energy l)
    σ d.labels_injective d.labels_dust d.source d.source_open
    (fun l => d.coordinate l) (fun l => d.coordinate_continuous l) (fun l => d.bound l)
    (fun l => d.coordinate_bounded l) d.source_map (fun l => d.pullback l)
    d.labels_closure (fun l => d.lower l) (fun l => d.upper l)
    (fun l => d.width_nonneg l) (fun l => d.width_summable l) (fun l => d.band l)
    Flag hFlag (fun x hx hfree l => d.free_trace x hx hfree l) ?_ O hO hε zero_lt_one 0
  intro j m labels hlabels
  exact hcompat j m (fun i => labels i) hlabels

theorem exists_countable_real_transfer
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {π : Sphere → Sphere} (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {S : Type*} [Countable S] {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (hcompat : d.NaturalCompatibility)
    (K₀ : ℕ → Set (ℝ × ℝ)) (hK₀ : ∀ n, IsClosed (K₀ n))
    (hK₀G : ∀ n, K₀ n ⊆ realChartDomain G)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ Flag : ℕ → Set S, (∀ n, (Flag n).Finite) ∧ Monotone Flag ∧
      (∀ n, Nonempty S → (Flag n).Nonempty) ∧
      ∃ M : ∀ n, d.Stage n (Flag n) (O n) (K₀ n) (ε n),
        ∀ s, ∀ᶠ n in atTop, s ∈ (M n).indices := by
  classical
  obtain ⟨Flag, hfin, hmono, hne, hcover⟩ := exists_increasing_finite_marks_inhabited S
  let M (n : ℕ) : d.Stage n (Flag n) (O n) (K₀ n) (ε n) :=
    Classical.choice (d.nonempty_stage hsard hsch hcompact hfinite hG hinf hπ hclosed
      hsurj hr hTD hcompat n (Flag n) (hfin n) (O n) (hO n) (hK₀ n) (hK₀G n) (hε n))
  refine ⟨Flag, hfin, hmono, hne, M, ?_⟩
  intro s
  exact (hcover s).mono (fun n hn => (M n).flags hn)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
