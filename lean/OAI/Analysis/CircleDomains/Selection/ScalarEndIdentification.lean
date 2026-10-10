import OAI.Analysis.CircleDomains.Selection.ScalarEndCaps

namespace OAI

/-! A single full-measure set satisfies all rational terminal bounds.
Shrinking the actual source caps then identifies the scalar on every
matched target end, even when those ends have positive total area. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem ae_rational_terminal_bounds (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain) :
    ∀ᵐ z ∂volume,
      (∀ n (j : Fin (R.limit.cores n).count) (b : ℚ), 0 ≤ (b : ℝ) →
        (∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b) →
        z ∈ closure (jordanInterior (R.limit.contours n j)) → W.scalar z ≤ b) ∧
      (∀ n (j : Fin (R.limit.cores n).count) (a : ℚ), (a : ℝ) ≤ 1 →
        (∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x)) →
        z ∈ closure (jordanInterior (R.limit.contours n j)) → (a : ℝ) ≤ W.scalar z) := by
  apply Filter.Eventually.and
  · apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro j
    apply ae_all_iff.2
    intro b
    by_cases hb : 0 ≤ (b : ℝ)
    · by_cases hs : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b
      · filter_upwards [W.le_on_terminal R hsch hG n j hb hs] with z hz
        exact fun _ _ => hz
      · exact Eventually.of_forall fun _ _ h => (hs h).elim
    · exact Eventually.of_forall fun _ h => (hb h).elim
  · apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro j
    apply ae_all_iff.2
    intro a
    by_cases ha : (a : ℝ) ≤ 1
    · by_cases hs : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk j)),
          (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x)
      · filter_upwards [W.ge_on_terminal R hsch hG n j ha hs] with z hz
        exact fun _ _ => hz
      · exact Eventually.of_forall fun _ _ h => (hs h).elim
    · exact Eventually.of_forall fun _ h => (ha h).elim

 theorem eq_on_all_matched_ends (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    ∀ᵐ z ∂volume, ∀ q : Sphere, ∀ E : RealTargetEnd R.limit q,
      z ∈ E.plane → W.scalar z = (Q i).quotient (π q) := by
  filter_upwards [W.ae_rational_terminal_bounds hsch hG] with z hz q E hzin
  let u : Sphere → ℝ := (Q i).quotient ∘ π
  have huc : Continuous u := hQ.comp hπ
  have huq : u q ∈ Icc 0 1 := (Q i).quotient_unit _
  have hucmp : ∀ p ∈ connectedComponentIn d.physicalDomainᶜ q, u p = u q := by
    intro p hp
    exact congrArg (Q i).quotient (hc q p hp)
  apply le_antisymm
  · by_contra hle
    have hlt : u q < W.scalar z := lt_of_not_ge hle
    obtain ⟨b, hbq, hbz⟩ := exists_rat_btwn hlt
    have hb0 : 0 ≤ (b : ℝ) := huq.1.trans hbq.le
    obtain ⟨n, hn⟩ := (E.eventually_source_values huc hucmp
      (a := -1) (by linarith [huq.1]) hbq).exists
    have hsrc : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk (E.address n))),
        (x : Sphere) ∈ d.physicalDomain → (Q i).physical (Complex.equivRealProdCLM x) < b := by
      intro x hx hxG
      rw [(Q i).pullback x hxG]
      exact (hn (x : Sphere) ⟨x, hx, rfl⟩).2
    have hle := hz.1 n (E.address n) b hb0 hsrc (subset_closure (E.plane_inside n hzin))
    exact (not_lt_of_ge hle) hbz
  · by_contra hle
    have hlt : W.scalar z < u q := lt_of_not_ge hle
    obtain ⟨a, hza, haq⟩ := exists_rat_btwn hlt
    have ha1 : (a : ℝ) ≤ 1 := haq.le.trans huq.2
    obtain ⟨n, hn⟩ := (E.eventually_source_values huc hucmp haq
      (b := 2) (by linarith [huq.2])).exists
    have hsrc : ∀ x ∈ closure (jordanInterior ((R.limit.cores n).disk (E.address n))),
        (x : Sphere) ∈ d.physicalDomain → (a : ℝ) < (Q i).physical (Complex.equivRealProdCLM x) := by
      intro x hx hxG
      rw [(Q i).pullback x hxG]
      exact (hn (x : Sphere) ⟨x, hx, rfl⟩).1
    have hle := hz.2 n (E.address n) a ha1 hsrc (subset_closure (E.plane_inside n hzin))
    exact (not_lt_of_ge hle) hza

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
