import OAI.Probability.SLE.Loewner.InitialInverseChart
import TauCeti.Analysis.Complex.Conformal.Montel.Basic

namespace OAI

/-! Compactness of the actual inverse charts of all initial subarcs.
The uniform bound is supplied by their common final capacity. -/
noncomputable section
open Set Filter Function Metric
open scoped Topology

namespace SLEExactGauge

lemma initialInverseChart_locallyBounded (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    TauCeti.IsLocallyBoundedOn (initialInverseChart p hi h0 hH) upperHalfPlane := by
  intro K hKH hK
  by_cases hne : K.Nonempty
  · obtain ⟨m,hm,hmin⟩ := compact_upperHalfPlane_min_height hK hKH hne
    obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
    let C := initialCapacity p hi h0 hH 1
    have hC : 0≤C := initialCapacity_nonneg p hi h0 hH 1
    refine ⟨R+C/m,fun t z hz => ?_⟩
    have hcap : initialCapacity p hi h0 hH t≤C :=
      initialCapacity_monotone p hi h0 hH (show t≤1 from le_top)
    have him : 0<z.im := hKH hz
    calc
      ‖initialInverseChart p hi h0 hH t z‖ ≤
          ‖initialInverseChart p hi h0 hH t z-z‖+‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ initialCapacity p hi h0 hH t/z.im+R :=
        add_le_add (initialInverseChart_displacement p hi h0 hH t (hKH hz)) (hR z hz)
      _ ≤ C/m+R := by
        have hb := (div_le_div_of_nonneg_right hcap him.le).trans
          (div_le_div_of_nonneg_left hC hm (hmin z hz))
        linarith
      _ = R+C/m := add_comm _ _
  · exact ⟨0,fun _ _ hz => False.elim (hne ⟨_,hz⟩)⟩

theorem initialInverseChart_subsequence (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : ℕ → unitInterval) :
    ∃ (φ : ℕ → ℕ) (F : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ F upperHalfPlane ∧
      TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t (φ n)))
        F atTop upperHalfPlane :=
  TauCeti.montel isOpen_upperHalfPlane
    (fun n => initialInverseChart_differentiableOn p hi h0 hH (t n))
    ((initialInverseChart_locallyBounded p hi h0 hH).comp t)

end SLEExactGauge

end

end OAI
