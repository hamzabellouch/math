import Mathlib
import OAI.Analysis.HardSphere.Paths.Admissible
import OAI.Analysis.HardSphere.Allocation.PhysicalGroupComparison

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma physical_lattice_bad_joint {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (μ : Measure (PhysicalDatum N K M G L)) (p : ℝ≥0∞)
    (hb : ∀A : Finset (Fin 3→Fin K),μ {d | A⊆datumBad hL g m t r R C S u d} ≤ p^A.card)
    (A : Finset (DiscreteTorus K)) :
    μ {d | A⊆latticeDatumBad hL g m t r R C S u d} ≤ p^A.card := by
  have he : {d : PhysicalDatum N K M G L | A⊆latticeDatumBad hL g m t r R C S u d}=
      {d | A.image siteIndex⊆datumBad hL g m t r R C S u d} := by
    ext d
    constructor
    · intro hh v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_latticeDatumBad hL g m t r R C S u d w).mp (hh hw)
    · intro hh v hv
      exact (mem_latticeDatumBad hL g m t r R C S u d v).mpr
        (hh (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  rw [he]
  have hinj : Function.Injective (siteIndex : DiscreteTorus K→Fin 3→Fin K) :=
    Function.LeftInverse.injective indexSite_siteIndex
  simpa only [Finset.card_image_of_injective _ hinj] using hb (A.image siteIndex)

theorem physical_path_comparison :
    ∃p₀ κ : ℝ, 0 < p₀ ∧ 0 < κ ∧ ∃K₀ : ℕ,
    ∀K : ℕ,K₀ ≤ K → ∀_ : NeZero K,
    ∀{N M G : ℕ} {L : Length},∀hL : L.val=(K:ℝ),1 ≤ K → 50 < L.val →
    ∀{ψ : Jet (N+1) L} {r : ℝ},IsGroundVector (N+1) L r ψ →
    ∀g : Fin G,∀m : ℕ,∀t R C S s₀ h : ℝ,∀u : Time,
    PhysicalScaleBounds m t r R C S s₀ h u →
    ∀p : ℝ,0 ≤ p → p ≤ p₀ →
    (∀A : Finset (Fin 3→Fin K),
      (physicalDatumLaw (M:=M) g ψ m r R C S s₀ (2*t) u)
        {d | A⊆datumBad hL g m t r R C S u d} ≤ (ENNReal.ofReal p)^A.card) →
    0 < M → ∀δ B : ℝ,0 < δ → 1 ≤ B → routeDensityBound t ≤ ENNReal.ofReal B →
    2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ →
    ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1 →
    ∀x y : DiscreteTorus K,currentAdmissiblePair x y →
    ∃σ : Measure (Torus L×Torus L×Configuration N L),IsFiniteMeasure σ ∧
      (1/2:ℝ≥0∞) ≤ σ univ ∧
      ∀b,
        let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
        IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
          (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ 2*B := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,H⟩ := HardSphere.DyadicSkeleton.current_good_paths 30
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst N M G L hL h1 h50 ψ r hψ g m t R C S s₀ h u hs p hp hpp hbad hM δ B hδ hB hBt hk hsmall x y hxy
  have := physicalDatumLaw_probability (K:=K) (M:=M) g hψ m R C S s₀ (2*t) (by linarith [hs.time_pos]) u
  obtain ⟨E,hE,hm,ν,hi,hgood,henc⟩ := (H K hK inst).2
    (physicalDatumLaw (K:=K) (M:=M) g ψ m r R C S s₀ (2*t) u) inferInstance
    (latticeDatumBad hL g m t r R C S u) (latticeDatumBad_measurable hL g m t r R C S u)
    p hp hpp (physical_lattice_bad_joint hL g m t r R C S u _ _ hbad) x y hxy
  have := hi
  have hne : x≠y := by
    intro he
    obtain ⟨n,hl,hu,d,hd,hy⟩ := hxy
    have hz := congrArg (fun z : DiscreteTorus K ↦ z 0) hy
    rw [←he] at hz
    simp only [Pi.add_apply,Matrix.cons_val_zero] at hz
    have hn0 : (n:ZMod K)=0 := by exact add_left_cancel (hz.symm.trans (add_zero _).symm)
    have hvn := congrArg ZMod.val hn0
    simp only [ZMod.val_natCast,ZMod.val_zero] at hvn
    rw [Nat.mod_eq_of_lt (by have := NeZero.pos K; omega)] at hvn
    have := NeZero.pos K
    omega
  have hc : (∫⁻d in E,∫⁻q,∫⁻q',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 q q':ℝ))) ∂ν d ∂ν d
      ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal (2:ℝ) := by
    simpa only [lintegral_indicator hE,ENNReal.ofReal_ofNat] using henc
  obtain ⟨σ,hσ,hmass,hest⟩ := physical_group_common_comparison hL h1 h50 hψ g m t R C S s₀ h u hs
    hne E hE ν hgood hM δ B κ 2 hδ hB (by norm_num) hBt hk hsmall hc
  exact ⟨σ,hσ,hmass ▸ hm,fun b ↦ by simpa only [mul_comm B 2] using hest b⟩

end HardSphere.Groups
end
end

end OAI
