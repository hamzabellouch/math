import OAI.NumberTheory.DukePrimeDegree.Dynamics.SmallOrbitSection

namespace OAI

/-! # A complete orbit section is visited in the future almost everywhere

Finite measure turns the forward saturation of a set into an invariant
set modulo null sets. No ergodicity assumption is needed.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] in
lemma ae_future_visits_of_orbit_section (μ : Measure Y) [IsFiniteMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    {S A : Set Y} (hS : MeasurableSet S)
    (hcover : ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y) :
    ∀ᵐ x ∂μ, x ∈ A → ∀ M : ℕ, ∃ n : ℕ, M ≤ n ∧ (e^n) x ∈ S := by
  let U := ⋃ n : ℕ, (e^n) ⁻¹' S
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n =>
    hS.preimage (e^n).measurable
  have hpre : e ⁻¹' U ⊆ U := by
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨n+1,?_⟩
    simpa only [mem_preimage,pow_succ,Homeomorph.mul_apply] using hn
  have heq : e ⁻¹' U =ᵐ[μ] U := ae_eq_of_subset_of_measure_ge hpre
    (he.measure_preimage hU.nullMeasurableSet).symm.le
    (hU.preimage e.measurable).nullMeasurableSet (measure_ne_top μ U)
  have hnat (n : ℕ) : ∀ᵐ x ∂μ, (e^n) x ∈ U ↔ x ∈ U := by
    induction n with
    | zero => exact ae_of_all μ (fun _ => by simp)
    | succ n ih =>
      filter_upwards [he.quasiMeasurePreserving.ae ih,heq.mem_iff] with x hx heq
      simpa only [pow_succ,Homeomorph.mul_apply] using hx.trans heq
  have hinv : MeasurePreserving (e⁻¹ : Y ≃ₜ Y) μ μ :=
    MeasurePreserving.symm e.toMeasurableEquiv he
  have hint (k : ℤ) : ∀ᵐ x ∂μ, (e^k) x ∈ U ↔ x ∈ U := by
    cases k with
    | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hnat n
    | negSucc n =>
      have hi := (measurePreserving_homeomorph_pow μ e⁻¹ hinv (n+1)).quasiMeasurePreserving.ae
        (hnat (n+1))
      filter_upwards [hi] with x hx
      have hc : (e^(n+1)) ((e⁻¹^(n+1)) x)=x := by
        rw [←Homeomorph.mul_apply,inv_pow,mul_inv_cancel,Homeomorph.one_apply]
      rw [hc] at hx
      simpa only [zpow_negSucc,inv_pow] using hx.symm
  filter_upwards [ae_all_iff.mpr hint] with x hx hxA
  obtain ⟨y,hy,k,hk⟩ := hcover x hxA
  have hyU : y ∈ U := mem_iUnion.mpr ⟨0,by simpa using hy⟩
  have hxU : x ∈ U := (hx k).mp (hk.symm ▸ hyU)
  intro M
  have hMx : (e^M) x ∈ U := by
    simpa only [zpow_natCast] using (hx (M:ℤ)).mpr hxU
  obtain ⟨n,hn⟩ := mem_iUnion.mp hMx
  refine ⟨n+M,by omega,?_⟩
  simpa only [mem_preimage,pow_add,Homeomorph.mul_apply] using hn

end DukePrimeDegree

end

end OAI
