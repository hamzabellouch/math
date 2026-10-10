import Mathlib

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurePreserving_equiv_zpow (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (n : ℤ) :
    MeasurePreserving (σ.toEquiv ^ n) μ μ := by
  cases n with
  | ofNat n =>
      change MeasurePreserving (σ.toEquiv ^ (n : ℤ)) μ μ
      simpa only [zpow_natCast, Equiv.Perm.coe_pow, MeasurableEquiv.coe_toEquiv] using
        hσ.iterate n
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow]
      simpa only [Equiv.Perm.coe_pow, Equiv.Perm.inv_def,
        MeasurableEquiv.coe_toEquiv_symm] using
        (hσ.symm σ).iterate (n + 1)

theorem ae_forall_equiv_zpow (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ n : ℤ, P ((σ.toEquiv ^ n) x) := by
  exact ae_all_iff.mpr fun n =>
    (measurePreserving_equiv_zpow σ hσ n).quasiMeasurePreserving.ae hP

theorem exists_invariant_conull_subset_equiv (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) {s : Set X} (hs : MeasurableSet s)
    (hae : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ μ tᶜ = 0 ∧
      ∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' t = t := by
  let t : Set X := ⋂ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s
  have htm : MeasurableSet t := MeasurableSet.iInter fun n =>
    hs.preimage (measurePreserving_equiv_zpow σ hσ n).measurable
  have ht : ∀ᵐ x ∂μ, x ∈ t := by
    simpa only [t, mem_iInter, mem_preimage] using ae_forall_equiv_zpow σ hσ hae
  refine ⟨t, htm, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 := Set.mem_iInter.mp hx 0
    simpa only [mem_preimage, zpow_zero, Equiv.Perm.one_apply] using hx0
  · exact mem_ae_iff.mp ht
  · intro n
    ext x
    simp only [t, mem_preimage, mem_iInter]
    constructor
    · intro hx k
      have h := hx (k - n)
      simpa only [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel] using h
    · intro hx k
      simpa only [← Equiv.Perm.mul_apply, ← zpow_add] using hx (k + n)

theorem exists_invariant_exponential_coboundary_domain (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (g gstar b : X → ℝ)
    (hg : Measurable g) (hgs : Measurable gstar) (hb : Measurable b)
    (heq : g =ᵐ[μ] fun x => gstar x + 1 + b (σ x) - b x) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      (∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (b ((σ.toEquiv ^ (k + 1)) x)) *
            Real.exp (-g ((σ.toEquiv ^ k) x)) =
          Real.exp (-1) * Real.exp (-gstar ((σ.toEquiv ^ k) x)) *
            Real.exp (b ((σ.toEquiv ^ k) x)) := by
  have hmeas : MeasurableSet {x | g x = gstar x + 1 + b (σ x) - b x} :=
    measurableSet_eq_fun hg (((hgs.add_const 1).add (hb.comp σ.measurable)).sub hb)
  obtain ⟨s, hsm, hsub, hnull, hinv⟩ := exists_invariant_conull_subset_equiv σ hσ hmeas heq
  refine ⟨s, hsm, hnull, hinv, ?_⟩
  intro x hx k
  have hxk : (σ.toEquiv ^ k) x ∈ s := by
    change x ∈ (σ.toEquiv ^ k) ⁻¹' s
    rwa [hinv k]
  have hrel := hsub hxk
  have hnext : (σ.toEquiv ^ (k + 1)) x = σ ((σ.toEquiv ^ k) x) := by
    rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rfl
  rw [hnext, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  change g ((σ.toEquiv ^ k) x) =
    gstar ((σ.toEquiv ^ k) x) + 1 + b (σ ((σ.toEquiv ^ k) x)) -
      b ((σ.toEquiv ^ k) x) at hrel
  linarith

theorem exists_invariant_weight_coboundary_domain (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (g gstar b f fstar : X → ℝ)
    (hg : Measurable g) (hgs : Measurable gstar) (hb : Measurable b)
    (hmf : Measurable f) (hmfs : Measurable fstar)
    (heq : g =ᵐ[μ] fun x => gstar x + 1 + b (σ x) - b x)
    (hf : f =ᵐ[μ] fun x => Real.exp (-g x))
    (hfs : fstar =ᵐ[μ] fun x => Real.exp (-gstar x)) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      (∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (b ((σ.toEquiv ^ (k + 1)) x)) * f ((σ.toEquiv ^ k) x) =
          Real.exp (-1) * fstar ((σ.toEquiv ^ k) x) *
            Real.exp (b ((σ.toEquiv ^ k) x)) := by
  obtain ⟨s₀, hs₀, hn₀, hi₀, hscalar⟩ :=
    exists_invariant_exponential_coboundary_domain σ hσ g gstar b hg hgs hb heq
  have hm : MeasurableSet {x | f x = Real.exp (-g x) ∧
      fstar x = Real.exp (-gstar x)} :=
    (measurableSet_eq_fun hmf (Real.continuous_exp.measurable.comp hg.neg)).inter
      (measurableSet_eq_fun hmfs (Real.continuous_exp.measurable.comp hgs.neg))
  obtain ⟨t, htm, hsub, htn, hti⟩ :=
    exists_invariant_conull_subset_equiv σ hσ hm (hf.and hfs)
  refine ⟨s₀ ∩ t, hs₀.inter htm, ?_, ?_, ?_⟩
  · rw [Set.compl_inter]
    exact measure_union_null hn₀ htn
  · intro n
    rw [Set.preimage_inter, hi₀ n, hti n]
  · intro x hx k
    have hxk : (σ.toEquiv ^ k) x ∈ t := by
      change x ∈ (σ.toEquiv ^ k) ⁻¹' t
      rw [hti k]
      exact hx.2
    obtain ⟨hfx, hfsx⟩ := hsub hxk
    rw [hfx, hfsx]
    exact hscalar x hx.1 k

end Invariant233

end OAI
