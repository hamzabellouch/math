import Mathlib
import OAI.Algebra.MarkedTensor.ReferenceWords
import OAI.Algebra.MarkedTensor.TripleProducts

namespace OAI

/-! Cubic nilpotence for reference holonomies and quotient ideals. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace BoundaryOnly.Holonomy
open Matrix
open scoped BigOperators commutatorElement
variable {R E : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def referenceOver (R : Type*) [CommRing R] [Algebra ℚ R]
    (c : shortWords) : SpecialLinearGroup (Fin 2) R :=
  SpecialLinearGroup.map (algebraMap ℚ R) (referenceRho c)

 

theorem cubic_nilpotence_reference [IsNoetherianRing R] [IsLocalRing R]
    (z : E → SpecialLinearGroup (Fin 2) R)
    (u : shortWords → SpecialLinearGroup (Fin 2) R)
    (hz : ∀ e, mat (z e)-1 ∈ (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hu : ∀ c, mat (u c)-mat (referenceOver R c) ∈
      (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hrel : ∀ e f g a b c,
      ⁅u a*z e*(u a)⁻¹,⁅u b*z f*(u b)⁻¹,u c*z g*(u c)⁻¹⁆⁆ = 1) :
    deviationIdeal z^3 = ⊥ := by
  apply cubic_nilpotence_local z u (referenceOver R) hz hu _ hrel
  exact adjoint_span_base_change (fun c : shortWords ↦ referenceRho c)
    finite_reference_adjoint_span

 

omit [Algebra ℚ R] in
lemma cube_sum_pullback {S T : Type*} [CommRing S] (r : Ideal S)
    (q : S →+* R) (hq : RingHom.ker q = r)
    (N : Ideal R) (hcube : N^3 = ⊥) (W : T → Ideal S)
    (hW : ∀ i, (W i).map q ≤ N) : (⨆ i, W i)^3 ≤ r := by
  have hm : (⨆ i, W i).map q ≤ N := by
    rw [Ideal.map_iSup]
    exact iSup_le hW
  have hp : ((⨆ i, W i)^3).map q ≤ ⊥ := by
    rw [Ideal.map_pow, ← hcube]
    exact pow_le_pow_left' hm 3
  have h := (Ideal.map_le_iff_le_comap).mp hp
  simpa only [← RingHom.ker_eq_comap_bot, hq] using h

 

omit [Algebra ℚ R] in
lemma slope_deviation_mem (z : E → SpecialLinearGroup (Fin 2) R)
    (e : E) (c : SpecialLinearGroup (Fin 2) R) (invert : Bool) :
    mat (c*(if invert then (z e)⁻¹ else z e)*c⁻¹)-1 ∈
      (deviationIdeal z).matrix (Fin 2) := by
  have h : mat (if invert then (z e)⁻¹ else z e)-1 ∈
      (deviationIdeal z).matrix (Fin 2) := by
    cases invert
    · exact deviation_mem z e
    · exact inv_deviation (deviation_mem z e)
  rw [conjugate_deviation]
  exact matrix_mul_right ((deviationIdeal z).matrix (Fin 2) |>.mul_mem_left _ h) _

end BoundaryOnly.Holonomy
namespace BoundaryOnly.Holonomy
open Matrix
open scoped commutatorElement
variable {R S E : Type*} [CommRing R] [CommRing S]

lemma map_deviation_entry (f : R →+* S) (v : SpecialLinearGroup (Fin 2) R)
    (i j : Fin 2) :
    (mat (SpecialLinearGroup.map f v)-1) i j = f ((mat v-1) i j) := by
  simp only [Matrix.sub_apply, map_sub]
  change f (mat v i j) - (1 : Matrix (Fin 2) (Fin 2) S) i j =
    f (mat v i j) - f ((1 : Matrix (Fin 2) (Fin 2) R) i j)
  simp [Matrix.one_apply]

 

theorem cubic_nilpotence_mod_ideal [Algebra ℚ R] [IsNoetherianRing R] [IsLocalRing R]
    (r : Ideal R) (hr : r ≤ IsLocalRing.maximalIdeal R)
    (z : E → SpecialLinearGroup (Fin 2) R)
    (u : shortWords → SpecialLinearGroup (Fin 2) R)
    (hz : ∀ e, mat (z e)-1 ∈ (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hu : ∀ c, mat (u c)-mat (referenceOver R c) ∈
      (IsLocalRing.maximalIdeal R).matrix (Fin 2))
    (hrel : ∀ e f g a b c,
      mat ⁅u a*z e*(u a)⁻¹,⁅u b*z f*(u b)⁻¹,u c*z g*(u c)⁻¹⁆⁆ - 1 ∈
        r.matrix (Fin 2)) :
    deviationIdeal z^3 ≤ r := by
  have hr' : r ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hr
  let : Nontrivial (R ⧸ r) := Ideal.Quotient.nontrivial_iff.mpr hr'
  let q : R →+* R ⧸ r := Ideal.Quotient.mk r
  let : IsLocalRing (R ⧸ r) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let z' : E → SpecialLinearGroup (Fin 2) (R ⧸ r) := fun e ↦ SpecialLinearGroup.map q (z e)
  let u' : shortWords → SpecialLinearGroup (Fin 2) (R ⧸ r) := fun c ↦ SpecialLinearGroup.map q (u c)
  have hm {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
      q x ∈ IsLocalRing.maximalIdeal (R ⧸ r) :=
    IsLocalRing.map_maximalIdeal_le q (Ideal.mem_map_of_mem q hx)
  have hz' (e) : mat (z' e)-1 ∈ (IsLocalRing.maximalIdeal (R ⧸ r)).matrix (Fin 2) := by
    intro i j
    rw [show z' e = SpecialLinearGroup.map q (z e) from rfl, map_deviation_entry]
    exact hm (hz e i j)
  have href (c) : referenceOver (R ⧸ r) c = SpecialLinearGroup.map q (referenceOver R c) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  have hu' (c) : mat (u' c)-mat (referenceOver (R ⧸ r) c) ∈
      (IsLocalRing.maximalIdeal (R ⧸ r)).matrix (Fin 2) := by
    intro i j
    rw [href]
    change q (mat (u c) i j) - q (mat (referenceOver R c) i j) ∈ _
    rw [← map_sub]
    exact hm (hu c i j)
  have hrel' (e f g a b c) :
      ⁅u' a*z' e*(u' a)⁻¹,⁅u' b*z' f*(u' b)⁻¹,u' c*z' g*(u' c)⁻¹⁆⁆ = 1 := by
    have hh : SpecialLinearGroup.map q
        ⁅u a*z e*(u a)⁻¹,⁅u b*z f*(u b)⁻¹,u c*z g*(u c)⁻¹⁆⁆ = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      apply sub_eq_zero.mp
      change (mat (SpecialLinearGroup.map q _)-1) i j = 0
      rw [map_deviation_entry]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel e f g a b c i j)
    simpa only [map_commutatorElement, map_mul, map_inv] using hh
  have hc := cubic_nilpotence_reference z' u' hz' hu' hrel'
  have hd : (deviationIdeal z).map q ≤ deviationIdeal z' := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro x ⟨⟨e,i,j⟩,rfl⟩
    change q ((mat (z e)-1) i j) ∈ deviationIdeal z'
    rw [← map_deviation_entry]
    exact deviation_mem z' e i j
  have hpow : ((deviationIdeal z)^3).map q ≤ ⊥ := by
    rw [Ideal.map_pow, ← hc]
    exact pow_le_pow_left' hd 3
  simpa only [← RingHom.ker_eq_comap_bot, q, Ideal.mk_ker] using
    (Ideal.map_le_iff_le_comap.mp hpow)
end BoundaryOnly.Holonomy
end

end OAI
