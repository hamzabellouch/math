import OAI.Analysis.KadisonKastler.MinimalCyclicExpectation

namespace OAI

/-! # Contractive weak limits with a faithful trace vector

Pointwise weak compactness constructs a contractive ambient map. Strong
convergence on the given separating trace vector suffices to prove that its
restriction to the von Neumann algebra is the identity.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Simultaneous weak limits preserve linearity and contractivity. -/
theorem exists_contractive_weak_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (F : ι → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hF : ∀ i, ‖F i‖ ≤ 1) :
    ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), ‖E‖ ≤ 1 ∧
      ∀ T x y, Tendsto (fun i => inner ℂ y (F i T x)) (ω : Filter ι)
        (𝓝 (inner ℂ y (E T x))) := by
  have hb (i : ι) (T : H →L[ℂ] H) : ‖F i T‖ ≤ ‖T‖ := by
    simpa only [one_mul] using (F i).le_of_opNorm_le (hF i) T
  choose E hE ht using fun T : H →L[ℂ] H =>
    exists_weak_operator_ultralimit ω (fun i => F i T) ‖T‖ (norm_nonneg T)
      (fun i => hb i T)
  have hadd (S T : H →L[ℂ] H) : E (S + T) = E S + E T := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (S + T) x y)
    simpa only [map_add, add_apply, inner_add_right] using (ht S x y).add (ht T x y)
  have hsmul (c : ℂ) (T : H →L[ℂ] H) : E (c • T) = c • E T := by
    ext x
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • T) x y)
    simpa only [map_smul, smul_apply, inner_smul_right] using (ht T x y).const_mul c
  let L : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
    LinearMap.mkContinuous { toFun := E, map_add' := hadd, map_smul' := hsmul }
      1 (fun T => by
        change ‖E T‖ ≤ 1 * ‖T‖
        simpa only [one_mul] using hE T)
  exact ⟨L, L.opNorm_le_bound zero_le_one (fun T => by
    change ‖E T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using hE T), ht⟩

/-- A faithful vector identifies the limit map on the entire algebra. -/
theorem isInjective_of_trace_approximations {M : VonNeumannAlgebra H}
    (τ : TracialRepresentation M)
    (F : ℕ → (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hF : ∀ n, ‖F n‖ ≤ 1) (hmem : ∀ n T, F n T ∈ M)
    (hfix : ∀ a : Algebra M, Tendsto (fun n => F n a.val τ.vector) atTop
      (𝓝 (a.val τ.vector))) : IsInjective M := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨E,hE,ht⟩ := exists_contractive_weak_ultralimit ω F hF
  have hEM (T : H →L[ℂ] H) : E T ∈ M :=
    weak_operator_limit_mem M (fun n => ⟨F n T,hmem n T⟩) (E T) (ht T)
  refine ⟨E,hE,hEM,?_⟩
  intro T hT
  let a : Algebra M := ⟨T,hT⟩
  have hvec : E T τ.vector = T τ.vector := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht T τ.vector y)
    exact ((continuous_const.inner continuous_id).tendsto _).comp
      ((hfix a).mono_left (Ultrafilter.of_le atTop))
  have hz : (⟨E T,hEM T⟩ : Algebra M) - a = 0 := τ.separating _ (by
    change E T τ.vector - T τ.vector = 0
    exact sub_eq_zero.mpr hvec)
  exact congrArg Subtype.val (sub_eq_zero.mp hz)

end

end KadisonKastler

end OAI
