import Mathlib
import OAI.Analysis.FreeWords.Bicommutant

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped InnerProductSpace ComplexOrder Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def bicommutantAlg (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)))

@[simp] theorem coe_bicommutantAlg (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantAlg S : Set (H →L[ℂ] H)) = Set.centralizer (Set.centralizer (S : Set _)) := by
  simp only [bicommutantAlg, StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq, Set.union_self]

instance bicommutantAlg_closed (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (bicommutantAlg S : Set (H →L[ℂ] H)) := by
  rw [coe_bicommutantAlg]
  exact Set.isClosed_centralizer _

@[instance_reducible] def biOrder (S : StarSubalgebra ℂ (H →L[ℂ] H)) : PartialOrder (bicommutantAlg S) :=
  CStarAlgebra.spectralOrder _

attribute [local instance] KKUltraTrace.biOrder

@[instance_reducible] def biLE (S : StarSubalgebra ℂ (H →L[ℂ] H)) : LE (bicommutantAlg S) :=
  (biOrder S).toLE

attribute [local instance] KKUltraTrace.biLE

@[instance_reducible] def biPreorder (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Preorder (bicommutantAlg S) :=
  (biOrder S).toPreorder

attribute [local instance] KKUltraTrace.biPreorder

theorem biSOR (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarOrderedRing (bicommutantAlg S) :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKUltraTrace.biSOR

theorem subset_bicommutantAlg (S : StarSubalgebra ℂ (H →L[ℂ] H)) : S ≤ bicommutantAlg S := by
  intro a ha
  change a ∈ (bicommutantAlg S : Set _)
  rw [coe_bicommutantAlg]
  exact Set.subset_centralizer_centralizer ha

theorem bicommutant_eval_closed (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : bicommutantAlg S) (n : ℕ) (ξ : Fin n → H) (Z : Set (Fin n → H))
    (hZ : IsClosed Z) (h : ∀ a ∈ S, (fun i => a (ξ i)) ∈ Z) :
    (fun i => T.1 (ξ i)) ∈ Z := by
  apply hZ.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hT : T.1 ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    have ht : T.1 ∈ (bicommutantAlg S : Set _) := T.2
    rwa [coe_bicommutantAlg] at ht
  obtain ⟨a, ha, hclose⟩ := UniversalStrongKK.bicommutant_strong_approximation S T.1 hT n ξ ε hε
  refine ⟨fun i => a (ξ i), h a ha, ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff hε).mpr
  intro i
  simpa only [Pi.sub_apply, norm_sub_rev, sub_apply] using hclose i

def bicommutantState (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) :
    bicommutantAlg S →ₚ[ℂ] ℂ where
  toFun x := ⟪Ω, x.1 Ω⟫_ℂ
  map_add' x y := by
    change ⟪Ω, x.1 Ω + y.1 Ω⟫_ℂ = _
    exact inner_add_right _ _ _
  map_smul' c x := by simp
  monotone' x y hxy := by
    obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
    apply sub_nonneg.mp
    change 0 ≤ ⟪Ω, y.1 Ω⟫_ℂ - ⟪Ω, x.1 Ω⟫_ℂ
    rw [← inner_sub_right]
    have he : y.1 Ω - x.1 Ω = v.1.adjoint (v.1 Ω) :=
      congrArg (fun z : bicommutantAlg S => z.1 Ω) hv
    rw [he, ContinuousLinearMap.adjoint_inner_right, ← inner_self_ofReal_re]
    exact Complex.zero_le_real.mpr (inner_self_nonneg (𝕜 := ℂ) (x := v.1 Ω))

@[simp] theorem bicommutantState_apply (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H)
    (x : bicommutantAlg S) : bicommutantState S Ω x = ⟪Ω, x.1 Ω⟫_ℂ := rfl

theorem trace_relation_extend (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H)
    (B : H →L[ℂ] H) (h : ∀ a ∈ S, ⟪Ω, (a*B) Ω⟫_ℂ = ⟪Ω, (B*a) Ω⟫_ℂ)
    (T : bicommutantAlg S) : ⟪Ω, (T.1*B) Ω⟫_ℂ = ⟪Ω, (B*T.1) Ω⟫_ℂ := by
  have hz := bicommutant_eval_closed S T 2 ![B Ω, Ω]
    {z | ⟪Ω, z 0⟫_ℂ = ⟪Ω, B (z 1)⟫_ℂ}
    (isClosed_eq (by fun_prop) (by fun_prop))
    (fun a ha => by simpa using h a ha)
  simpa using hz

theorem bicommutantState_tracial (S : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H)
    (htr : ∀ a ∈ S, ∀ b ∈ S, ⟪Ω, (a*b) Ω⟫_ℂ = ⟪Ω, (b*a) Ω⟫_ℂ)
    (x y : bicommutantAlg S) :
    bicommutantState S Ω (x*y) = bicommutantState S Ω (y*x) := by
  have ha (a : H →L[ℂ] H) (ha : a ∈ S) (T : bicommutantAlg S) :
      ⟪Ω, (T.1*a) Ω⟫_ℂ = ⟪Ω, (a*T.1) Ω⟫_ℂ :=
    trace_relation_extend S Ω a (fun b hb => htr b hb a ha) T
  exact (trace_relation_extend S Ω x.1 (fun a ha' => (ha a ha' x).symm) y).symm

end

end KKUltraTrace
end

end OAI
