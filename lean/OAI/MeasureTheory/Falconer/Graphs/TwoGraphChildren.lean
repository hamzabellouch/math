import OAI.MeasureTheory.Falconer.Graphs.JetStateGraph
import OAI.MeasureTheory.Falconer.Recursion.TwoProfileEnergy

namespace OAI

/-! # Separate self energies for the children of a two-profile graph -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def selfChildMaximum (G : JetStateGraphData n k α B)
    (K : ℕ) (A : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  childJetStateMaximum n K k G.Dq (G.F.filter (fun b => G.p < PlanarFalconer.descriptorAnchor b))
    G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    G.X G.X (G.p-G.a) (profileModelMass G.profile G.N G.p) G.p G.v Ψ

theorem selfChildMaximum_nonneg (G : JetStateGraphData n k α B)
    (K : ℕ) (A : ℝ) (Ψ : ℝ → ℝ) : 0 ≤ G.selfChildMaximum K A Ψ :=
  finiteEnvelopeMaximum_nonneg _ _

noncomputable def childTransform (G : JetStateGraphData n k α B) {K : ℕ}
    (A : ℝ) (f : DescriptorJetSymbol n K k G.F G.Dq)
    (X : List (Fin (n+2) → Bool)) (z : ℝ × Sphere (n+2)) : ℂ :=
  endpointTransform (G.ρ.restrict ((G.Q.descendant G.X).descendant X).carrier)
    (profileModelMass G.profile G.N G.p) (G.symbol f A) z.1 z.2

 theorem child_self_energy_le (G : JetStateGraphData n k α B) {K : ℕ}
    {A : ℝ} (hA : 0 < A) (f : DescriptorJetSymbol n K k G.F G.Dq)
    (X : List (Fin (n+2) → Bool))
    (hX : X ∈ (G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a))
    (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure G.v Ψ)] :
    independentAngularEnergy G.p G.v Ψ (G.childTransform A f X) (G.childTransform A f X) ≤
      ((descriptorJetBound (n+2) K)^K)^2*((descriptorJetBound (n+2) K)^K)^2*
        G.selfChildMaximum K A Ψ := by
  let := G.regular.probability
  exact childJetStateEnergy_le G.Q (by rw [G.unit]; norm_num) G.ρ
    (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks G.separated hA G.ap
    G.X G.X G.X_length G.X_length (X,X) (Finset.mem_product.mpr ⟨hX,hX⟩)
    (by unfold profileModelMass; positivity) G.v Ψ f f

end JetStateGraphData

theorem two_graph_child_energy_le {n K k : ℕ} {α B A : ℝ}
    (G H : JetStateGraphData n k α B) (hA : 0 < A) (hp : H.p = G.p) (hv : H.v = G.v)
    (f : DescriptorJetSymbol n K k G.F G.Dq) (g : DescriptorJetSymbol n K k H.F H.Dq)
    (X Y : List (Fin (n+2) → Bool))
    (hX : X ∈ (G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a))
    (hY : Y ∈ (H.Q.descendant H.X).occupiedPaths H.ρ (H.p-H.a))
    (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure G.v Ψ)] :
    independentAngularEnergy G.p G.v Ψ (G.childTransform A f X) (H.childTransform A g Y) ≤
      ((descriptorJetBound (n+2) K)^K)^2*((descriptorJetBound (n+2) K)^K)^2*
        Real.sqrt (G.selfChildMaximum K A Ψ*H.selfChildMaximum K A Ψ) := by
  let := G.regular.probability
  let := H.regular.probability
  have hfinite : IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure H.v Ψ) := by
    rw [hv]
    infer_instance
  let := hfinite
  let μ := G.ρ.restrict ((G.Q.descendant G.X).descendant X).carrier
  let ν := H.ρ.restrict ((H.Q.descendant H.X).descendant Y).carrier
  have hM : 0 < profileModelMass G.profile G.N G.p := by unfold profileModelMass; positivity
  have hP : 0 < profileModelMass H.profile H.N H.p := by unfold profileModelMass; positivity
  have hU : Measurable (G.childTransform A f X) :=
    measurable_endpointTransform μ _ _
      (f.value_measurable G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A)
  have hV : Measurable (H.childTransform A g Y) :=
    measurable_endpointTransform ν _ _
      (g.value_measurable H.Q H.ρ (fun t => H.profile (t/H.N)) H.N H.σ H.J H.i H.masks A)
  have hjet : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by
    have := descriptorJetBound_one_le (n+2) K
    positivity
  have hUbound := fun z : ℝ × Sphere (n+2) => endpointTransform_norm_le μ hM _
    (f.value_norm_le G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks G.separated hA) z.1 z.2
  have hVbound := fun z : ℝ × Sphere (n+2) => endpointTransform_norm_le ν hP _
    (g.value_norm_le H.Q H.ρ (fun t => H.profile (t/H.N)) H.N H.σ H.J H.i H.masks H.separated hA) z.1 z.2
  have hleft := G.child_self_energy_le hA f X hX Ψ
  have hright := H.child_self_energy_le hA g Y hY Ψ
  rw [hp,hv] at hright
  let C : ℝ := ((descriptorJetBound (n+2) K)^K)^2*((descriptorJetBound (n+2) K)^K)^2
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hCS := independentAngularEnergy_le_self_sqrt G.p G.v Ψ _ _ hU hV
    (div_nonneg (mul_nonneg hjet measureReal_nonneg) hM.le)
    (div_nonneg (mul_nonneg hjet measureReal_nonneg) hP.le) hUbound hVbound
  apply (hCS.trans (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).trans_eq
  change Real.sqrt (C*G.selfChildMaximum K A Ψ)*Real.sqrt (C*H.selfChildMaximum K A Ψ) = _
  rw [Real.sqrt_mul hC,Real.sqrt_mul hC,
    Real.sqrt_mul (G.selfChildMaximum_nonneg K A Ψ)]
  calc
    _ = (Real.sqrt C)^2*(Real.sqrt (G.selfChildMaximum K A Ψ)*
        Real.sqrt (H.selfChildMaximum K A Ψ)) := by ring
    _ = _ := by rw [Real.sq_sqrt hC]

end Falconer

end OAI
