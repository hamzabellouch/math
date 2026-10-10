import OAI.MeasureTheory.Falconer.Graphs.TwoGraphChildren

namespace OAI

/-! # The graph reduction for two original regularized profiles

Only geometric scales are shared. The laws, profiles, descriptor lists,
mask families and endpoint multipliers remain separate.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

structure JetGraphAlignment {n k : ℕ} {α B : ℝ}
    (G H : JetStateGraphData n k α B) : Prop where
  N : H.N = G.N
  a : H.a = G.a
  p : H.p = G.p
  lam : H.lam = G.lam
  σ : H.σ = G.σ
  v : H.v = G.v
  τ : H.τ = G.τ
  δ : H.δ = G.δ
  Dgraph : H.Dgraph = G.Dgraph

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def twoProfileCoefficient (G H : JetStateGraphData n k α B) : ℝ :=
  2*11^(n+2)*((2:ℝ)^G.N)^(
    -(profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)-
    (profileExcess (d := n+2) H.profile H.N H.p-profileExcess (d := n+2) H.profile H.N H.a)+
    min (PlanarFalconer.height (profileExcess (d := n+2) G.profile G.N) G.a G.p)
      (PlanarFalconer.height (profileExcess (d := n+2) H.profile H.N) H.a H.p)+
    (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*G.σ+4*(((n+2:ℕ):ℝ)+1)*G.lam)

noncomputable def twoProfileError (G H : JetStateGraphData n k α B) (A C W T : ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(G.v-G.a))*
    ((profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a)*
      (profileModelMass H.profile H.N H.p/profileModelMass H.profile H.N H.a))^2*
    capGraphError (n+2) k A C W ((2:ℝ)^G.N) T
      (profileModelMass G.profile G.N G.p) (profileModelMass H.profile H.N H.p)
      G.capBound 1 G.Dgraph G.v G.τ G.caps.card
      ((G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (H.Q.descendant H.X).occupiedPaths H.ρ (H.p-H.a)).card

end JetStateGraphData

theorem exists_two_profile_graph_step
    (hpublished : PublishedGnomonicSurface) (n K k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ B Z A C : ℝ, 1 ≤ B ∧ 1 ≤ Z ∧ 0 ≤ A ∧ 0 < C ∧
      ∀ G H : JetStateGraphData n k α B, JetGraphAlignment G H →
      IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure G.v Ψ) →
      ∀ (f : DescriptorJetSymbol n K k G.F G.Dq)
        (g : DescriptorJetSymbol n K k H.F H.Dq),
      independentAngularEnergy G.a G.v Ψ
        (fun z => endpointTransform (G.ρ.restrict (G.Q.descendant G.X).carrier)
          (profileModelMass G.profile G.N G.a) (G.symbol f Z) z.1 z.2)
        (fun z => endpointTransform (H.ρ.restrict (H.Q.descendant H.X).carrier)
          (profileModelMass H.profile H.N H.a) (H.symbol g Z) z.1 z.2) ≤
      G.twoProfileCoefficient H *
        (((descriptorJetBound (n+2) K)^K)^2*((descriptorJetBound (n+2) K)^K)^2*
          Real.sqrt (G.selfChildMaximum K Z Ψ*H.selfChildMaximum K Z Ψ)) +
        G.twoProfileError H A C W T := by
  obtain ⟨B,Z,hB,hZ,hadm⟩ := exists_descriptorJetSymbol_admissible n K k
  obtain ⟨A,C,hA,hC,hgraph⟩ := dyadic_profile_graph_energy_step hpublished n k hn
    φ Ψ hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨B,Z,A,C,hB,hZ,hA,hC,?_⟩
  intro G H hsame hfinite f g
  let := hfinite
  let := G.regular.probability
  let := H.regular.probability
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hsymG : ChartSymbolControl k (G.symbol f Z) 1 G.Dgraph :=
    ((hadm G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.F G.masks G.separated
      G.Dq G.Dmask G.Dsymbol G.Dq_nonneg G.Dmask_one G.Dsymbol_one G.mask_scale G.list_scale f).mono
      (add_nonneg G.Dq_nonneg (zero_le_one.trans G.Dsymbol_one)) G.symbol_scale (subset_refl _)).1
  have hsymH : ChartSymbolControl k (H.symbol g Z) 1 G.Dgraph := by
    rw [← hsame.Dgraph]
    exact ((hadm H.Q H.ρ (fun t => H.profile (t/H.N)) H.N H.σ H.J H.i H.F H.masks H.separated
      H.Dq H.Dmask H.Dsymbol H.Dq_nonneg H.Dmask_one H.Dsymbol_one H.mask_scale H.list_scale g).mono
      (add_nonneg H.Dq_nonneg (zero_le_one.trans H.Dsymbol_one)) H.symbol_scale (subset_refl _)).1
  let E : ℝ := ((descriptorJetBound (n+2) K)^K)^2*((descriptorJetBound (n+2) K)^K)^2*
    Real.sqrt (G.selfChildMaximum K Z Ψ*H.selfChildMaximum K Z Ψ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hchild (row) (hr : row ∈ (G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
      (H.Q.descendant H.X).occupiedPaths H.ρ (G.p-G.a)) :
      independentAngularEnergy G.p G.v Ψ
        (fun z => endpointTransform (G.ρ.restrict ((G.Q.descendant G.X).descendant row.1).carrier)
          (profileModelMass G.profile G.N G.p) (G.symbol f Z) z.1 z.2)
        (fun z => endpointTransform (H.ρ.restrict ((H.Q.descendant H.X).descendant row.2).carrier)
          (profileModelMass H.profile G.N G.p) (H.symbol g Z) z.1 z.2) ≤ E := by
    have hh := Finset.mem_product.mp hr
    have hy : row.2 ∈ (H.Q.descendant H.X).occupiedPaths H.ρ (H.p-H.a) := by
      simpa only [hsame.p,hsame.a] using hh.2
    have he := two_graph_child_energy_le G H hZpos hsame.p hsame.v f g row.1 row.2 hh.1 hy Ψ
    unfold JetStateGraphData.childTransform at he
    simpa only [hsame.p,hsame.N] using he
  have hresult := hgraph G.Q H.Q G.unit H.unit G.ρ H.ρ G.N G.s H.s G.lam
    G.profile H.profile G.regular
    (by simpa only [hsame.N,hsame.lam] using H.regular) G.N_pos
    G.a G.p G.g H.g G.σ G.ap G.pN G.σ_nonneg G.ag G.gp G.gap
    (by simpa only [hsame.a] using H.ag) (by simpa only [hsame.p] using H.gp)
    (by simpa only [hsame.a,hsame.σ,hsame.N] using H.gap)
    G.X H.X G.X_length (H.X_length.trans hsame.a)
    G.v G.τ G.δ G.capBound 1 G.Dgraph G.τ_pos G.δ_pos G.δ_small
    G.capBound_nonneg (by norm_num) G.Dgraph_one G.cap_scale G.endpoint_scale G.phase_error
    G.frequency G.test_scale G.caps id G.partition G.cap_control G.cap_nonneg G.partition_one
    (G.symbol f Z) (H.symbol g Z) hsymG hsymH
    (angularTestWidth G.N G.σ G.J (G.i+1) G.p)
    (angularTestWidth H.N H.σ H.J (H.i+1) H.p) G.left_width
    (by simpa only [hsame.τ,hsame.δ,hsame.a] using H.left_width)
    (G.symbol_parallel_test f Z G.X G.X_length)
    (by
      have ht := H.symbol_parallel_test g Z H.X H.X_length
      unfold profileExcess at ht
      simpa only [hsame.p,hsame.a,hsame.N,hsame.σ] using ht) E hE hchild
  unfold JetStateGraphData.twoProfileCoefficient JetStateGraphData.twoProfileError
  unfold profileExcess
  simpa only [hsame.N,hsame.a,hsame.p,E,add_assoc] using hresult

end Falconer

end OAI
