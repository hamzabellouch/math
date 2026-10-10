import OAI.MeasureTheory.Falconer.Fourier.JetStateChildren
import OAI.MeasureTheory.Falconer.Fourier.JetStateBudget
import OAI.MeasureTheory.Falconer.Estimates.DescriptorEnvelope
import OAI.MeasureTheory.Falconer.Recursion.ProfileExcess

namespace OAI

/-! # The profile graph estimate on the exact factorized state class

This packages the geometric hypotheses of the proved graph estimate. The
child envelope uses exactly the original list with anchors at most p
removed, and the same normalization and smooth multipliers.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped SchwartzMap

structure JetStateGraphData (n k : ℕ) (α B : ℝ) where
  Q : DyadicCube (n+2)
  unit : Q.side = 1
  ρ : Measure (Space (n+2))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  a : ℕ
  p : ℕ
  g : ℕ
  ap : a ≤ p
  pN : p ≤ N
  ag : a ≤ g
  gp : g ≤ p
  σ : ℝ
  σ_nonneg : 0 ≤ σ
  gap : (g:ℝ)-a ≤ 2*σ*N
  X : List (Fin (n+2) → Bool)
  Y : List (Fin (n+2) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  v : ℝ
  τ : ℝ
  δ : ℝ
  capBound : ℝ
  Dq : ℝ
  Dmask : ℝ
  Dsymbol : ℝ
  Dgraph : ℝ
  τ_pos : 0 < τ
  δ_pos : 0 < δ
  δ_small : δ ≤ 1/2
  capBound_nonneg : 0 ≤ capBound
  Dq_nonneg : 0 ≤ Dq
  Dmask_one : 1 ≤ Dmask
  Dsymbol_one : 1 ≤ Dsymbol
  Dgraph_one : 1 ≤ Dgraph
  symbol_scale : Dq+Dsymbol ≤ Dgraph
  cap_scale : δ⁻¹ ≤ Dgraph
  endpoint_scale : Real.sqrt (n+2 : ℕ)*(Q.descendant X).side ≤ (τ/4)*Dgraph
  phase_error : 2*Real.sqrt (n+2 : ℕ)*((Q.descendant X).side/(2:ℝ)^(p-a))+
    8*δ*(Real.sqrt (n+2 : ℕ)*(Q.descendant X).side) ≤ τ/4
  frequency : 4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ
  test_scale : 4*τ*((2:ℝ)^(p-a)/(Q.descendant X).side) ≤
    (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ)
  F : Finset PolicyDescriptor
  masks : PolicyDescriptor → Finset (Sphere (n+2))
  J : ℕ
  i : ℕ
  separated : ∀ b ∈ F, ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
    descriptorMaskRadius N σ b/2 ≤ dist w z
  mask_scale : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask
  list_scale : (F.card:ℝ)*B*Dmask ≤ Dsymbol
  parallel : PolicyDescriptor.parallel g p ∈ F
  left_width : 2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q.descendant X).side/(2:ℝ)^(g-a))) ≤
    angularTestWidth N σ J (i+1) p
  right_width : 2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q.descendant Y).side/(2:ℝ)^(g-a))) ≤
    angularTestWidth N σ J (i+1) p
  caps : Finset (Sphere (n+2))
  partition : Sphere (n+2) → Sphere (n+2) → ℝ
  cap_control : ∀ w ∈ caps, ChartCapControl k (partition w) (w : Space (n+2)) δ capBound
  cap_nonneg : ∀ w ∈ caps, ∀ z, 0 ≤ partition w z
  partition_one : ∀ z, ∑ w ∈ caps, partition w z = 1

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

noncomputable def coefficient (G : JetStateGraphData n k α B) : ℝ :=
  2*11^(n+2)*((2:ℝ)^G.N)^(
    -(profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)-
    (profileExcess (d := n+2) G.profile G.N G.p-profileExcess (d := n+2) G.profile G.N G.a)+
    PlanarFalconer.height (profileExcess (d := n+2) G.profile G.N) G.a G.p+
    (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*G.σ+4*(((n+2:ℕ):ℝ)+1)*G.lam)

noncomputable def error (G : JetStateGraphData n k α B) (H C W T : ℝ) : ℝ :=
  (2:ℝ)^(((n+2:ℕ):ℝ)*(G.v-G.a)) *
    ((profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a)*
      (profileModelMass G.profile G.N G.p/profileModelMass G.profile G.N G.a))^2 *
    capGraphError (n+2) k H C W ((2:ℝ)^G.N) T
      (profileModelMass G.profile G.N G.p) (profileModelMass G.profile G.N G.p)
      G.capBound 1 G.Dgraph G.v G.τ G.caps.card
      ((G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (G.Q.descendant G.Y).occupiedPaths G.ρ (G.p-G.a)).card

noncomputable abbrev symbol (G : JetStateGraphData n k α B) {K : ℕ}
    (f : DescriptorJetSymbol n K k G.F G.Dq) (A : ℝ) :=
  f.value G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A

noncomputable def childMaximum (G : JetStateGraphData n k α B) (K : ℕ) (A : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  childJetStateMaximum n K k G.Dq (G.F.filter (fun b => G.p < descriptorAnchor b))
    G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    G.X G.Y (G.p-G.a) (profileModelMass G.profile G.N G.p) G.p G.v Ψ

 theorem symbol_parallel_test (G : JetStateGraphData n k α B) {K : ℕ}
    (f : DescriptorJetSymbol n K k G.F G.Dq) (A : ℝ)
    (X : List (Fin (n+2) → Bool)) (hX : X.length = G.a)
    (U : List (Fin (n+2) → Bool))
    (hU : U ∈ (G.Q.descendant X).occupiedPaths G.ρ (G.p-G.a)) :
    ∀ᵐ x ∂G.ρ.restrict ((G.Q.descendant X).descendant U).carrier,
    ∀ w : Sphere (n+2), G.symbol f A x w ≠ 0 →
      DyadicParallelTest (G.Q.descendant X) ((G.Q.descendant X).occupiedPaths G.ρ (G.p-G.a))
        (G.g-G.a) U w (angularTestWidth G.N G.σ G.J (G.i+1) G.p)
        ⌈((2:ℝ)^G.N)^(PlanarFalconer.height
          (profileExcess (d := n+2) G.profile G.N) G.g G.p+
            1000*(((n+2:ℕ):ℝ)+1)*G.σ)⌉₊ := by
  filter_upwards [ae_restrict_mem ((G.Q.descendant X).descendant U).measurable] with x hx
  intro w hw
  apply descriptorListGood_parallel_test G.Q G.unit G.ρ G.profile G.N G.σ G.J (G.i+1)
    G.F G.ag G.gp G.parallel X U hX ((mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hU).1) hx w
  intro b hb
  exact descriptorJetProduct_support G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i
    G.F id G.masks (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w
    (mul_ne_zero_iff.mp hw).1 b hb

 theorem coefficient_nonneg (G : JetStateGraphData n k α B) : 0 ≤ G.coefficient := by
  unfold coefficient
  positivity

 theorem error_nonneg (G : JetStateGraphData n k α B) {H C W T : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hW : 0 ≤ W) : 0 ≤ G.error H C W T := by
  have hcap := G.capBound_nonneg
  have hD := G.Dgraph_one
  have hτ := G.τ_pos
  unfold error capGraphError
  positivity

end JetStateGraphData
 theorem exists_jetState_graph_step
    (hpublished : PublishedGnomonicSurface) (n K k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ)
    :
    ∃ B A H C : ℝ, 1 ≤ B ∧ 1 ≤ A ∧ 0 ≤ H ∧ 0 < C ∧
      ∀ G : JetStateGraphData n k α B,
      IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure G.v Ψ) →
      jetStateEnvelope n K k G.Dq G.F G.F G.Q G.ρ (fun t => G.profile (t/G.N))
        G.N G.σ G.J G.i G.masks A
        (G.ρ.restrict (G.Q.descendant G.X).carrier) (G.ρ.restrict (G.Q.descendant G.Y).carrier)
        (profileModelMass G.profile G.N G.a) (profileModelMass G.profile G.N G.a) G.a G.v Ψ ≤
      G.coefficient *
        (((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
          G.childMaximum K A Ψ) + G.error H C W T := by
  obtain ⟨B,A,hB,hA,hadm⟩ := exists_descriptorJetSymbol_admissible n K k
  obtain ⟨H,C,hH,hC,hgraph⟩ := dyadic_profile_graph_energy_step hpublished n k hn
    φ Ψ hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨B,A,H,C,hB,hA,hH,hC,?_⟩
  intro G hfinite
  let := hfinite
  let := G.regular.probability
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hQ : 0 < G.Q.side := by rw [G.unit]; norm_num
  have hMp : 0 < profileModelMass G.profile G.N G.p := by unfold profileModelMass; positivity
  have hsym (f : DescriptorJetSymbol n K k G.F G.Dq) :
      AngularAdmissible k G.Dgraph
        {z | ∀ b ∈ G.F, z ∈ descriptorEndpointGood G.Q G.ρ (fun t => G.profile (t/G.N))
          G.N G.σ G.J (G.i+1) b} (G.symbol f A) :=
    (hadm G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.F G.masks G.separated
      G.Dq G.Dmask G.Dsymbol G.Dq_nonneg G.Dmask_one G.Dsymbol_one G.mask_scale G.list_scale f).mono
      (add_nonneg G.Dq_nonneg (zero_le_one.trans G.Dsymbol_one)) G.symbol_scale (subset_refl _)
  have hchild0 : 0 ≤ ((descriptorJetBound (n+2) K)^K)^2 *
      ((descriptorJetBound (n+2) K)^K)^2 * G.childMaximum K A Ψ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (childJetStateMaximum_nonneg n K k G.Dq _ G.Q G.ρ _ G.N G.σ G.J G.i G.masks A
        G.X G.Y (G.p-G.a) _ G.p G.v Ψ)
  apply csSup_le (show (jetStateValues n K k G.Dq G.F G.F G.Q G.ρ
    (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    (G.ρ.restrict (G.Q.descendant G.X).carrier) (G.ρ.restrict (G.Q.descendant G.Y).carrier)
    (profileModelMass G.profile G.N G.a) (profileModelMass G.profile G.N G.a)
    G.a G.v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact add_nonneg (mul_nonneg G.coefficient_nonneg hchild0) (G.error_nonneg hH hC.le hW)
  · have hchild (row) (hr : row ∈ (G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (G.Q.descendant G.Y).occupiedPaths G.ρ (G.p-G.a)) :
        independentAngularEnergy G.p G.v Ψ
          (fun z => endpointTransform (G.ρ.restrict ((G.Q.descendant G.X).descendant row.1).carrier)
            (profileModelMass G.profile G.N G.p) (G.symbol f A) z.1 z.2)
          (fun z => endpointTransform (G.ρ.restrict ((G.Q.descendant G.Y).descendant row.2).carrier)
            (profileModelMass G.profile G.N G.p) (G.symbol g A) z.1 z.2) ≤
        ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
          G.childMaximum K A Ψ :=
      childJetStateEnergy_le G.Q hQ G.ρ (fun t => G.profile (t/G.N))
        G.N G.σ G.J G.i G.masks G.separated hAp G.ap G.X G.Y G.X_length G.Y_length
        row hr hMp G.v Ψ f g
    have hresult := hgraph G.Q G.Q G.unit G.unit G.ρ G.ρ G.N G.s G.s G.lam
      G.profile G.profile G.regular G.regular G.N_pos
      G.a G.p G.g G.g G.σ G.ap G.pN G.σ_nonneg
      G.ag G.gp G.gap G.ag G.gp G.gap G.X G.Y G.X_length G.Y_length
      G.v G.τ G.δ G.capBound 1 G.Dgraph G.τ_pos G.δ_pos G.δ_small
      G.capBound_nonneg (by norm_num) G.Dgraph_one G.cap_scale G.endpoint_scale G.phase_error
      G.frequency G.test_scale G.caps id G.partition G.cap_control G.cap_nonneg G.partition_one
      (G.symbol f A) (G.symbol g A) (hsym f).1 (hsym g).1
      (angularTestWidth G.N G.σ G.J (G.i+1) G.p)
      (angularTestWidth G.N G.σ G.J (G.i+1) G.p) G.left_width G.right_width
      (G.symbol_parallel_test f A G.X G.X_length) (G.symbol_parallel_test g A G.Y G.Y_length)
      _ hchild0 hchild
    have hexcess : profileExcess (d := n+2) G.profile G.N =
        (fun j : ℕ => G.profile ((j:ℝ)/G.N)-((n+2:ℕ):ℝ)/2*(j:ℝ)/G.N) := rfl
    simpa only [jetStateEnergy,JetStateGraphData.symbol,JetStateGraphData.coefficient,
      JetStateGraphData.error,hexcess,min_self,add_assoc] using hresult

end Falconer

end OAI
