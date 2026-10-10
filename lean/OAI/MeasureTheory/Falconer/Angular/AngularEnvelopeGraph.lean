import OAI.MeasureTheory.Falconer.Angular.AngularEnvelope
import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphEstimate

namespace OAI

/-! # The actual profile graph estimate on the admissible energy envelope

Restriction to a child is implemented by the existing spatial cell symbol.
The original restricted endpoint integral is unchanged, and the support
condition is propagated explicitly to the child's good set.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

noncomputable def finiteEnvelopeMaximum {ι : Type*} (S : Finset ι) (F : ι → ℝ) : ℝ :=
  sSup (insert 0 (F '' (S : Set ι)))

theorem finiteEnvelopeMaximum_nonneg {ι : Type*} (S : Finset ι) (F : ι → ℝ) :
    0 ≤ finiteEnvelopeMaximum S F :=
  le_csSup ((S.finite_toSet.image F).insert 0).bddAbove (Or.inl rfl)

theorem le_finiteEnvelopeMaximum {ι : Type*} (S : Finset ι) (F : ι → ℝ)
    {i : ι} (hi : i ∈ S) : F i ≤ finiteEnvelopeMaximum S F :=
  le_csSup ((S.finite_toSet.image F).insert 0).bddAbove (Or.inr ⟨i,hi,rfl⟩)

theorem finiteEnvelopeMaximum_le {ι : Type*} (S : Finset ι) (F : ι → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h : ∀ i ∈ S, F i ≤ H) :
    finiteEnvelopeMaximum S F ≤ H := by
  change sSup (insert (0:ℝ) (F '' (S : Set ι))) ≤ H
  apply csSup_le (show (insert (0:ℝ) (F '' (S : Set ι))).Nonempty from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨i,hi,rfl⟩
  · exact hH
  · exact h i hi

theorem angularEnvelope_le_of_admissible {n : ℕ}
    (μ ν : Measure (Space (n+2))) (M P : ℝ) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2)))
    {H : ℝ} (hH : 0 ≤ H)
    (h : ∀ b c, AngularAdmissible k D GoodLeft b → AngularAdmissible k D GoodRight c →
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform μ M b z.1 z.2)
        (fun z => endpointTransform ν P c z.1 z.2) ≤ H) :
    angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight ≤ H := by
  apply csSup_le (angularEnergyValues_nonempty μ ν M P k D a v Ψ GoodLeft GoodRight)
  intro E hE
  rcases hE with rfl | ⟨b,c,hb,hc,rfl⟩
  · exact hH
  · exact h b c hb hc

theorem AngularAdmissible.cell {n k : ℕ} {D : ℝ}
    {Good Good' : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ}
    (h : AngularAdmissible k D Good b) (hD : 0 ≤ D) (Q : DyadicCube (n+2))
    (hGood : ∀ x ∈ Q.carrier, ∀ w, (x,w) ∈ Good → (x,w) ∈ Good') :
    AngularAdmissible k D Good' (cellSymbol Q b) := by
  refine ⟨h.1.cell (by norm_num) hD Q,?_⟩
  intro x w hw
  have hx := cellSymbol_active Q b hw
  have hb : b x w ≠ 0 := by simpa only [cellSymbol,ite_eq_left hx] using hw
  exact hGood x hx w (h.2 x w hb)

theorem child_energy_le_angularEnvelope {n k : ℕ} {D : ℝ}
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q₁ Q₂ : DyadicCube (n+2)) {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (hD : 0 ≤ D) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight ChildLeft ChildRight : Set (Space (n+2) × Sphere (n+2)))
    (hLeft : ∀ x ∈ Q₁.carrier, ∀ w, (x,w) ∈ GoodLeft → (x,w) ∈ ChildLeft)
    (hRight : ∀ x ∈ Q₂.carrier, ∀ w, (x,w) ∈ GoodRight → (x,w) ∈ ChildRight)
    (b c : Space (n+2) → Sphere (n+2) → ℂ)
    (hb : AngularAdmissible k D GoodLeft b) (hc : AngularAdmissible k D GoodRight c) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) M b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) P c z.1 z.2) ≤
      angularEnvelope (μ.restrict Q₁.carrier) (ν.restrict Q₂.carrier)
        M P k D a v Ψ ChildLeft ChildRight := by
  have h := admissible_energy_le_angularEnvelope (μ.restrict Q₁.carrier) (ν.restrict Q₂.carrier)
    hM hP k D a v Ψ ChildLeft ChildRight (cellSymbol Q₁ b) (cellSymbol Q₂ c)
    (hb.cell hD Q₁ hLeft) (hc.cell hD Q₂ hRight)
  simpa only [endpointTransform_cellSymbol] using h

theorem profile_angular_envelope_terminal {n : ℕ} (k : ℕ) (D : ℝ)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a q : ℕ} (ha : a ≤ N) (X Y : List (Fin (n+2) → Bool))
    (hX : X.length = a) (hY : Y.length = a) (v : ℝ)
    (hv : v ≤ (a:ℝ)+100*q) (Ψ : ℝ → ℝ) {W : ℝ}
    (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hsupp : ∀ t, 4 < t → Ψ t = 0)
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2))) :
    angularEnvelope (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
      (profileModelMass m N a) (profileModelMass m N a) k D a v Ψ GoodLeft GoodRight ≤
    (4*W*(sphereMeasure (n+2)).real univ^2)*
      ((2:ℝ)^N)^(100*((n+2:ℕ):ℝ)*q/N+4*(((n+2:ℕ):ℝ)+1)*lam) := by
  apply angularEnvelope_le_of_admissible _ _ _ _ _ _ _ _ _ _ _ (by positivity)
  intro b c hb hc
  simpa only [one_pow,mul_one] using profile_angular_terminal Q ρ hreg hN ha X Y
    hX hY v hv Ψ hW hΨ hsupp (by norm_num : (0:ℝ) ≤ 1) b c hb.1.bound hc.1.bound

/-- The finite maximum uses the same original measures and the actual child good sets. -/
noncomputable def childAngularEnvelopeMaximum {n : ℕ}
    (Q₁ Q₂ : DyadicCube (n+2)) (ρ₁ ρ₂ : Measure (Space (n+2))) (j : ℕ)
    (M P : ℝ) (k : ℕ) (D a v : ℝ) (Ψ : ℝ → ℝ)
    (GoodLeft GoodRight : List (Fin (n+2) → Bool) →
      Set (Space (n+2) × Sphere (n+2))) : ℝ :=
  finiteEnvelopeMaximum (Q₁.occupiedPaths ρ₁ j ×ˢ Q₂.occupiedPaths ρ₂ j)
    (fun row => angularEnvelope
      (ρ₁.restrict (Q₁.descendant row.1).carrier)
      (ρ₂.restrict (Q₂.descendant row.2).carrier)
      M P k D a v Ψ (GoodLeft row.1) (GoodRight row.2))

/-- The actual near contribution uses the same finite child maximum as the graph step. -/
theorem profile_near_le_child_angular_envelope {n k : ℕ} (D : ℝ) (hD : 0 ≤ D)
    (Q : DyadicCube (n+2)) (hQ : Q.side = 1) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2)))
    (ChildLeft ChildRight : List (Fin (n+2) → Bool) →
      Set (Space (n+2) × Sphere (n+2)))
    (hLeft : ∀ q ∈ (Q.descendant X).occupiedPaths ρ (p-a),
      ∀ x ∈ ((Q.descendant X).descendant q).carrier, ∀ z,
      (x,z) ∈ GoodLeft → (x,z) ∈ ChildLeft q)
    (hRight : ∀ q ∈ (Q.descendant Y).occupiedPaths ρ (p-a),
      ∀ x ∈ ((Q.descendant Y).descendant q).carrier, ∀ z,
      (x,z) ∈ GoodRight → (x,z) ∈ ChildRight q)
    (b c : Space (n+2) → Sphere (n+2) → ℂ)
    (hb : AngularAdmissible k D GoodLeft b) (hc : AngularAdmissible k D GoodRight c) :
    profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ m N a p v Ψ b c ≤
      ((2*(10*((n+2)+1))+1)^(2*(n+2)):ℕ) *
      ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-(((n+2:ℕ):ℝ)/2)*(p:ℝ)/N)-
        (m ((a:ℝ)/N)-(((n+2:ℕ):ℝ)/2)*(a:ℝ)/N))+4*(((n+2:ℕ):ℝ)+1)*lam)*
      childAngularEnvelopeMaximum (Q.descendant X) (Q.descendant Y) ρ ρ (p-a)
        (profileModelMass m N p) (profileModelMass m N p) k D p v Ψ
        ChildLeft ChildRight := by
  let := hreg.probability
  have hM : 0 < profileModelMass m N p := by unfold profileModelMass; positivity
  apply profile_near_reduction Q hQ ρ hreg hN hap hp X Y hX hY v Ψ b c
    hb.1.measurable hc.1.measurable (by norm_num) (by norm_num)
    (finiteEnvelopeMaximum_nonneg _ _) hb.1.bound hc.1.bound
  intro row hrow
  have hr := Finset.mem_product.mp hrow
  apply (child_energy_le_angularEnvelope ρ ρ
    ((Q.descendant X).descendant row.1) ((Q.descendant Y).descendant row.2)
    hM hM hD p v Ψ GoodLeft GoodRight (ChildLeft row.1) (ChildRight row.2)
    (hLeft row.1 hr.1) (hRight row.2 hr.2) b c hb hc).trans
  exact le_finiteEnvelopeMaximum _ (fun row =>
    angularEnvelope (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier)
      (profileModelMass m N p) (profileModelMass m N p) k D p v Ψ
      (ChildLeft row.1) (ChildRight row.2)) hrow

/-- The graph estimate preserves the fixed symbol budget in the parent and child
suprema. Only the localization estimate uses the enlarged analytic budget. -/
theorem dyadic_profile_angular_envelope_step
    (hpublished : PublishedGnomonicSurface) (n k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (n+2))) (N : ℕ) (s₁ s₂ lam : ℝ)
        (m₁ m₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂ → 0 < N →
      ∀ (a p g₁ g₂ : ℕ) (σ : ℝ), a ≤ p → p ≤ N → 0 ≤ σ →
      a ≤ g₁ → g₁ ≤ p → (g₁:ℝ)-a ≤ 2*σ*N →
      a ≤ g₂ → g₂ ≤ p → (g₂:ℝ)-a ≤ 2*σ*N →
      ∀ (X Y : List (Fin (n+2) → Bool)), X.length = a → Y.length = a →
      ∀ (v τ δ H Dsym Dgraph : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ Dsym → Dsym ≤ Dgraph → 1 ≤ Dgraph → δ⁻¹ ≤ Dgraph →
      Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side ≤ (τ/4)*Dgraph →
      2*Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(p-a))+
        8*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side) ≤ τ/4 →
      4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ →
      4*τ*((2:ℝ)^(p-a)/(Q₁.descendant X).side) ≤
        (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ) →
      ∀ {ι : Type*} (K : Finset ι) (w : ι → Sphere (n+2))
        (η : ι → Sphere (n+2) → ℝ),
      (∀ j ∈ K, ChartCapControl k (η j) (w j : Space (n+2)) δ H) →
      (∀ j ∈ K, ∀ z, 0 ≤ η j z) → (∀ z, ∑ j ∈ K, η j z = 1) →
      ∀ (GoodLeft GoodRight : Set (Space (n+2) × Sphere (n+2)))
        (ChildLeft ChildRight : List (Fin (n+2) → Bool) →
          Set (Space (n+2) × Sphere (n+2))),
      (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
        ∀ x ∈ ((Q₁.descendant X).descendant q).carrier, ∀ z,
        (x,z) ∈ GoodLeft → (x,z) ∈ ChildLeft q) →
      (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        ∀ x ∈ ((Q₂.descendant Y).descendant q).carrier, ∀ z,
        (x,z) ∈ GoodRight → (x,z) ∈ ChildRight q) →
      ∀ (W₁ W₂ : ℝ),
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(g₁-a))) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₂.descendant Y).side/(2:ℝ)^(g₂-a))) ≤ W₂ →
      (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
        ∀ x ∈ ((Q₁.descendant X).descendant q).carrier,
        ∀ z : Sphere (n+2), (x,z) ∈ GoodLeft →
          DyadicParallelTest (Q₁.descendant X) ((Q₁.descendant X).occupiedPaths ρ₁ (p-a))
            (g₁-a) q z W₁
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₁ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        ∀ x ∈ ((Q₂.descendant Y).descendant q).carrier,
        ∀ z : Sphere (n+2), (x,z) ∈ GoodRight →
          DyadicParallelTest (Q₂.descendant Y) ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))
            (g₂-a) q z W₂
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₂ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      let E := childAngularEnvelopeMaximum (Q₁.descendant X) (Q₂.descendant Y)
        ρ₁ ρ₂ (p-a) (profileModelMass m₁ N p) (profileModelMass m₂ N p)
        k Dsym p v Ψ ChildLeft ChildRight
      angularEnvelope (ρ₁.restrict (Q₁.descendant X).carrier)
        (ρ₂.restrict (Q₂.descendant Y).carrier)
        (profileModelMass m₁ N a) (profileModelMass m₂ N a)
        k Dsym a v Ψ GoodLeft GoodRight ≤
      2*11^(n+2)*((2:ℝ)^N)^(
        -((m₁ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₁ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))-
        ((m₂ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₂ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))+
        (min (PlanarFalconer.height (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)
          (PlanarFalconer.height (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)+
        (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*σ)+4*(((n+2:ℕ):ℝ)+1)*lam)*E +
      (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError (n+2) k A C W ((2:ℝ)^N) T
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H 1 Dgraph v τ K.card
          ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
            (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card := by
  obtain ⟨A,C,hA,hC,hgraph⟩ := dyadic_profile_graph_energy_step hpublished n k hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ N s₁ s₂ lam m₁ m₂ hreg₁ hreg₂ hN
    a p g₁ g₂ σ hap hp hσ hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂ X Y hX hY
    v τ δ H Dsym Dgraph hτ hδ hδsmall hH hDsym hsymgraph hD hδD hnorm herr hfreq hL
    ι K w η hcap hη hpart GoodLeft GoodRight ChildLeft ChildRight
    hleft hright W₁ W₂ hw₁ hw₂ htest₁ htest₂ _
  let := hreg₁.probability
  let := hreg₂.probability
  let E := childAngularEnvelopeMaximum (Q₁.descendant X) (Q₂.descendant Y)
    ρ₁ ρ₂ (p-a) (profileModelMass m₁ N p) (profileModelMass m₂ N p)
    k Dsym p v Ψ ChildLeft ChildRight
  have hE : 0 ≤ E := finiteEnvelopeMaximum_nonneg _ _
  have hmass (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  have herror : 0 ≤ capGraphError (n+2) k A C W ((2:ℝ)^N) T
      (profileModelMass m₁ N p) (profileModelMass m₂ N p) H 1 Dgraph v τ K.card
      ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
        (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card := by
    unfold capGraphError
    positivity
  apply angularEnvelope_le_of_admissible _ _ _ _ _ _ _ _ _ _ _ (by positivity)
  intro b c hb hc
  apply hgraph Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ N s₁ s₂ lam m₁ m₂ hreg₁ hreg₂ hN
    a p g₁ g₂ σ hap hp hσ hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂ X Y hX hY
    v τ δ H 1 Dgraph hτ hδ hδsmall hH (by norm_num) hD hδD hnorm herr hfreq hL
    K w η hcap hη hpart b c
    (hb.mono hDsym hsymgraph subset_rfl).1
    (hc.mono hDsym hsymgraph subset_rfl).1 W₁ W₂ hw₁ hw₂
  · intro q hq
    filter_upwards [ae_restrict_mem ((Q₁.descendant X).descendant q).measurable] with x hx
    intro z hz
    exact htest₁ q hq x hx z (hb.2 x z hz)
  · intro q hq
    filter_upwards [ae_restrict_mem ((Q₂.descendant Y).descendant q).measurable] with x hx
    intro z hz
    exact htest₂ q hq x hx z (hc.2 x z hz)
  · exact hE
  · intro row hrow
    have hr := Finset.mem_product.mp hrow
    apply (child_energy_le_angularEnvelope ρ₁ ρ₂
      ((Q₁.descendant X).descendant row.1) ((Q₂.descendant Y).descendant row.2)
      (hmass m₁ p) (hmass m₂ p) hDsym p v Ψ GoodLeft GoodRight
      (ChildLeft row.1) (ChildRight row.2)
      (hleft row.1 hr.1) (hright row.2 hr.2) b c hb hc).trans
    exact le_finiteEnvelopeMaximum _ (fun row =>
      angularEnvelope (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
        (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
        (profileModelMass m₁ N p) (profileModelMass m₂ N p) k Dsym p v Ψ
        (ChildLeft row.1) (ChildRight row.2)) hrow

end Falconer

end OAI
