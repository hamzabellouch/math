import OAI.MeasureTheory.Falconer.Fourier.JetStateChildren
import OAI.MeasureTheory.Falconer.Recursion.ProfileExcess

namespace OAI

/-! # Near and terminal bounds for the exact factorized angular states -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

 theorem profile_near_jetState {n K L : ℕ} {D : ℝ} {F : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (hQ : Q.side = 1) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f g : DescriptorJetSymbol n K L F D) :
    profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ m N a p v Ψ
      (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (g.value Q ρ (fun t => m (t/N)) N σ J i S A) ≤
    ((2*(10*((n+2)+1))+1)^(2*(n+2)):ℕ) *
      ((2:ℝ)^N)^(-2*(profileExcess (d := n+2) m N p-profileExcess (d := n+2) m N a)+
        4*(((n+2:ℕ):ℝ)+1)*lam)*
      (((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
        childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
          Q ρ (fun t => m (t/N)) N σ J i S A X Y (p-a) (profileModelMass m N p) p v Ψ) := by
  let := hreg.probability
  have hbase : 0 ≤ descriptorJetBound (n+2) K := zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by positivity
  have hMp : 0 < profileModelMass m N p := by unfold profileModelMass; positivity
  have hchild0 : 0 ≤ ((descriptorJetBound (n+2) K)^K)^2 *
      ((descriptorJetBound (n+2) K)^K)^2 *
        childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
          Q ρ (fun t => m (t/N)) N σ J i S A X Y (p-a) (profileModelMass m N p) p v Ψ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (childJetStateMaximum_nonneg n K L D _ Q ρ _ N σ J i S A X Y (p-a) _ p v Ψ)
  apply profile_near_reduction Q hQ ρ hreg hN hap hp X Y hX hY v Ψ
    (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
    (g.value Q ρ (fun t => m (t/N)) N σ J i S A)
    (f.value_measurable _ _ _ _ _ _ _ _ _) (g.value_measurable _ _ _ _ _ _ _ _ _)
    hbound hbound
    hchild0
    (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hF hA)
  intro row hrow
  exact childJetStateEnergy_le Q (by rw [hQ]; norm_num) ρ (fun t => m (t/N))
    N σ J i S hF hA hap X Y hX hY row hrow hMp v Ψ f g

 theorem profile_jetState_terminal {n K L : ℕ} {D : ℝ} (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a q : ℕ} (ha : a ≤ N)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (hv : v ≤ (a:ℝ)+100*q) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hsupp : ∀ t, 4 < t → Ψ t = 0) :
    jetStateEnvelope n K L D F F Q ρ (fun t => m (t/N)) N σ J i S A
      (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
      (profileModelMass m N a) (profileModelMass m N a) a v Ψ ≤
    (4*W*((descriptorJetBound (n+2) K)^K*A⁻¹)^4*(sphereMeasure (n+2)).real univ^2)*
      ((2:ℝ)^N)^(100*((n+2:ℕ):ℝ)*q/N+4*(((n+2:ℕ):ℝ)+1)*lam) := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K := zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by positivity
  apply csSup_le (show (jetStateValues n K L D F F Q ρ (fun t => m (t/N)) N σ J i S A
    (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
    (profileModelMass m N a) (profileModelMass m N a) a v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · positivity
  · exact profile_angular_terminal Q ρ hreg hN ha X Y hX hY v hv Ψ hW hΨ hsupp hbound
      (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (g.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hF hA)

end Falconer

end OAI
