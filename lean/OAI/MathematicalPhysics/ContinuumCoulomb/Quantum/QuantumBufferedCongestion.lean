import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedIntersections

namespace OAI

/-! Away from graph vertices, at most two of the actual simple routes meet. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def armedAt (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) (z : ℕ × ℕ) : Prop :=
  ∃ (v : Fin M.n) (h : M.left e = v ∨ M.right e = v), M.endpointArmSupport hd v ⟨e,h⟩ z

theorem armedAt_unique (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {e f : M.Term} {z : ℕ × ℕ} (hv : ∀ v, z ≠ M.placedVertex v)
    (he : M.armedAt hd e z) (hf : M.armedAt hd f z) : e = f := by
  obtain ⟨v,he,hes⟩ := he
  obtain ⟨w,hf,hfs⟩ := hf
  rcases M.endpointArmSupport_meet hA hd v w ⟨e,he⟩ ⟨f,hf⟩ hes hfs with h | h
  · exact h
  · exact (hv v h).elim

theorem armedAt_avoids_crossing (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {e f g : M.Term} (hef : e ≠ f) {z : ℕ × ℕ}
    (he : M.spacedSupport e z) (hf : M.spacedSupport f z) : ¬M.armedAt hd g z := by
  rintro ⟨v,hg,hs⟩
  exact M.endpointArm_avoids_crossing hA hd v ⟨g,hg⟩ hef he hf hs

theorem spaced_third_eq (hA : 0 < A) {e f g : M.Term} (hef : e ≠ f) {z : ℕ × ℕ}
    (he : M.spacedSupport e z) (hf : M.spacedSupport f z) (hg : M.spacedSupport g z) :
    g = e ∨ g = f := by
  by_contra hn
  have hge : g ≠ e := fun h => hn (Or.inl h)
  have hgf : g ≠ f := fun h => hn (Or.inr h)
  have hceg : M.spacedColor e ≠ M.spacedColor g := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hge.symm h) he hg
  have hcfg : M.spacedColor f ≠ M.spacedColor g := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hgf.symm h) hf hg
  have hcef : M.spacedColor e ≠ M.spacedColor f := fun h =>
    Set.disjoint_left.mp (M.spaced_color_disjoint hA hef h) he hf
  rcases he with ⟨he,_⟩ | ⟨he,_⟩ <;>
    rcases hf with ⟨hf,_⟩ | ⟨hf,_⟩ <;> rcases hg with ⟨hg,_⟩ | ⟨hg,_⟩
  all_goals first
    | exact hcef (qmaHorizontalLane_color he hf)
    | exact hcef (qmaVerticalLane_color he hf)
    | exact hceg (qmaHorizontalLane_color he hg)
    | exact hceg (qmaVerticalLane_color he hg)
    | exact hcfg (qmaHorizontalLane_color hf hg)
    | exact hcfg (qmaVerticalLane_color hf hg)

theorem bufferedPath_arm_or_lane (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) {z : ℕ × ℕ} (he : z ∈ (M.bufferedPath hd e).val.support) :
    M.armedAt hd e z ∨ M.spacedSupport e z := by
  rcases M.bufferedPath_support hd e he with h | h | h
  · exact Or.inl ⟨M.left e,Or.inl rfl,h⟩
  · exact Or.inr h
  · exact Or.inl ⟨M.right e,Or.inr rfl,h⟩

theorem bufferedPath_third_eq (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {e f g : M.Term} (hef : e ≠ f) {z : ℕ × ℕ} (hv : ∀ v, z ≠ M.placedVertex v)
    (he : z ∈ (M.bufferedPath hd e).val.support)
    (hf : z ∈ (M.bufferedPath hd f).val.support)
    (hg : z ∈ (M.bufferedPath hd g).val.support) : g = e ∨ g = f := by
  by_contra hn
  have hge : g ≠ e := fun h => hn (Or.inl h)
  have hgf : g ≠ f := fun h => hn (Or.inr h)
  rcases M.bufferedPath_arm_or_lane hd e he with he | he <;>
    rcases M.bufferedPath_arm_or_lane hd f hf with hf | hf <;>
    rcases M.bufferedPath_arm_or_lane hd g hg with hg | hg
  · exact hef (M.armedAt_unique hA hd hv he hf)
  · exact hef (M.armedAt_unique hA hd hv he hf)
  · exact hge (M.armedAt_unique hA hd hv hg he)
  · exact M.armedAt_avoids_crossing hA hd hgf.symm hf hg he
  · exact hgf (M.armedAt_unique hA hd hv hg hf)
  · exact M.armedAt_avoids_crossing hA hd hge.symm he hg hf
  · exact M.armedAt_avoids_crossing hA hd hef he hf hg
  · exact hn (M.spaced_third_eq hA hef he hf hg)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
