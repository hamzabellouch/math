import OAI.Geometry.SurfaceImmersion.Primitive.SpatialLoopAmplitude

namespace OAI

/-! Restrict a constructed loop to a neighborhood where every zero-amplitude
jet has the constant normal velocity required by the supported expansion. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial

variable {O : TopologicalSpace.Opens LowJet}

def restrict (l : SurfaceVelocityFamily.Loop O) (V : TopologicalSpace.Opens LowJet)
    (hVO : (V : Set LowJet) ⊆ O) : SurfaceVelocityFamily.Loop V where
  amplitude := l.amplitude
  smoothAmplitude := l.smoothAmplitude.mono hVO
  velocity := l.velocity
  smoothVelocity := l.smoothVelocity.mono (Set.prod_mono hVO Subset.rfl)
  periodic J hJ := l.periodic J (hVO hJ)
  gram_ne J hJ := l.gram_ne J (hVO hJ)
  nonzero J hJ := l.nonzero J (hVO hJ)
  perpY J hJ := l.perpY J (hVO hJ)
  perpC J hJ := l.perpC J (hVO hJ)
  length J hJ := l.length J (hVO hJ)
  mean J hJ := l.mean J (hVO hJ)

lemma restrict_hasSpatialAmplitude (l : SurfaceVelocityFamily.Loop O)
    (V : TopologicalSpace.Opens LowJet) (hVO : (V : Set LowJet) ⊆ O)
    {a : Base → ℝ} (ha : l.HasSpatialAmplitude a) :
    (l.restrict V hVO).HasSpatialAmplitude a := fun J hJ => ha J (hVO hJ)

theorem restrict_zero_collar (l : SurfaceVelocityFamily.Loop O)
    {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    {Q W : Set LowJet} (hQ : Q ⊆ O) (hW : IsOpen W)
    (hQW : ∀ J ∈ Q, a (lowJetPosition J) = 0 → J ∈ W)
    (hzero : ∀ J ∈ W, a (lowJetPosition J) = 0 → ∀ t, l.velocity (J,t) = normal J) :
    ∃ V : TopologicalSpace.Opens LowJet, Q ⊆ V ∧ (V : Set LowJet) ⊆ O ∧
      ∃ l' : SurfaceVelocityFamily.Loop V, l'.HasSpatialAmplitude a ∧
        (l'.velocity = l.velocity) ∧
        ∀ J ∈ V, a (lowJetPosition J) = 0 → ∀ t, l'.velocity (J,t) = normal J := by
  let C : Set LowJet := {J | a (lowJetPosition J) ≠ 0} ∪ W
  have hC : IsOpen C := (isClosed_eq ((ha.comp lowJetPosition.contDiff).continuous)
    continuous_const).isOpen_compl.union hW
  let V : TopologicalSpace.Opens LowJet := ⟨(O : Set LowJet) ∩ C,O.isOpen.inter hC⟩
  have hVO : (V : Set LowJet) ⊆ O := inter_subset_left
  refine ⟨V,?_,hVO,l.restrict V hVO,l.restrict_hasSpatialAmplitude V hVO hamp,rfl,?_⟩
  · intro J hJ
    refine ⟨hQ hJ,?_⟩
    by_cases hz : a (lowJetPosition J) = 0
    · exact Or.inr (hQW J hJ hz)
    · exact Or.inl hz
  · intro J hJ hz t
    have hJW : J ∈ W := hJ.2.resolve_left (not_not_intro hz)
    exact hzero J hJW hz t

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
