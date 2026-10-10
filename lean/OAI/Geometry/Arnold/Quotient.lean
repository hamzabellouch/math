import OAI.Geometry.Arnold.FieldAlgebra

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Quadric
open scoped ContDiff Topology

lemma project_eq_iff_phase (z w : UnitQuadric) : project z = project w ↔
    ∃ c : ℂ, Complex.normSq c = 1 ∧ c • (w:CV) = (z:CV) := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change Projectivization.mk ℂ (z:CV) _ = Projectivization.mk ℂ (w:CV) _ at he
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
    refine ⟨c, ?_, hc⟩
    have hn := congrArg normSquared hc
    simpa only [normSquared_smul, z.property.1, w.property.1, mul_one] using hn
  · rintro ⟨c, _, hc⟩
    apply Subtype.ext
    change Projectivization.mk ℂ (z:CV) _ = Projectivization.mk ℂ (w:CV) _
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,hc⟩

def unitRepresentative (q : Q3) : UnitQuadric := project_surjective q |>.choose
lemma project_unitRepresentative (q : Q3) : project (unitRepresentative q) = q :=
  (project_surjective q).choose_spec

lemma phase_map_respects (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hphase : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (z w : UnitQuadric) (hzw : project z = project w) :
    project ⟨F z,hF z⟩ = project ⟨F w,hF w⟩ := by
  obtain ⟨c,hc,he⟩ := (project_eq_iff_phase z w).mp hzw
  apply (project_eq_iff_phase _ _).mpr
  exact ⟨c,hc, (hphase w c hc).symm.trans (congrArg F he)⟩

/-- Descent through the actual circle quotient, proved from its actual fibers. -/
def descend (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z)) (q : Q3) : Q3 :=
  project ⟨F (unitRepresentative q),hF _⟩

lemma descend_project (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hphase : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (z : UnitQuadric) : descend F hF (project z) = project ⟨F z,hF z⟩ :=
  phase_map_respects F hF hphase _ z (project_unitRepresentative (project z))

def descendEquiv (F G : CV → CV)
    (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hG : ∀ z : UnitQuadric, IsUnitQuadric (G z))
    (hFp : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (hGp : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → G (c • (z:CV)) = c • G z)
    (hGF : ∀ z : UnitQuadric, G (F z) = z) (hFG : ∀ z : UnitQuadric, F (G z) = z) : Q3 ≃ Q3 where
  toFun := descend F hF
  invFun := descend G hG
  left_inv q := by
    obtain ⟨z,rfl⟩ := project_surjective q
    rw [descend_project F hF hFp, descend_project G hG hGp]
    exact congrArg project (Subtype.ext (hGF z))
  right_inv q := by
    obtain ⟨z,rfl⟩ := project_surjective q
    rw [descend_project G hG hGp, descend_project F hF hFp]
    exact congrArg project (Subtype.ext (hFG z))

end ArnoldCounterexample.Quadric

end

end OAI
