import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedIdentityClass
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ResolutionCoefficientSequence

namespace OAI

/-! # The connecting maps carry the normalized identity cocycle forward -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable (G : Type) [Group G]

def normalizedIdentityConnecting (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))).homology n ⟶
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy (n + 1)).obj (trivialIntegral G))).homology (n + 1) :=
  (resolutionCoefficientSequence_shortExact (normalizedProjectiveResolution (trivialIntegral G))
    (normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)))).δ
      n (n + 1) rfl

theorem normalizedIdentityConnecting_class (n : ℕ) :
    normalizedIdentityConnecting G n (normalizedIdentityClass (trivialIntegral G) n) =
      normalizedIdentityClass (trivialIntegral G) (n + 1) := by
  let A := trivialIntegral G
  let P := normalizedProjectiveResolution A
  let S := normalizedSyzygySequence ((iteratedNormalizedSyzygy n).obj A)
  let hS := resolutionCoefficientSequence_shortExact P S
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
  have hz : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).X₃.d n (n + 1)))
        (normalizedResolutionProjection A n) = 0 := by
    change (normalizedResolutionComplex A).d (n + 1) n ≫
      normalizedResolutionProjection A n = 0
    exact normalizedResolution_d_projection A n
  have hl : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).g.f n)) (𝟙 (P.complex.X n)) =
        normalizedResolutionProjection A n := by
    change 𝟙 _ ≫ normalizedResolutionProjection A n = normalizedResolutionProjection A n
    exact Category.id_comp _
  have hd : ((forget₂ (ModuleCat ℤ) Ab).map
      ((resolutionCoefficientSequence P S).f.f (n + 1)))
        (normalizedResolutionProjection A (n + 1)) =
      ((forget₂ (ModuleCat ℤ) Ab).map
        ((resolutionCoefficientSequence P S).X₂.d n (n + 1))) (𝟙 (P.complex.X n)) := by
    change normalizedResolutionProjection A (n + 1) ≫
        kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)) =
      (normalizedResolutionComplex A).d (n + 1) n ≫ 𝟙 _
    rw [Category.comp_id, normalizedResolutionComplex_d]
    rfl
  exact hS.δ_apply n (n + 1) rfl (normalizedResolutionProjection A n) hz
    (𝟙 (P.complex.X n)) hl (normalizedResolutionProjection A (n + 1)) hd (n + 2) (by simp)

end PolycyclicRecognition

end

end OAI
