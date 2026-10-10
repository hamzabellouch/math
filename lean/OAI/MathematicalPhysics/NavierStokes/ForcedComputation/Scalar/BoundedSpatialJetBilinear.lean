import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetOperators

namespace OAI

/-! The pointwise product as a continuous bilinear operator on finite spatial jets. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open scoped Topology BoundedContinuousFunction

variable (E F G H : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The operator type with its normed-space structure fixed before taking another operator space. -/
def Operator (k : ℕ) := Space E G k →L[ℝ] Space E H k

instance (k : ℕ) : NormedAddCommGroup (Operator E G H k) :=
  inferInstanceAs (NormedAddCommGroup (Space E G k →L[ℝ] Space E H k))

instance (k : ℕ) : NormedSpace ℝ (Operator E G H k) :=
  inferInstanceAs (NormedSpace ℝ (Space E G k →L[ℝ] Space E H k))

def operatorEquiv (k : ℕ) :
    Operator E G H k ≃ₗᵢ[ℝ] (Space E G k →L[ℝ] Space E H k) :=
  LinearIsometryEquiv.refl ℝ _

instance (k : ℕ) : CoeFun (Operator E G H k) (fun _ => Space E G k → Space E H k) :=
  ⟨fun L => operatorEquiv E G H k L⟩

/-- Dependence of the multiplication operator on its coefficient jet is linear and bounded. -/
def bilinearCLM (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H) :
    Space E F k →L[ℝ] Operator E G H k :=
  LinearMap.mkContinuous
    { toFun := fixedBilinear E F G H k B
      map_add' := by
        intro J L
        apply ContinuousLinearMap.ext
        intro K
        apply function_injective E H k
        apply BoundedContinuousFunction.ext
        intro x
        change function E H k (bilinear E F G H k B (J + L) K) x =
          function E H k (bilinear E F G H k B J K + bilinear E F G H k B L K) x
        simp only [function_bilinear, function_add, map_add,
          add_apply]
      map_smul' := by
        intro c J
        apply ContinuousLinearMap.ext
        intro K
        apply function_injective E H k
        apply BoundedContinuousFunction.ext
        intro x
        change function E H k (bilinear E F G H k B (c • J) K) x =
          function E H k (c • bilinear E F G H k B J K) x
        simp only [function_bilinear, function_smul, map_smul, smul_apply] }
    (‖B‖ * (2 : ℝ) ^ k)
    (fun J => by
      change ‖fixedBilinear E F G H k B J‖ ≤ (‖B‖ * (2 : ℝ) ^ k) * ‖J‖
      exact norm_fixedBilinear_le E F G H k B J)

@[simp] theorem bilinearCLM_apply (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H)
    (J : Space E F k) (K : Space E G k) :
    bilinearCLM E F G H k B J K = bilinear E F G H k B J K := rfl

theorem norm_bilinearCLM_le (k : ℕ) (B : F →L[ℝ] G →L[ℝ] H) :
    ‖bilinearCLM E F G H k B‖ ≤ ‖B‖ * (2 : ℝ) ^ k := by
  refine (bilinearCLM E F G H k B).opNorm_le_bound (by positivity) ?_
  intro J
  change ‖fixedBilinear E F G H k B J‖ ≤ (‖B‖ * (2 : ℝ) ^ k) * ‖J‖
  exact norm_fixedBilinear_le E F G H k B J

/-- Joint time continuity of coefficient and unknown is enough for continuity of the source. -/
theorem continuous_bilinear {X : Type*} [TopologicalSpace X] (k : ℕ)
    (B : F →L[ℝ] G →L[ℝ] H) (J : X → Space E F k) (K : X → Space E G k)
    (hJ : Continuous J) (hK : Continuous K) :
    Continuous (fun t => bilinear E F G H k B (J t) (K t)) := by
  convert! (((operatorEquiv E G H k).continuous.comp
    ((bilinearCLM E F G H k B).continuous.comp hJ)).clm_apply hK) using 1

/-- The same continuity statement restricted to a time interval. -/
theorem continuousOn_bilinear {X : Type*} [TopologicalSpace X] (S : Set X) (k : ℕ)
    (B : F →L[ℝ] G →L[ℝ] H) (J : X → Space E F k) (K : X → Space E G k)
    (hJ : ContinuousOn J S) (hK : ContinuousOn K S) :
    ContinuousOn (fun t => bilinear E F G H k B (J t) (K t)) S := by
  convert! (((operatorEquiv E G H k).continuous.comp_continuousOn
    ((bilinearCLM E F G H k B).continuous.comp_continuousOn hJ)).clm_apply hK) using 1

end ForcedComputation.BoundedSpatialJets

end

end OAI
