import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalCubeTerm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreCoefficient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFreeCubeIndex

namespace OAI

/-! The concrete angular transform with the free cube variable separated.
Both its coefficient bound and its absolutely convergent sum are proved. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def cubicThetaCommonArgument (x : CubicThetaCommonIndex) : MetaplecticDualArgument :=
  ⟨cubicThetaCommonNumerator x,(cubicThetaCommonCoordinates x).ne_zero⟩

lemma cubicThetaCommonArgument_injective : Function.Injective cubicThetaCommonArgument := by
  intro x y he
  exact cubicThetaCommonNumerator_injective (congrArg Subtype.val he)

lemma cubicThetaLocalDualTerm_reindex {r : Eisenstein} (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ) :
    (∑' n,cubicThetaLocalDualTerm r rev k W σ X n)=
      ∑' x : CubicThetaCommonIndex,
        cubicThetaLocalDualTerm r rev k W σ X (cubicThetaCommonArgument x) := by
  apply (cubicThetaCommonArgument_injective.tsum_eq ?_).symm
  intro n hn
  have ha : cubicThetaCommonCuspCoefficient n.val≠0 := by
    intro h
    exact hn (by simp [cubicThetaLocalDualTerm,h])
  obtain ⟨x,hx⟩ := (cubicThetaCommonNumerator_range n.val).mpr
    (cubicThetaCommonCuspCoefficient_support n.property ha)
  exact ⟨x,Subtype.ext hx⟩

lemma cubicThetaCoreCoefficient_index (r : Eisenstein) (x : CubicThetaCoreIndex r) :
    cubicThetaCoreCoefficient r (cubicThetaCommonArgument x.val)=
      cubicThetaCommonTau (cubicThetaCommonNumerator x.val) := by
  unfold cubicThetaCoreCoefficient
  apply ite_eq_left
  exact ⟨cubicThetaCommonCoordinates x.val,x.property⟩

lemma cubicThetaFreeCubeJoin_argument (r : Eisenstein)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x)=
      cubicThetaDualCube (x.2.val:Eisenstein) x.2.val.property
        (cubicThetaCommonArgument x.1.val) := by
  apply Subtype.ext
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3
  unfold cubicThetaCommonNumerator cubicThetaFreeCubeJoin
  ring

def cubicThetaFreeLocalDualTerm (r : Eisenstein) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) : ℂ :=
  theta (cubicThetaCircleOrder rev k) (cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x))*
    (cubicThetaCoreCoefficient r (cubicThetaCommonArgument x.1.val)*
      metaplecticLocalCoefficient r (cubicThetaCommonArgument x.1.val))/
        ((‖cubicThetaFrequency (cubicThetaCommonNumerator x.1.val)‖^2*
          norm (x.2.val:Eisenstein)^(5/2:ℝ):ℝ):ℂ)*
    metaplecticTransform (cubicThetaCircleOrder (!rev) k) W σ
      (cubicThetaDualScale r (X/27)*
        ‖cubicThetaFrequency (cubicThetaCommonNumerator x.1.val)‖^2*
          norm (x.2.val:Eisenstein)^3)

lemma cubicThetaFreeLocalDualTerm_eq {r : Eisenstein} (hr : primary r)
    (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (σ X : ℝ)
    (x : CubicThetaCoreIndex r × CubicThetaFreeArgument r) :
    cubicThetaLocalDualTerm r rev k W σ X
      (cubicThetaCommonArgument (cubicThetaFreeCubeJoin r x))=
        cubicThetaFreeLocalDualTerm r rev k W σ X x := by
  rw [cubicThetaFreeCubeJoin_argument,cubicThetaLocalDualTerm_cube hr x.2.val.property x.2.property]
  unfold cubicThetaFreeLocalDualTerm
  rw [cubicThetaCoreCoefficient_index]
  have he := congrArg Subtype.val (cubicThetaFreeCubeJoin_argument r x)
  change cubicThetaCommonNumerator (cubicThetaFreeCubeJoin r x)=
    cubicThetaCommonNumerator x.1.val*(x.2.val:Eisenstein)^3 at he
  rw [he]
  rfl

theorem cubicThetaFree_voronoi {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    [Fintype (Residues r)] (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 0<σ) (hX : 0<X) :
    Summable (cubicThetaFreeLocalDualTerm r rev k W σ X) ∧
    ((((3^(5/2:ℝ):ℝ):ℂ)*theta (cubicThetaCircleOrder (!rev) k) lambdaE)*
      ((Real.sqrt (norm r):ℂ)*gauss r))*
        metaplecticRawCompleted r (cubicThetaCircleOrder (!rev) k) W X=
    (cubicThetaLevelAngularRoot r rev k)⁻¹*cubicThetaDualPrefactor r*
      ∑' x,cubicThetaFreeLocalDualTerm r rev k W σ X x := by
  obtain ⟨hS,hE⟩ := cubicThetaLocal_voronoi hr hs rev hk W hW hpos hsm hσ hX
  have hI := hS.comp_injective cubicThetaCommonArgument_injective
  have hJ := hI.comp_injective (cubicThetaFreeCubeJoin_injective (primary_ne_zero hr))
  have he := cubicThetaFreeLocalDualTerm_eq hr rev k W σ X
  refine ⟨hJ.congr he,?_⟩
  rw [cubicThetaLocalDualTerm_reindex,
    cubicTheta_free_cube_tsum (primary_ne_zero hr)] at hE
  simpa only [he] using hE

end CubicFirstMoment

end

end OAI
