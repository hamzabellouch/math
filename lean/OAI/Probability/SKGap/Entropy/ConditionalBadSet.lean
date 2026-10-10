import Mathlib
import OAI.Probability.SKGap.Localization.ScalarParametersJoined

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def plantedInteraction {n : ℕ} (j : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  W+(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1)

def badFieldSet (n : ℕ) (j A ε c : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p | ∃ a : Fin n → ℝ, (∀ i,a i ∈ Icc 0 A) ∧
    (∑ i,(a i-spinVariance p.2 i)^2) ≤ ε^2*(n:ℝ) ∧
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖=1 ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.1) p.2 a) x.ofLp ≤ c}

lemma continuous_fieldHessian {n : ℕ} (j : ℝ) :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) × (Fin n → ℝ)=>
      fieldHessian j p.1.1 p.1.2 p.2) := by
  unfold fieldHessian hessianCore onsager overlap magnetization
  fun_prop

lemma isClosed_badFieldSet (n : ℕ) (j A ε c : ℝ) : IsClosed (badFieldSet n j A ε c) := by
  let X := ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : CompactSpace ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) :=
    {p | (∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2) ≤ ε^2*(n:ℝ) ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1) (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp ≤ c}
  have ha (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.1:Fin n → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hx (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n=>ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hy (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      tanh (p.2.2 i)) := continuous_tanh.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        ∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2)
        (g := fun _ => ε^2*(n:ℝ)) (by
        apply continuous_finsetSum
        intro i _
        exact ((ha i).sub (continuous_const.sub ((hy i).pow 2))).pow 2) continuous_const
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1)
          (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp) (g := fun _=>c) (by
        dsimp [X,quadraticForm,fieldHessian,hessianCore,plantedInteraction,onsager,overlap,magnetization]
        apply continuous_finsetSum; intro i _
        apply continuous_finsetSum; intro k _
        apply Continuous.mul _ (hx k)
        apply Continuous.mul (hx i)
        apply Continuous.add continuous_const
        apply Continuous.mul _ (Real.continuous_sqrt.comp (ha k))
        apply Continuous.mul (Real.continuous_sqrt.comp (ha i))
        exact (((continuous_const.mul (continuous_const.sub
          ((continuous_finsetSum _ (fun l _ => (hy l).pow 2)).div_const _))).mul continuous_const).sub
          ((by fun_prop : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) => p.2.1 i k)).add continuous_const)).sub
          (((continuous_const.mul (hy i))).mul (hy k))) continuous_const
  have hproj := isClosedMap_snd_of_compactSpace S hS
  convert hproj using 1
  ext p
  constructor
  · rintro ⟨a,ha,hclose,x,hx,hquad⟩
    have ha' : a ∈ Icc (0 : Fin n → ℝ) (fun _=>A) := ⟨fun i=>(ha i).1,fun i=>(ha i).2⟩
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ⟨((⟨a,ha'⟩,⟨x,hx'⟩),p),⟨hclose,hquad⟩,rfl⟩
  · rintro ⟨⟨⟨a,x⟩,p'⟩,hS,rfl⟩
    exact ⟨a,fun i=>⟨a.2.1 i,a.2.2 i⟩,hS.1,x,by simpa only [Metric.mem_sphere,dist_zero_right] using x.2,hS.2⟩

end SKGap
end
end

end OAI
