import Mathlib
import OAI.Probability.SKGap.Stability.RootDiagonalTransfer

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}
local instance matrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma continuous_joint_tapField (j : ℝ) :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × Field n) × Field n=>tapField j p.1.1 p.1.2 p.2) := by
  unfold tapField onsager overlap magnetization
  fun_prop

lemma rootBad_iff_unplanted (j A ε c ρ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h ↔ ∃ y : Field n,vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) ∧
      (J-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c := by
  simp only [rootBad,badFieldSet,mem_ofPred_eq,plantedInteraction,sub_add_cancel]

lemma isClosed_bounded_rootBad (j A ε c ρ : ℝ) (m : ℕ) :
    IsClosed {p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
      vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
      (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
  let X := ↥(Metric.closedBall (0 : Field n) m)
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Field n) m)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × Field n)) :=
    {p | vectorNorm (tapField j p.2.1 p.2.2 p.1) ≤ ρ*sqrt (n:ℝ) ∧
      (p.2.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),(p.1:Field n))∈badFieldSet n j A ε c}
  have hy : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × Field n)=>(p.1:Field n)) :=
    continuous_subtype_val.comp continuous_fst
  have ht := (continuous_joint_tapField (n:=n) j).comp (continuous_snd.prodMk hy)
  have hS : IsClosed S := (isClosed_le ((continuous_vectorNorm n).comp ht) continuous_const).inter
    ((isClosed_badFieldSet n j A ε c).preimage
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk hy))
  have hp := isClosedMap_snd_of_compactSpace S hS
  convert hp using 1
  ext p
  constructor
  · rintro ⟨y,hy,hr,hb⟩
    exact ⟨(⟨y,hy⟩,p),⟨hr,hb⟩,rfl⟩
  · rintro ⟨⟨y,p⟩,⟨hr,hb⟩,rfl⟩
    exact ⟨y,y.property,hr,hb⟩

theorem measurableSet_rootBad (j A ε c ρ : ℝ) :
    MeasurableSet {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2} := by
  have he : {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2}=
      ⋃ m : ℕ,{p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
        vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
        (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
    ext p
    rw [mem_ofPred_eq,rootBad_iff_unplanted]
    constructor
    · rintro ⟨y,hr,hb⟩
      obtain ⟨m,hm⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨m,y,by simpa only [Metric.mem_closedBall,dist_zero_right] using hm,hr,hb⟩
    · intro hp
      obtain ⟨m,y,_,hr,hb⟩ := mem_iUnion.mp hp
      exact ⟨y,hr,hb⟩
  rw [he]
  exact MeasurableSet.iUnion (fun m=>(isClosed_bounded_rootBad j A ε c ρ m).measurableSet)
end SKGap
end
end

end OAI
