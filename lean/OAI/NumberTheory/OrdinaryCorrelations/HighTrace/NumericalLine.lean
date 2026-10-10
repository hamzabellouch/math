import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GeometryRetained
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BoundedLists

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}

structure NumericalLine (D : S.DivisorFamily B τ C₀) (h ℓ : ℕ) where
  line : ClosedLine h ℓ
  labels : ∀ i, line.label i ∈ D.members

namespace NumericalLine
def toEmpty (w : NumericalLine D h ℓ) : LineList D 0 h ℓ 0 :=
  ⟨w.line,w.labels,[],by simp⟩

lemma toEmpty_injective : Function.Injective (toEmpty : NumericalLine D h ℓ → _) := by
  intro w v he
  have hl := congrArg LineList.line he
  cases w
  cases v
  simp only [toEmpty] at hl
  cases hl
  rfl

instance : Finite (NumericalLine D h ℓ) := Finite.of_injective toEmpty toEmpty_injective
noncomputable instance : Fintype (NumericalLine D h ℓ) := Fintype.ofFinite _

noncomputable def listEquiv : (w : NumericalLine D h ℓ) ×
    ↥(boundedLists (AttachedSpec w.line D L) t) ≃ LineList D L h ℓ t where
  toFun x := ⟨x.1.line,x.1.labels,x.2.val,(mem_boundedLists _ _).mp x.2.property⟩
  invFun x := ⟨⟨x.line,x.labels⟩,⟨x.primitives,(mem_boundedLists _ _).mpr x.length_le⟩⟩
  left_inv x := by cases x with | mk w l => cases w; cases l; rfl
  right_inv x := by cases x; rfl

lemma listEquiv_eval (F : (w : NumericalLine D h ℓ) → List (AttachedSpec w.line D L) → ℝ)
    (x : (w : NumericalLine D h ℓ) × ↥(boundedLists (AttachedSpec w.line D L) t)) :
    F x.1 x.2.val = F ⟨(listEquiv x).line,(listEquiv x).labels⟩ (listEquiv x).primitives := by
  rcases x with ⟨⟨w,hw⟩,⟨l,hl⟩⟩
  rfl

private lemma sum_sigma_instances {α : Type*} {β : α → Type*}
    [Fintype α] [∀ a, Fintype (β a)] (i : Fintype (Sigma β)) (f : Sigma β → ℝ) :
    (∑ a, ∑ b, f ⟨a,b⟩) = @Finset.sum (Sigma β) ℝ _ (@Finset.univ _ i) f := by
  have he : i = Sigma.instFintype := Subsingleton.elim _ _
  rw [he]
  exact (Fintype.sum_sigma f).symm

lemma sum_lists (F : (w : NumericalLine D h ℓ) → List (AttachedSpec w.line D L) → ℝ) :
    (∑ w : NumericalLine D h ℓ, ∑ l ∈ boundedLists (AttachedSpec w.line D L) t, F w l) =
      ∑ x : LineList D L h ℓ t, F ⟨x.line,x.labels⟩ x.primitives := by
  calc
    _ = ∑ w : NumericalLine D h ℓ,
        ∑ l : ↥(boundedLists (AttachedSpec w.line D L) t), F w l.val :=
      sum_congr rfl (fun w _ => (sum_attach _ _).symm)
    _ = ∑ x : (w : NumericalLine D h ℓ) × ↥(boundedLists (AttachedSpec w.line D L) t),
        F x.1 x.2.val := sum_sigma_instances (α:=NumericalLine D h ℓ)
          (β:=fun w => ↥(boundedLists (AttachedSpec w.line D L) t))
          inferInstance (fun x => F x.1 x.2.val)
    _ = _ := Fintype.sum_equiv (listEquiv (D:=D) (L:=L) (t:=t))
          (fun x => F x.1 x.2.val) (fun x => F ⟨x.line,x.labels⟩ x.primitives) (listEquiv_eval F)

def sourceRetained {B τ C₀ : ℝ} {D : (sourceSystem B).DivisorFamily B τ C₀}
    {h ℓ : ℕ} (hh : 0 < h) (K₀ : ℝ) (w : NumericalLine D h ℓ)
    (a : (sourceSystem B).FixedResidues w.line) : Prop :=
  RetainedCountConditions w.line hh a B K₀ ∧ NoFixedForbidden w.line D (pathLength B) a

lemma retained_list_sum_le {B τ C₀ T : ℝ} {D : (sourceSystem B).DivisorFamily B τ C₀}
    {h ℓ : ℕ} (hh : 0 < h) (K₀ : ℝ) (cut : (sourceSystem B).Cutoffs T) (t : ℕ) :
    (∑ w : NumericalLine D h ℓ,
      ∑ l ∈ boundedLists (AttachedSpec w.line D (pathLength B)) t,
        assignedKernelIntegral w.line cut l (sourceRetained hh K₀ w)) ≤
      LineList.retainedSum (D:=D) (L:=pathLength B) (ℓ:=ℓ) (n:=t) cut (LineList.geometryRetained hh K₀) := by
  rw [sum_lists]
  apply sum_le_sum
  intro x _
  exact assignedKernelIntegral_mono x.line cut x.primitives _ _ (fun _ ha => ha.1)

end NumericalLine
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
