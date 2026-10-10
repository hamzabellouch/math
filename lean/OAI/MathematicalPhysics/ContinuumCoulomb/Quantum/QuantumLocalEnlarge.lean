import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateLocality

namespace OAI

/-! Enlarging an explicit operator support introduces only identity factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSupportExtend (S : Finset ι) (u : QMASupportBasis S) : ι → Fin 2 :=
  fun i => if hi : i ∈ S then u ⟨i,hi⟩ else 0

theorem QMALocalOn.mono {S T : Finset ι} (hST : S ⊆ T)
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) : QMALocalOn T A := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨(fun u v => qmaLocalLift S B (qmaSupportExtend T u) (qmaSupportExtend T v)),?_⟩
  ext s t
  have hc (v : ι → Fin 2) :
      (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => v j.val) i.val) =
        (fun i : {i // i ∈ S} => v i.val) := by
    funext i
    simp only [qmaSupportExtend,dite_eq_left (hST i.property)]
  change B (fun i => s i.val) (fun i => t i.val)*
      (if (fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val) then 1 else 0) =
    (B (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => s j.val) i.val)
      (fun i : {i // i ∈ S} => qmaSupportExtend T (fun j => t j.val) i.val)*
      (if (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => s j.val) i.val) =
          (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => t j.val) i.val) then 1 else 0))*
      (if (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val) then 1 else 0)
  rw [hc,hc]
  by_cases hr : (fun i : {i // i ∉ T} => s i.val) = (fun i : {i // i ∉ T} => t i.val)
  · have he :
        ((fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => s j.val) i.val) =
          (fun i : {i // i ∉ S} => qmaSupportExtend T (fun j => t j.val) i.val)) ↔
        ((fun i : {i // i ∉ S} => s i.val) = (fun i : {i // i ∉ S} => t i.val)) := by
      constructor
      · intro h
        funext i
        by_cases hi : i.val ∈ T
        · simpa only [qmaSupportExtend,dite_eq_left hi] using congrFun h i
        · exact congrFun hr ⟨i.val,hi⟩
      · intro h
        funext i
        by_cases hi : i.val ∈ T
        · simpa only [qmaSupportExtend,dite_eq_left hi] using congrFun h i
        · simp only [qmaSupportExtend,dite_eq_right hi]
    simp only [ite_eq_left hr,mul_one,he]
  · have hs : (fun i : {i // i ∉ S} => s i.val) ≠ (fun i : {i // i ∉ S} => t i.val) := by
      intro h
      apply hr
      funext i
      exact congrFun h ⟨i.val,fun hi => i.property (hST hi)⟩
    rw [ite_eq_right hr,ite_eq_right hs,mul_zero,mul_zero]

end ContinuumCoulomb

end

end OAI
