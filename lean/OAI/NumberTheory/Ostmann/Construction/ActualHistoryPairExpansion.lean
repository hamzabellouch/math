import OAI.NumberTheory.Ostmann.Construction.DiagonalEnvironmentTerms
import OAI.NumberTheory.Ostmann.Construction.SmoothHistoryFactor

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate FourierTransform Classical
namespace Ostmann.Construction

def actualHistoryWeight (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (X G : ℝ) (g : (p : ℕ)→ZMod p→ℂ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) : ℂ :=
  (decodeHistory sources seed V l a c).supportedWeight V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G

theorem actualCoefficient_eq_histories (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (X G : ℝ) (g : (p : ℕ)→ZMod p→ℂ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ) (a : State) :
    actualCoefficient sources seed V X G g bins outside l a=
      ∑c : HistoryChoices sources seed V l,(choicesMass sources seed V l c:ℂ)*
        actualHistoryWeight sources seed V X G g bins outside l a c := rfl

theorem history_pair_compensation_factor (X G : ℝ)
    (g : (p : ℕ)→ZMod p→ℂ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) {l : ℕ} (h k : History l) :
    h.weight (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
        Ostmann.smoothPartition G *
      conj (k.weight (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
        Ostmann.smoothPartition G)=
    ((h.compensationProduct:ℂ)*(k.compensationProduct:ℂ))*
      (smoothHistoryScalar X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) bins outside
          Ostmann.smoothPartition G h *
        conj (smoothHistoryScalar X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) bins outside
          Ostmann.smoothPartition G k))*
      (h.leafProduct (spectatorFactor g outside)*conj (k.leafProduct (spectatorFactor g outside))) := by
  rw [history_weight_eq_compensation_smooth_spectator,
    history_weight_eq_compensation_smooth_spectator]
  simp only [map_mul,map_natCast]
  ring

theorem finite_weighted_pair_expansion {α β : Type*} [Fintype α] [Fintype β]
    (w : α→ℝ) (u : β→ℝ) (F : α→ℂ) (G : β→ℂ) :
    (∑a,(w a:ℂ)*F a)*conj (∑b,(u b:ℂ)*G b)=
      ∑a,∑b,((w a*u b:ℝ):ℂ)*F a*conj (G b) := by
  simp only [map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,Finset.mul_sum,Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (seed : List SourceSlot)
    (l : ℕ) (B Δ : ℝ)
local notation "T" => Template.remainder (l+1) (Template.current seed l)
local notation "U" => Template.extracted (l+1) (Template.current seed l)

theorem correctedCounterpartTerm_sum {ι : Type*} [Fintype ι]
    (u : SourceAssignment C.sources U) (x : RemainingSample C.sources T C.giant)
    (F : ι→RemainingSample C.sources T C.giant→ℂ) (e : Equiv.Perm (RemainingIndex T)) :
    C.correctedCounterpartTerm seed l B Δ u x (fun y => ∑i,F i y) e=
      ∑i,C.correctedCounterpartTerm seed l B Δ u x (F i) e := by
  unfold correctedCounterpartTerm
  split_ifs <;> simp only [Finset.mul_sum,Finset.sum_const_zero]

theorem correctedCounterpartTerm_cmul (u : SourceAssignment C.sources U)
    (x : RemainingSample C.sources T C.giant) (F : RemainingSample C.sources T C.giant→ℂ)
    (e : Equiv.Perm (RemainingIndex T)) (z : ℂ) :
    C.correctedCounterpartTerm seed l B Δ u x (fun y => z*F y) e=
      z*C.correctedCounterpartTerm seed l B Δ u x F e := by
  unfold correctedCounterpartTerm
  split_ifs <;> ring

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
