import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ReadUnary

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

theorem bits_injective : Function.Injective bits := by
  intro I J he
  have h := congrArg readInput he
  rw [readInput_code,readInput_code] at h
  simp only [Option.some.injEq,Prod.mk.injEq] at h
  obtain ⟨hn,hk,hc,hf,hd⟩ := h
  cases I with
  | mk n d D F k hF hkpos hcover hnneg hself hsym htri =>
    cases J with
    | mk n' d' D' F' k' hF' hkpos' hcover' hnneg' hself' hsym' htri' =>
      dsimp at hn hk hc hf hd
      subst n'
      subst k'
      have hD : D = D' := by
        apply Finset.ext
        intro i
        have h := congrFun (List.ofFn_injective hc) i
        simpa only [decide_eq_decide] using h
      have hF : F = F' := by
        apply Finset.ext
        intro i
        have h := congrFun (List.ofFn_injective hf) i
        simpa only [decide_eq_decide] using h
      have hd' : d = d' := by
        funext i
        exact List.ofFn_injective (congrFun (List.ofFn_injective hd) i)
      subst D'
      subst F'
      subst d'
      rfl

end MetricKMedianRecovery.RationalMetricInput
namespace MetricKMedianRecovery.RationalMetricInput

def maskSet (n : ℕ) (l : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => l[i.val]?.getD false = true)

def matrixData (n : ℕ) (l : List (List ℚ)) (i j : Fin n) : ℚ :=
  ((l[i.val]?.getD [])[j.val]?).getD 0

def validate (n k : ℕ) (D F : List Bool) (rows : List (List ℚ)) : Option RationalMetricInput :=
  let clients := maskSet n D
  let facilities := maskSet n F
  let distance := matrixData n rows
  if h : facilities.Nonempty ∧ 0 < k ∧ clients ∪ facilities = Finset.univ ∧
      (∀ x y, 0 ≤ distance x y) ∧ (∀ x, distance x x = 0) ∧
      (∀ x y, distance x y = distance y x) ∧
      (∀ x y z, distance x z ≤ distance x y + distance y z) then
    some ⟨n,distance,clients,facilities,k,h.1,h.2.1,h.2.2.1,h.2.2.2.1,
      h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
  else none

def decodeInput (l : List Bool) : Option RationalMetricInput := do
  let (n,k,D,F,rows) ← readInput l
  validate n k D F rows

lemma maskSet_ofFn (n : ℕ) (S : Finset (Fin n)) :
    maskSet n (List.ofFn (fun i => decide (i ∈ S))) = S := by
  ext i
  simp [maskSet]

lemma matrixData_ofFn (n : ℕ) (d : Fin n → Fin n → ℚ) :
    matrixData n (List.ofFn (fun i => List.ofFn (d i))) = d := by
  funext i j
  simp only [matrixData,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,
    dite_eq_left j.isLt]

lemma validate_code (I : RationalMetricInput) : validate I.pointCount I.budget
    (List.ofFn (fun i => decide (i ∈ I.clients)))
    (List.ofFn (fun i => decide (i ∈ I.facilities)))
    (List.ofFn (fun i => List.ofFn (I.distance i))) = some I := by
  unfold validate
  simp only [maskSet_ofFn,matrixData_ofFn]
  rw [dite_eq_left (show I.facilities.Nonempty ∧ 0 < I.budget ∧
    I.clients ∪ I.facilities = Finset.univ ∧ (∀ x y, 0 ≤ I.distance x y) ∧
    (∀ x, I.distance x x = 0) ∧ (∀ x y, I.distance x y = I.distance y x) ∧
    (∀ x y z, I.distance x z ≤ I.distance x y + I.distance y z) from
    ⟨I.facilities_nonempty,I.budget_pos,I.covered,I.distance_nonneg,I.distance_self,
      I.distance_symm,I.distance_triangle⟩)]

lemma decodeInput_code (I : RationalMetricInput) : decodeInput I.bits = some I := by
  unfold decodeInput
  rw [readInput_code]
  exact validate_code I

end MetricKMedianRecovery.RationalMetricInput

end OAI
