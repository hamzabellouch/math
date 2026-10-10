import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Cells
import OAI.Combinatorics.HoneycombCorridor.RationalPotential

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def directedCurrent (q : EdgeIndex → ℚ) (g : Germ) : ℚ :=
  (dartSign g : ℚ) * q (edgeOf g)

def ConservedCurrent (q : EdgeIndex → ℚ) : Prop :=
  ∀ v : Vertex, ∑ k : Fin 3, directedCurrent q (v,k) = 0

@[simp] theorem directedCurrent_reverse (q : EdgeIndex → ℚ) (g : Germ) :
    directedCurrent q (reverseGerm g) = -directedCurrent q g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [directedCurrent,dartSign,edgeOf,reverseGerm,neighbor]

@[simp] theorem directedCurrent_advance (q : EdgeIndex → ℚ) (g : Germ) (b : Bool) :
    directedCurrent q (advance g b) = -directedCurrent q (g.1,outgoingSlot g b) := by
  have h := directedCurrent_reverse q (advance g b)
  rw [reverseGerm_advance] at h
  linarith

theorem orientedFlow_zero_iff (q : EdgeIndex →₀ ℤ) (g : Germ) :
    orientedFlow q g = 0 ↔ q (edgeOf g) = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [orientedFlow_up,orientedFlow_down,edgeOf]

theorem directedCurrent_cast (q : EdgeIndex →₀ ℤ) (g : Germ) :
    directedCurrent (fun e => (q e : ℚ)) g = (orientedFlow q g : ℚ) := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [directedCurrent,dartSign,orientedFlow_up,orientedFlow_down,edgeOf]

theorem local_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (b : Bool) (hl : LocalContour p g b) :
    directedCurrent q (advance g b) = directedCurrent q g ∧
      ∀ k : Fin 3, directedCurrent q (g.1,k) =
        -directedCurrent q g * (orientedFlow p (g.1,k) : ℚ) := by
  have hz (k : Fin 3) :
      (if k = outgoingSlot g b then (1 : ℤ) else 0) -
        (if k = g.2 then 1 else 0) = 0 → directedCurrent q (g.1,k) = 0 := by
    intro h
    have h0 : orientedFlow p (g.1,k) = 0 := (hl k).trans h
    have he := hs (edgeOf (g.1,k)) ((orientedFlow_zero_iff p _).mp h0)
    simp [directedCurrent,he]
  have hsum := hq g.1
  rw [directedCurrent_advance]
  constructor
  · rcases g with ⟨v,k⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases k <;> cases b <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith
  · intro k
    rw [hl k]
    rcases g with ⟨v,l⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases l <;> cases b <;> fin_cases k <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith

theorem word_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (w : List Bool) (hw : WordContour p g w) :
    directedCurrent q (terminalGerm g w) = directedCurrent q g ∧
    ∀ e : EdgeIndex, wordFlow g w e ≠ 0 →
      q e = -directedCurrent q g * (p e : ℚ) := by
  induction w generalizing g with
  | nil => simp [terminalGerm,wordFlow]
  | cons b w ih =>
      obtain ⟨hstep,hlocal⟩ := local_contour_current p q hq hs g b hw.1
      obtain ⟨hend,hedge⟩ := ih (advance g b) hw.2
      constructor
      · exact hend.trans hstep
      · intro e he
        by_cases ht : wordFlow (advance g b) w e ≠ 0
        · simpa only [hstep] using hedge e ht
        · have hd : dartFlow (g.1,outgoingSlot g b) e ≠ 0 := by
            simpa only [wordFlow,Finsupp.add_apply,not_not.mp ht,add_zero] using he
          have heq : e = edgeOf (g.1,outgoingSlot g b) := by
            by_contra h
            exact hd (by simp [dartFlow,h])
          subst e
          have h := hlocal (outgoingSlot g b)
          rcases g with ⟨v,k⟩
          cases v <;>
            simp [directedCurrent,dartSign,edgeOf,orientedFlow_up,orientedFlow_down] at h ⊢ <;>
            linarith

theorem simple_cycle_current_scalar (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (q : EdgeIndex → ℚ) (hq : ConservedCurrent q)
    (hs : ∀ e, wordFlow g w e = 0 → q e = 0) :
    ∃ c : ℚ, ∀ e, q e = c * (wordFlow g w e : ℚ) := by
  refine ⟨-directedCurrent q g,?_⟩
  intro e
  by_cases he : wordFlow g w e = 0
  · simp [hs e he,he]
  · exact (word_contour_current _ q hq hs g w
      (simple_closed_word_contour g w hN hc)).2 e he

def faceGradient (r : FaceIndex → ℚ) (e : EdgeIndex) : ℚ :=
  r (leftFace (canonicalDart e)) - r (rightFace (canonicalDart e))

theorem directedCurrent_gradient (r : FaceIndex → ℚ) (g : Germ) :
    directedCurrent (faceGradient r) g = r (leftFace g) - r (rightFace g) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [directedCurrent,faceGradient,dartSign,edgeOf,canonicalDart,upEnd,
      leftFace,rightFace,reverseGerm,neighbor]

theorem gradient_conserved (r : FaceIndex → ℚ) : ConservedCurrent (faceGradient r) := by
  intro v
  simp only [directedCurrent_gradient]
  cases v <;> simp [Fin.sum_univ_succ,leftFace,rightFace,reverseGerm,neighbor] <;> ring

theorem finite_gradient_injective (r s : FaceIndex →₀ ℚ)
    (h : faceGradient r = faceGradient s) : r = s := by
  have hh (i j : ℤ) : r (i+1,j) - s (i+1,j) = r (i,j) - s (i,j) := by
    have he := congrFun h ((i+1,j),0)
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] at he
    linarith
  ext a
  rcases a with ⟨i,j⟩
  let k : ℤ := -(QFlow.faceRadius r : ℤ) - QFlow.faceRadius s - 1
  have hr : r (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box r (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have hs : s (k,j) = 0 := by
    by_contra hz
    have hb := (QFlow.mem_support_in_box s (k,j) (Finsupp.mem_support_iff.mpr hz)).1
    dsimp [k] at hb
    omega
  have he := QFlow.int_function_constant (f := fun i => r (i,j) - s (i,j)) (fun i => hh i j) i k
  rw [hr,hs] at he
  linarith

end PolynomialVacuumBridge.Corridor

end

end OAI
