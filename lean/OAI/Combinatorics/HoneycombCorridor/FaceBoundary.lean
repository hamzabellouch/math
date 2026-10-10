import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Convexity

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def OnFaceBoundary (S : Finset FaceIndex) (g : Germ) : Prop :=
  leftFace g ∉ S ∧ rightFace g ∈ S

noncomputable def faceBoundaryTurn (S : Finset FaceIndex) (g : Germ) : Bool :=
  decide (leftFace (g.1,g.2+1) ∉ S)

theorem faceBoundary_advance (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) :
    OnFaceBoundary S (advance g (faceBoundaryTurn S g)) := by
  classical
  rcases g with ⟨v,k⟩
  have h := hg
  simp only [OnFaceBoundary,rightFace_prev] at h
  unfold faceBoundaryTurn
  by_cases ht : leftFace (v,k+1) ∈ S
  · simp only [ht,not_true_eq_false,decide_false]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]
  · simp only [ht,not_false_eq_true,decide_true]
    cases v <;> fin_cases k <;>
      simp_all [OnFaceBoundary,advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor]

theorem faceBoundary_germ_unique (S : Finset FaceIndex) (v : Vertex) (k l : Fin 3)
    (hk : OnFaceBoundary S (v,k)) (hl : OnFaceBoundary S (v,l)) : k = l := by
  simp only [OnFaceBoundary,rightFace_prev] at hk hl
  fin_cases k <;> fin_cases l <;> norm_num at hk hl ⊢ <;> tauto

theorem faceBoundary_vertex_mem (S : Finset FaceIndex) (g : Germ)
    (hg : OnFaceBoundary S g) : g.1 ∈ cellVertices S := by
  apply (mem_cellVertices _ _).mpr
  exact ⟨g.2+2,by simpa only [rightFace_prev] using
    (show rightFace (g.1,g.2) ∈ S from hg.2)⟩

abbrev FaceBoundary (S : Finset FaceIndex) := {g : Germ // OnFaceBoundary S g}

noncomputable instance faceBoundaryFinite (S : Finset FaceIndex) : Finite (FaceBoundary S) := by
  let f : FaceBoundary S → (cellVertices S) × Fin 3 :=
    fun g => (⟨g.val.1,faceBoundary_vertex_mem S g.val g.property⟩,g.val.2)
  apply Finite.of_injective f
  intro g h he
  apply Subtype.ext
  have hv := congrArg (fun x : (cellVertices S) × Fin 3 => (x.1.val,x.2)) he
  exact hv

noncomputable def faceBoundaryNext (S : Finset FaceIndex) (g : FaceBoundary S) : FaceBoundary S :=
  ⟨advance g.val (faceBoundaryTurn S g.val),faceBoundary_advance S _ g.property⟩

theorem faceBoundary_vertex_injective (S : Finset FaceIndex) :
    Function.Injective (fun g : FaceBoundary S => g.val.1) := by
  intro ⟨⟨v,k⟩,hk⟩ ⟨⟨u,l⟩,hl⟩ he
  dsimp at he
  subst u
  have := faceBoundary_germ_unique S v k l hk hl
  subst l
  rfl

theorem faceBoundaryNext_injective (S : Finset FaceIndex) :
    Function.Injective (faceBoundaryNext S) := by
  intro g h he
  apply faceBoundary_vertex_injective S
  have hval := congrArg Subtype.val he
  have hv := congrArg (fun d : Germ => neighbor d.1 d.2) hval
  simpa only [faceBoundaryNext,advance,neighbor_neighbor] using hv

noncomputable def faceBoundaryWord (S : Finset FaceIndex) (g : FaceBoundary S) : ℕ → List Bool
  | 0 => []
  | n+1 => faceBoundaryTurn S g.val :: faceBoundaryWord S (faceBoundaryNext S g) n

theorem faceBoundaryWord_length (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    (faceBoundaryWord S g n).length = n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [faceBoundaryWord,ih]

theorem faceBoundaryWord_terminal (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    terminalGerm g.val (faceBoundaryWord S g n) = ((faceBoundaryNext S)^[n] g).val := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [faceBoundaryWord,terminalGerm,Function.iterate_succ_apply]
    exact ih (faceBoundaryNext S g)

theorem faceBoundaryWord_traced (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    traced g.val (faceBoundaryWord S g n) =
      List.ofFn (fun i : Fin n => ((faceBoundaryNext S)^[i.val] g).val.1) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    simp only [faceBoundaryWord,traced,List.ofFn_succ,Fin.val_zero,Function.iterate_zero,
      id_eq,Fin.val_succ,Function.iterate_succ_apply]
    congr 1
    exact ih (faceBoundaryNext S g)

theorem faceBoundary_closed_word (S : Finset FaceIndex) (g : FaceBoundary S) :
    ∃ n : ℕ, 0 < n ∧ (traced g.val (faceBoundaryWord S g n)).Nodup ∧
      terminalGerm g.val (faceBoundaryWord S g n) = g.val := by
  let n := Function.minimalPeriod (faceBoundaryNext S) g
  refine ⟨n,Function.minimalPeriod_pos_of_mem_periodicPts
    ((faceBoundaryNext_injective S).mem_periodicPts g),?_,?_⟩
  · rw [faceBoundaryWord_traced,List.nodup_ofFn]
    intro i j he
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
    exact faceBoundary_vertex_injective S he
  · rw [faceBoundaryWord_terminal,Function.iterate_minimalPeriod]

end PolynomialVacuumBridge.Corridor

end

end OAI
