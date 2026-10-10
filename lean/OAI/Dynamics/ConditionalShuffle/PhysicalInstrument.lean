import OAI.Dynamics.ConditionalShuffle.PhysicalOne

namespace OAI

noncomputable section
namespace Revealed.Physical
open scoped Classical
open Thorp Thorp.Conditional Revealed.Split Revealed.Instrument
variable {ι α : Type} [fintype_ι : Fintype ι] [fintype_α : Fintype α] [decidableEq_α : DecidableEq α]

def instrument (d : ℕ) : Data (Outside ι α (Position d)) (Outside ι α (Position d))
    (Equiv.Perm α) (Coins d) where
  obs e c := nextOutside e (step d c)
  inc e c := increment e (step d c)
  next _ s := s

lemma physical_base (d : ℕ) (L : Sum ι α ≃ Position d) (t : ℕ) (ω : History d t) :
    base (instrument d) (Split.outside L) t (observed (instrument d) (Split.outside L) t ω) =
      Split.outside (L.trans (run d t ω)) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  induction t with
  | zero => simp only [base, run_zero]; rfl
  | succ t ih =>
      simp only [base, observed, Fin.init_snoc, Fin.snoc_last]
      change nextOutside (base (instrument d) (Split.outside L) t
        (observed (instrument d) (Split.outside L) t (Fin.init ω))) (step d (ω (Fin.last t))) = _
      rw [ih, ← outside_post, run_succ]
      rfl

lemma physical_group (d : ℕ) (L : Sum ι α ≃ Position d) (t : ℕ) (ω : History d t) :
    groupRun (instrument d) (Split.outside L) t ω * assignment L =
      assignment (L.trans (run d t ω)) := by
  induction t with
  | zero => simp only [groupRun, run_zero, one_mul]; rfl
  | succ t ih =>
      simp only [groupRun]
      change (increment (base (instrument d) (Split.outside L) t
        (observed (instrument d) (Split.outside L) t (Fin.init ω))) (step d (ω (Fin.last t))) *
        groupRun (instrument d) (Split.outside L) t (Fin.init ω)) * assignment L = _
      rw [mul_assoc, ih, physical_base, ← assignment_post, run_succ]
      rfl

def fullPath {d t : ℕ} (e : Outside ι α (Position d))
    (p : Fin t → Outside ι α (Position d)) : Fin (t+1) → ι → Position d :=
  Fin.cons e.val (fun i => (p i).val)

lemma fullPath_injective {d t : ℕ} (e : Outside ι α (Position d)) :
    Function.Injective (fullPath (t:=t) e) := by
  let retained_fintype_ι := fintype_ι
  let retained_fintype_α := fintype_α
  let retained_decidableEq_α := decidableEq_α
  intro p q h
  funext i
  apply Subtype.ext
  exact (congrFun h i.succ)

lemma physical_path (d : ℕ) (L : Sum ι α ≃ Position d) (t : ℕ) (ω : History d t) :
    fullPath (Split.outside L) (observed (instrument d) (Split.outside L) t ω) = splitPath L t ω := by
  induction t with
  | zero =>
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
  | succ t ih =>
      rw [show ω = Fin.snoc (Fin.init ω) (ω (Fin.last t)) from (Fin.snoc_init_self ω).symm]
      simp only [observed, Fin.init_snoc, Fin.snoc_last, fullPath]
      have he := Fin.comp_snoc (fun o : Outside ι α (Position d) => o.val)
        (observed (instrument d) (Split.outside L) t (Fin.init ω))
        ((instrument d).obs (base (instrument d) (Split.outside L) t
          (observed (instrument d) (Split.outside L) t (Fin.init ω))) (ω (Fin.last t)))
      dsimp only [Function.comp_def] at he
      rw [he, Fin.cons_snoc_eq_snoc_cons, ← fullPath, ih]
      simp only [splitPath, exposedPath_snoc]
      congr 1
      rw [physical_base]
      change (Split.outside (((sectionFrame (Split.outside (L.trans (run d t (Fin.init ω))))).trans
        (step d (ω (Fin.last t)))))).val = _
      funext i
      change step d (ω (Fin.last t))
        (sectionFrame (Split.outside (L.trans (run d t (Fin.init ω)))) (.inl i)) = _
      rw [sectionFrame_spec]
      rfl

lemma physical_group_frame (d : ℕ) (e : Outside ι α (Position d)) (t : ℕ) (ω : History d t) :
    groupRun (instrument d) e t ω = assignment ((sectionFrame e).trans (run d t ω)) := by
  simpa only [outside_sectionFrame, assignment_sectionFrame, mul_one] using
    physical_group d (sectionFrame e) t ω

lemma physical_path_frame (d : ℕ) (e : Outside ι α (Position d)) (t : ℕ) (ω : History d t) :
    fullPath e (observed (instrument d) e t ω) = splitPath (sectionFrame e) t ω := by
  simpa only [outside_sectionFrame] using physical_path d (sectionFrame e) t ω

lemma physical_kernel_dichotomy [Nontrivial α] (d : ℕ)
    (e s : Outside ι α (Position (d + 1))) :
    Trim.signDichotomy (kernel (instrument (d + 1)) e s) :=
  physical_step_signDichotomy d (sectionFrame e) s

end Revealed.Physical

end

end OAI
