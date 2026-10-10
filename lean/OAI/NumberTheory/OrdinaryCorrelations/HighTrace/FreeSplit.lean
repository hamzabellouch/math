import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvgAdd

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

local instance (w : ClosedLine h ℓ) : DecidableEq (S.FreeIndex w) := Classical.decEq _

def freeSplit (S : PrimeSystem) (w : ClosedLine h ℓ) :
    S.FreeResidues w ≃ S.FreeCoreResidues w × S.FreeCenterResidues w :=
  Equiv.piEquivPiSubtypeProd (fun p : S.FreeIndex w => S.IsCore p.val)
    (fun p => ZMod (p.val:ℕ))

lemma merge_freeSplit (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (bc : S.FreeCoreResidues w × S.FreeCenterResidues w) :
    mergeResidues w a ((S.freeSplit w).symm bc) = (S.splitResidues w).symm (a,bc) := rfl

lemma avg_residual_eq_split (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (F : S.Residues → ℝ) :
    avg (fun c : S.FreeResidues w => F (mergeResidues w a c)) =
      avg (fun bc : S.FreeCoreResidues w × S.FreeCenterResidues w =>
        F ((S.splitResidues w).symm (a,bc))) := by
  rw [avg_equiv (S.freeSplit w)]
  rfl

lemma labelledIndicator_full_list (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (l : List (AttachedSpec w D L)) (c : S.FreeResidues w) :
    labelledIndicator (univ.filter (fun s : AttachedSpec w D L => s.Compatible a))
      AttachedSpec.residualCylinder l c = listIndicator w l (mergeResidues w a c) := by
  have he : (∀ s ∈ l, s ∈ univ.filter (fun s : AttachedSpec w D L => s.Compatible a) ∧
      s.residualCylinder.Holds c) ↔
      ∀ s ∈ l, ∀ p : S.Index, s.spec.ResidueTest p s.vertex (mergeResidues w a c p) := by
    simp only [mem_filter,mem_univ,true_and,← AttachedSpec.fullCylinder_merge,
      AttachedSpec.fullCylinder_holds]
  simp only [labelledIndicator,listIndicator,he]
  split_ifs <;> rfl

noncomputable def allowedIndicator (w : ClosedLine h ℓ) (D : S.DivisorFamily B τ C₀)
    (L : ℕ) (r : S.Residues) : ℝ :=
  if ∀ s : AttachedSpec w D L, ¬s.fullCylinder.Holds r then 1 else 0

lemma allowedIndicator_integer (w : ClosedLine h ℓ) (n : ℤ) :
    allowedIndicator w D L (S.integerResidues n) =
      ∏ i : Fin (ℓ+1), (if VertexAllowed D h L (n+w.offset i) then (1:ℝ) else 0) := by
  simp only [allowedIndicator,all_attachments_integer_iff]
  by_cases hy : ∀ i : Fin (ℓ+1), VertexAllowed D h L (n+w.offset i)
  · rw [ite_eq_left hy]
    symm
    exact prod_eq_one (fun i hi => ite_eq_left (hy i))
  · rw [ite_eq_right hy]
    push Not at hy
    obtain ⟨i,hi⟩ := hy
    symm
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

lemma avoidance_eq_allowed (w : ClosedLine h ℓ) (a : S.FixedResidues w) (c : S.FreeResidues w) :
    (avoidance (residualEvents w D L a) c : ℝ) = allowedIndicator w D L (mergeResidues w a c) := by
  simp only [avoidance,allowedIndicator,residualEvents_avoidance]
  split_ifs <;> norm_num

noncomputable def retainedAllowedIntegral (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) : ℝ :=
  avg (fun a => if G a then |avg (fun c : S.FreeResidues w =>
    S.kernel w cut (mergeResidues w a c) * allowedIndicator w D L (mergeResidues w a c))| else 0)

noncomputable def residualWitnessIntegral (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) (t : ℕ) : ℝ :=
  avg (fun a => if G a then avg (fun c : S.FreeResidues w =>
    |S.kernel w cut (mergeResidues w a c)| * (witnessCount (residualEvents w D L a) t c:ℝ)) else 0)

lemma residualWitnessIntegral_nonneg (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) (t : ℕ) :
    0 ≤ residualWitnessIntegral (D:=D) (L:=L) w cut G t := by
  apply avg_nonneg
  intro a
  split_ifs
  · exact avg_nonneg (fun c => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  · exact le_rfl

private lemma avg_instance_congr {α : Type*} (i j : Fintype α) (f g : α → ℝ)
    (he : f=g) : @avg α i f = @avg α j g := by
  subst g
  cases Subsingleton.elim i j
  rfl

lemma assignedKernelIntegral_binary (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (l : List (AttachedSpec w D L)) (G : S.FixedResidues w → Prop) :
    avg (fun a : S.FixedResidues w => if G a then
      |avg (fun c : S.FreeResidues w => S.kernel w cut (mergeResidues w a c) *
        listIndicator w l (mergeResidues w a c))| else 0) = assignedKernelIntegral w cut l G := by
  unfold assignedKernelIntegral
  apply avg_instance_congr
  funext a
  split_ifs
  · congr 1
    rw [avg_equiv (S.freeSplit w)]
    exact avg_instance_congr _ _ _ _ rfl
  · rfl

lemma conditional_primitive_reduction (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (a : S.FixedResidues w) (ha : NoFixedForbidden w D L a) (t : ℕ) (ht : 1 ≤ t) :
    |avg (fun c : S.FreeResidues w => S.kernel w cut (mergeResidues w a c) *
      allowedIndicator w D L (mergeResidues w a c))| ≤
    ((max 1 ((t*(L*⌈C₀*Real.log B⌉₊+1))^(t*(L*⌈C₀*Real.log B⌉₊+1)+1)):ℕ):ℝ) *
      (∑ l ∈ boundedLists (AttachedSpec w D L) t,
        |avg (fun c : S.FreeResidues w => S.kernel w cut (mergeResidues w a c) *
          listIndicator w l (mergeResidues w a c))|) +
    ((2^(t*(L*⌈C₀*Real.log B⌉₊+1))*
      max 1 ((t*(L*⌈C₀*Real.log B⌉₊+1))^(t*(L*⌈C₀*Real.log B⌉₊+1)+1)):ℕ):ℝ) *
      avg (fun c : S.FreeResidues w => |S.kernel w cut (mergeResidues w a c)| *
        (witnessCount (residualEvents w D L a) t c:ℝ)) := by
  have hr := signed_list_reduction
    (univ.filter (fun s : AttachedSpec w D L => s.Compatible a)) AttachedSpec.residualCylinder
    (residualEvents_proper w a ha) t (L*⌈C₀*Real.log B⌉₊+1) ht (residualEvents_width w a)
    (fun c : S.FreeResidues w => S.kernel w cut (mergeResidues w a c))
  have he : (univ.filter (fun s : AttachedSpec w D L => s.Compatible a)).image
    AttachedSpec.residualCylinder = residualEvents w D L a := rfl
  rw [he] at hr
  simpa only [avoidance_eq_allowed,labelledIndicator_full_list] using hr

theorem primitive_cylinder_reduction (w : ClosedLine h ℓ) {T : ℝ} (cut : S.Cutoffs T)
    (G : S.FixedResidues w → Prop) (hG : ∀ a, G a → NoFixedForbidden w D L a)
    (t : ℕ) (ht : 1 ≤ t) :
    retainedAllowedIntegral (D:=D) (L:=L) w cut G ≤
      (max 1 ((t*(L*⌈C₀*Real.log B⌉₊+1))^(t*(L*⌈C₀*Real.log B⌉₊+1)+1)) : ℕ) *
      (∑ l ∈ boundedLists (AttachedSpec w D L) t, assignedKernelIntegral w cut l G) +
      ((2^(t*(L*⌈C₀*Real.log B⌉₊+1)) *
        max 1 ((t*(L*⌈C₀*Real.log B⌉₊+1))^(t*(L*⌈C₀*Real.log B⌉₊+1)+1)) : ℕ) : ℝ) *
        residualWitnessIntegral (D:=D) (L:=L) w cut G t := by
  let W := L*⌈C₀*Real.log B⌉₊+1
  let U : ℝ := (max 1 ((t*W)^(t*W+1)):ℕ)
  let E : ℝ := (2^(t*W)*max 1 ((t*W)^(t*W+1)):ℕ)
  let f (l : List (AttachedSpec w D L)) (a : S.FixedResidues w) :=
    |avg (fun c : S.FreeResidues w => S.kernel w cut (mergeResidues w a c)*
      listIndicator w l (mergeResidues w a c))|
  let g (a : S.FixedResidues w) := avg (fun c : S.FreeResidues w =>
    |S.kernel w cut (mergeResidues w a c)| * (witnessCount (residualEvents w D L a) t c:ℝ))
  calc
    _ ≤ avg (fun a => if G a then U*(∑ l ∈ boundedLists (AttachedSpec w D L) t, f l a)+E*g a else 0) := by
      apply avg_mono
      intro a
      split_ifs with ha
      · exact conditional_primitive_reduction w cut a (hG a ha) t ht
      · exact le_rfl
    _ = U*(∑ l ∈ boundedLists (AttachedSpec w D L) t,
        avg (fun a => if G a then f l a else 0)) + E*avg (fun a => if G a then g a else 0) :=
      avg_ite_add_sum_mul _ G f g U E
    _ = _ := by
      have he : (∑ l ∈ boundedLists (AttachedSpec w D L) t,
          avg (fun a => if G a then f l a else 0)) =
          ∑ l ∈ boundedLists (AttachedSpec w D L) t, assignedKernelIntegral w cut l G :=
        sum_congr rfl (fun l hl => assignedKernelIntegral_binary w cut l G)
      exact congrArg (fun z : ℝ => U*z + E*avg (fun a => if G a then g a else 0)) he

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
