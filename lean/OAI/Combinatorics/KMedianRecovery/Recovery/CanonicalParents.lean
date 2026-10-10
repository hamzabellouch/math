import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledInitial
import OAI.Combinatorics.KMedianRecovery.Machines.MergeResources
import OAI.Combinatorics.KMedianRecovery.Strictness.Dual

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]
omit [DecidableEq V] in
lemma parent_original (i : V) : parent (original i)=i := rfl
omit [DecidableEq V] in
lemma parent_leaf (key : ℕ) (i : V) (s : ℚ) : parent (leaf key i s)=i := rfl
omit [DecidableEq V] in
lemma parent_copy (key : ℕ) (x : Label V) : parent (copy key x)=parent x := by cases x <;> rfl
end MetricKMedianRecovery.RationalLeaves
namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Rooted (F : Finset V) (B : Finset (Label V)) : Prop := ∀ x∈B,parent x∈F
omit [LinearOrder V] in
lemma rooted_empty (F : Finset V) : Rooted F ∅ := by intro x hx; simp at hx
lemma correction_parent (c : Correction V) (x : Label V) : parent (c.apply x)=parent x := by
  cases c with
  | identity => rfl
  | shorten key i l u => exact parent_shorten key i l u x
lemma rooted_mapFree (F : Finset V) (s : State V) (h : Rooted F s.B) : Rooted F s.mapFree := by
  intro x hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  rw [correction_parent]
  exact h y hy
lemma rooted_pool (F : Finset V) (B : Finset (Label V)) (key : ℕ) (h : Rooted F B) :
    Rooted F (PhaseMergePath.pool (F.image original) B (copy key)) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · exact h x hx
  · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hy
    simpa only [parent_copy,parent_original] using hi
lemma rooted_banks (F : Finset V) (B : Finset (Label V)) (q : ℕ) (h : Rooted F B) :
    Rooted F (banks F B q) := rooted_pool F _ _ (rooted_pool F B _ h)
lemma rooted_insert (F : Finset V) (B : Finset (Label V)) (key : ℕ) (i : V) (s : ℚ)
    (h : Rooted F B) (hi : i∈F) : Rooted F (insert (leaf key i s) B) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hi
  · exact h x hx

def Outcome.Rooted (F : Finset V) : Outcome V→Prop
  | .inl o => CanonicalCoupledMerge.Rooted F o.B
  | .inr s => CanonicalCoupledMerge.Rooted F s.B
lemma resolve_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k key : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V)) (h : Rooted F B) :
    (resolve loc distance F v M N precision q n k key B lam P R).Rooted F := by
  cases R with
  | success H T => exact h
  | common H T U => exact h
  | sensitive H G T U =>
    simp only [resolve]
    split
    next he => exact h
    next J he =>
      have hj:=view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G J he
      have hr : J.root∈F.image original := by cases J <;> exact hj.1
      obtain ⟨i,hi,hiJ⟩:=Finset.mem_image.mp hr
      have hp : parent J.root∈F := by rw [←hiJ,parent_original]; exact hi
      split <;> exact rooted_insert F B key (parent J.root) _ h hp
lemma step_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) (h : Rooted F s.B) :
    (step loc distance F v M N precision q n k s).Rooted F := by
  unfold step
  split
  next H T G U hT hU =>
    dsimp only
    split
    · exact rooted_mapFree F s h
    · split
      · exact resolve_rooted loc distance F v M N precision q n k _ _ _ _ _
          (rooted_banks F s.mapFree q (rooted_mapFree F s h))
      · exact h
  next => exact h
lemma run_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k q n : ℕ) (s : State V) (h : Rooted F s.B) :
    Rooted F (run loc distance F v M N precision k q n s).B := by
  induction n generalizing q s with
  | zero => exact h
  | succ n ih =>
    have hs:=step_rooted loc distance F v M N precision q n k s h
    rw [run]
    split
    next o he => rw [he] at hs; exact hs
    next t he => rw [he] at hs; exact ih (q+1) t hs

def StartOutput.Rooted (F : Finset V) : StartOutput V→Prop
  | .small o => CanonicalCoupledMerge.Rooted F o.B
  | .normal o => CanonicalCoupledMerge.Rooted F o.B
lemma start_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) :
    (start loc distance F v lo M N precision total k).Rooted F := by
  simp only [start]
  split
  · exact rooted_empty F
  · split
    · exact rooted_empty F
    · split
      · exact rooted_empty F
      · exact run_rooted loc distance F v M N precision k 0 total _ (rooted_empty F)
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
attribute [local instance] RationalLeaves.metric

def project (Q : Finset (Label V)) : Finset V := Q.image parent
omit [PseudoMetricSpace V] in
lemma project_nonempty {Q : Finset (Label V)} (hQ : Q.Nonempty) : (project Q).Nonempty := hQ.image parent
omit [PseudoMetricSpace V] in
lemma project_card (Q : Finset (Label V)) : (project Q).card≤Q.card := Finset.card_image_le
omit [DecidableEq V] in
lemma parent_distance (j : V) (x : Label V) : dist j (parent x)≤dist (original j) x := by
  cases x with
  | inl i => exact (original_dist j i).ge
  | inr c =>
    change dist j c.2.1≤dist (original j) (leaf c.1 c.2.1 c.2.2)
    rw [leaf_dist]
    have hh : (0:ℝ)≤(max c.2.2 0:ℚ) := by exact_mod_cast le_max_right c.2.2 0
    linarith
lemma project_distance (j : V) (Q : Finset (Label V)) :
    nearestDistance j (project Q)≤nearestDistance (original j) Q := by
  by_cases hQ : Q.Nonempty
  · obtain ⟨x,hx,he⟩:=nearestDistance_attained (original j) Q hQ
    exact (nearestDistance_le_mem j _ (parent x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).trans
      ((parent_distance j x).trans_eq he.symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp [project, nearestDistance]
omit [PseudoMetricSpace V] in
lemma project_subset (F : Finset V) (B Q : Finset (Label V))
    (hb : CanonicalCoupledMerge.Rooted F B) (hQ : Q⊆F.image original∪B) : project Q⊆F := by
  intro i hi
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hi
  rcases Finset.mem_union.mp (hQ hx) with hx|hx
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    exact hj
  · exact hb x hx
end MetricKMedianRecovery.RationalLeaves
namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def Output.project (o : Output V) : Finset V := RationalLeaves.project (after ∅ o.P)

lemma Output.normal_certificate (loc : Fin d→V) (F : Finset V) (v eta lo hi M : ℝ)
    (k : ℕ) (o : Output V) (h : o.Correct loc F v eta lo hi (limit v (M+hi)+1) k)
    (hroot : Rooted F o.B) (hk : 0<k) (hF : F.Nonempty) (hv : 0<v) (hv1 : v<1/6)
    (hlo : 0<lo) (hZ : 0<M+hi)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M) :
    o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k+3*(limit v (M+hi)+1) ∧
    ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
      PhaseOriginalLedger.Dual loc F v o.lam alpha ∧
      (1-3*v)*Q+(k:ℝ)*((o.lam:ℝ)-(d:ℝ)*eta)≤∑ j,alpha j := by
  obtain ⟨hdis,hl,hu,hp,hcount⟩:=h
  have hne : (after ∅ o.P).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.empty_inter,Finset.card_empty] at hcount
    omega
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hdiam' : ∀ x∈F.image original,∀ j,dist x (original (loc j))≤M := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hdiam i hi j
  obtain ⟨alpha,hpos,hdual,hpay,hstrict⟩:=certify (hF.image original) hdis hv hv1 (hlo.trans_le hl)
    hfar' hdiam' hZ hu hp
  refine ⟨project_subset F o.B _ hroot hp.after_subset,project_nonempty hne,?_,
    ∑ j,nearestDistance (original (loc j)) (after ∅ o.P),alpha,?_,?_,?_,?_⟩
  · have hc:=PhaseTerminalProducer.copies_bound hp
    have he:=Finset.card_inter_add_card_sdiff (after ∅ o.P) (F.image original)
    exact (project_card _).trans (by omega)
  · exact Finset.sum_nonneg (fun j _=>nearestDistance_nonneg _ _)
  · exact Finset.sum_le_sum (fun j _=>project_distance (loc j) _)
  · refine ⟨hpos,?_,?_⟩
    · intro i hi
      simpa only [original_dist] using hdual (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · intro C hC i hi b hb hP hlp hsmall
      have hP' : 0<∑ j∈C,dist (original i) (original (loc j)) := by simpa only [original_dist] using hP
      have hlp' : (o.lam:ℝ)≤b*(∑ j∈C,dist (original i) (original (loc j))) := by
        simpa only [original_dist] using hlp
      simpa only [original_dist] using hstrict C hC (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) b hb hP' hlp' hsmall
  · simpa only [hcount,Fintype.card_fin] using hpay
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
