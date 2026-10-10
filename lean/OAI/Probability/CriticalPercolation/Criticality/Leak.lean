import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BoundaryCount
import OAI.Probability.CriticalPercolation.Criticality.CutInside

namespace OAI

section
section CurrentModule4
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype E]

lemma probability_mono_event {p : ℝ} (hp : p ∈ Icc 0 1) {F F' : Set E → Prop}
    (h : ∀ ω, F ω → F' ω) : probability p F ≤ probability p F' := by
  apply expect_mono (fun _ => weight_nonneg hp)
  intro ω
  by_cases hF : F ω
  · simp only [ite_eq_left hF,ite_eq_left (h ω hF),le_refl]
  · simp only [ite_eq_right hF]
    split_ifs <;> norm_num

variable (G : BondGraph V E)

def leak (S C : Set V) (e : E) (v : V) (ω : Set E) : ℝ :=
  if IsCut G S e ∧ cutInside G S e ∈ C then
    if e ∈ ω ∧ (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0
  else 0

omit [Fintype E] in
lemma leak_nonneg (S C : Set V) (e : E) (v : V) (ω : Set E) :
    0 ≤ leak G S C e v ω := by unfold leak; split_ifs <;> norm_num

omit [Fintype E] in
lemma leak_dependsOn (S C : Set V) (e : E) (v : V) :
    DependsOn (leak G S C e v) (internalIncident G S C)ᶜ := by
  intro ω ω' hω
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · have he : ω e = ω' e := hω e (cut_not_internalIncident G hc.1)
    have hg : delete (G.openGraph ω) C = delete (G.openGraph ω') C :=
      G.delete_openGraph_dependsOn C (fun j hj => hω j (fun hD => hj hD.1))
    simp only [leak,ite_eq_left hc]
    change (if ω e ∧ _ then (1:ℝ) else 0) = if ω' e ∧ _ then 1 else 0
    simp only [he,hg]
  · simp only [leak,ite_eq_right hc]

lemma leak_expect (p : ℝ) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) =
      if IsCut G S e ∧ cutInside G S e ∈ C then
        p * probability p (fun ω => (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v)
      else 0 := by
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · rw [ite_eq_left hc]
    have heI : e ∈ G.incidentEdges C :=
      ⟨cutInside G S e,hc.2,by rw [cut_ends G S e]; simp⟩
    calc
      _ = expect (fun _ : E => weight p) (fun ω => if ω e = True then
          (if (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0) else 0) := by
        congr 1
        funext ω
        simp only [leak,ite_eq_left hc]
        change (if ω e ∧ (delete (G.openGraph ω) C).Reachable
          (cutOutside G S e) v then (1:ℝ) else 0) = _
        by_cases he : ω e <;> simp [he]
      _ = weight p True * expect (fun _ : E => weight p) (fun ω =>
          if (delete (G.openGraph (Function.update ω e True)) C).Reachable
            (cutOutside G S e) v then 1 else 0) :=
        by
          convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
            e True (fun ω => if (delete (G.openGraph ω) C).Reachable
              (cutOutside G S e) v then (1:ℝ) else 0) using 1
          congr 1
          funext ω
          split_ifs <;> rfl
      _ = _ := by
        simp only [weight,ite_true]
        congr 1
        unfold probability
        congr 1
        funext ω
        erw [delete_update_incident G heI]
  · rw [ite_eq_right hc]
    calc
      _ = expect (fun _ : E => weight p) (fun _ => 0) := by
        congr 1; funext ω; simp only [leak,ite_eq_right hc]
      _ = 0 := expect_const _ (fun _ => weight_sum p) 0

lemma leak_expect_le {p : ℝ} (hp : p ∈ Icc 0 1) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) ≤
      (if IsCut G S e ∧ cutInside G S e ∈ C then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v)) := by
  rw [leak_expect]
  split_ifs
  · simp only [one_mul]
    apply mul_le_mul_of_nonneg_left _ hp.1
    exact probability_mono_event hp (fun _ h => h.mono (delete_le _ _))
  · simp

lemma boundary_probability_cut (p : ℝ) (S : Set V) (o : V) (e : E) :
    probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) =
      expect (fun _ : E => weight p) (fun ω =>
        if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) := by
  unfold probability
  congr 1
  funext ω
  simp only [boundaryReach_iff_cut,internalCluster,component,Set.mem_ofPred_eq]
  congr 1

lemma exposed_leak_le {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o v : V) (e : E) :
    expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) ≤
      p * probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) *
        probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  rw [expect_exposure_finiteRange _ (fun _ => weight_sum p)
    (fun ω => internalCluster G S o ω) (internalIncident G S)
    (fun C => dependsOn_internalCluster G S C o) (fun C => leak G S C e v)
    (fun C => leak_dependsOn G S C e v)]
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω =>
        (if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v))) :=
      expect_mono (fun _ => weight_nonneg hp) (fun _ => leak_expect_le G hp S _ e v)
    _ = _ := by rw [expect_mul_const,← boundary_probability_cut]; ring

theorem simon_lieb {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o : V) (ho : o ∈ S)
    (v : V) (hv : v ∉ S) :
    probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      ∑ e, p * probability p (fun ω => boundaryReach G Sᶜ
        (delete (G.openGraph ω) Sᶜ) o e) *
          probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  have hpoint (ω : Set E) : (if (G.openGraph ω).Reachable o v then (1:ℝ) else 0) ≤
      ∑ e, leak G S (internalCluster G S o ω) e v ω := by
    by_cases hr : (G.openGraph ω).Reachable o v
    · rw [ite_eq_left hr]
      obtain ⟨e,hc,hi,he,hv'⟩ := internalCluster_exit G S o ho ω hv hr
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset E)) =>
        leak_nonneg G S (internalCluster G S o ω) j v ω) (Finset.mem_univ e)
      have heq : leak G S (internalCluster G S o ω) e v ω = 1 := by
        simp only [leak, ite_eq_left (And.intro hc hi), ite_eq_left (And.intro he hv')]
      rwa [heq] at hh
    · rw [ite_eq_right hr]
      exact Finset.sum_nonneg (fun _ _ => leak_nonneg G S (internalCluster G S o ω) _ v ω)
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω => ∑ e, leak G S (internalCluster G S o ω) e v ω) :=
      expect_mono (fun _ => weight_nonneg hp) hpoint
    _ = ∑ e, expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) :=
      expect_sum _ _
    _ ≤ _ := Finset.sum_le_sum (fun e _ => exposed_leak_le G hp S o v e)

end CriticalPercolation.Sharpness
end
end CurrentModule4

end

end OAI
