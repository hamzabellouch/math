import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.TerminalPrefix
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialCoupling2
import OAI.Combinatorics.KMedianRecovery.Recovery.RegularCardBounds
import OAI.Combinatorics.KMedianRecovery.Strictness.ValidExecutionClusterStrictness

namespace OAI

namespace MetricKMedianRecovery.HistoryCompatibleCertificate
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma final_budget_pos {steps : ℕ} {v lam eta : ℝ}
    (E : ValidExecution D X steps v lam eta) (hvsmall : v < 1/6) (j : D) :
    0 < (E.state steps).budget j := by
  rw [E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)]
  exact (E.phase_pos _ (E.removal j).isLt.le).trans_le
    ((E.transition _ (E.removal j).isLt).active_budget_lower hvsmall
      (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_active j))

theorem compatible_certificate (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) :
    ∃ alpha : D → ℝ,
      (∀ j, 0 < alpha j) ∧
      (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
      ((1-3*v)*(∑ j, nearestDistance (loc j) (PhaseHistoryTransfer.after ∅ T)) +
        ((PhaseHistoryTransfer.after ∅ T ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤
          ∑ j, alpha j) ∧
      (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
        0 < (∑ j ∈ C, dist i (loc j)) →
        lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
        v^2 ≤ strictnessGap b/(6*(b+2)) →
        (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j))) := by
  obtain ⟨steps,E,paid,hloc,hF,hopen,_,hpaid,hcert,hcount⟩ :=
    CountedHistoryExecution.valid_counted_execution loc F B v lam eta T hFB hfar h hterm
  refine ⟨(E.state steps).budget,final_budget_pos E hv1,?_,?_,?_⟩
  · intro i hi
    have hiE : i ∈ E.regular := by simpa only [hF] using hi
    simpa only [hloc] using valid_execution_final_dual v lam eta E hv hv1 hlam i hiE
  · simpa only [hloc,hopen,hcount] using valid_execution_payment v lam eta E paid hpaid hcert hv1
  · intro C hC i hi b hb hP hprice hsmall
    have hiE : i ∈ E.regular := by simpa only [hF] using hi
    have hPE : 0 < ∑ j ∈ C, dist i (E.location j) := by simpa only [hloc] using hP
    have hpriceE : lam ≤ b*(∑ j ∈ C, dist i (E.location j)) := by simpa only [hloc] using hprice
    simpa only [hloc] using valid_execution_cluster_strictness v lam eta b E C hC i hiE
      hv hv1 hlam hb hPE hpriceE hsmall

end MetricKMedianRecovery.HistoryCompatibleCertificate

namespace MetricKMedianRecovery.PhaseMergeCertificate
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
  PhaseTerminalProducer HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Budget (loc : D → X) (F Q : Finset X) (v lam eta : ℝ) : Prop :=
  ∃ alpha : D → ℝ,
    (∀ j, 0 < alpha j) ∧
    (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
    ((1-3*v)*(∑ j, nearestDistance (loc j) Q) +
      ((Q ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤ ∑ j, alpha j) ∧
    (∀ (C : Finset D), C.Nonempty → ∀ i ∈ F, ∀ b : ℝ, 0 < b →
      0 < (∑ j ∈ C, dist i (loc j)) → lam ≤ b*(∑ j ∈ C, dist i (loc j)) →
      v^2 ≤ strictnessGap b/(6*(b+2)) →
      (∑ j ∈ C, alpha j) ≤ lam+(2-strictnessGap b/2)*(∑ j ∈ C, dist i (loc j)))

lemma certify {loc : D → X} {F B : Finset X} {v lam eta M hi : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hdis : Disjoint F B)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < M+hi) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta (limit v (M+hi)+1) P) :
    Budget loc F (after ∅ P) v lam eta := by
  exact HistoryCompatibleCertificate.compatible_certificate loc F B v lam eta P hdis
    (fun j i hi => hfar i hi j) hp.history
    (terminal_next hF hv hvsmall hdiam hZ (by linarith only [hu]) hp) hv hvsmall hlam

def Output (loc : D → X) (F : Finset X) (v eta lo hi M U : ℝ) (k : ℕ) : Prop :=
  ∃ B lam P, Nonempty (PhaseLeafGeometry.Data loc F B U) ∧
    Disjoint F B ∧ lo ≤ lam ∧ lam ≤ hi ∧
    PrefixData loc F B v lam eta (limit v (M+hi)+1) P ∧
    (∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(limit v (M+hi))) (after ∅ P) j) ∧
    ((after ∅ P) ∩ F).card = k ∧
    (after ∅ P \ F).card ≤ 3*(limit v (M+hi)+1) ∧
    Budget loc F (after ∅ P) v lam eta

def EnlargedOutput (loc : D → X) (F : Finset X) (v eta lo hi M U : ℝ) (k : ℕ) : Prop :=
  ∃ (Y : Type uX) (m : PseudoMetricSpace Y) (d : DecidableEq Y) (e : X ↪ Y),
    letI := m
    letI := d
    (∀ x y, dist (e x) (e y) = dist x y) ∧
      Output (fun j => e (loc j)) (F.image e) v eta lo hi M U k

omit [DecidableEq X] in
lemma solved_output {loc : D → X} {F : Finset X} {v eta lo hi M U : ℝ} {k : ℕ}
    (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6) (hlo : 0 < lo)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < M+hi)
    (hs : PhaseGeometricMerge.Solved loc F v eta lo hi (limit v (M+hi)+1) k U) :
    EnlargedOutput loc F v eta lo hi M U k := by
  obtain ⟨Y,m,d,e,he,B,lam,P,hg,hd,hl,hu,hp,hk⟩ := hs
  let := m
  let := d
  have hfar' : ∀ i ∈ F.image e, ∀ j, 1 ≤ dist i (e (loc j)) := by
    intro y hy j
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [he]
    exact hfar x hx j
  have hdiam' : ∀ i ∈ F.image e, ∀ j, dist i (e (loc j)) ≤ M := by
    intro y hy j
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [he]
    exact hdiam x hx j
  refine ⟨Y,m,d,e,he,B,lam,P,hg,hd,hl,hu,hp,?_,hk,copies_bound hp,?_⟩
  · exact terminal_prefix (hF.image e) hv hvsmall hdiam' hZ (by linarith only [hu]) hp
  · exact certify (hF.image e) hd hv hvsmall (hlo.trans_le hl) hfar' hdiam' hZ hu hp

theorem produce [Nonempty D] (loc : D → X) (F : Finset X) (v eta : ℝ)
    (lo M : ℚ) (k N : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heta : 0 ≤ eta) (hprec : (1:ℝ)/2^N ≤ eta)
    (hlo : 0 < lo) (hM : 0 < M) (hN : 3 ≤ N) (hnN : Fintype.card D ≤ N)
    (hk : 2 ≤ k) (hlohi : lo ≤ 8*(Fintype.card D:ℚ)*M)
    (hF : F.Nonempty) (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ)) :
    (∃ P, PrefixData loc F ∅ v (lo:ℝ) 0
        (limit v ((M:ℝ)+8*(Fintype.card D:ℝ)*(M:ℝ))+1) P ∧
      (∀ j, ¬activeAt loc (1-3*v)
        ((1+v^2)^(limit v ((M:ℝ)+8*(Fintype.card D:ℝ)*(M:ℝ)))) (after ∅ P) j) ∧
      (after ∅ P).card ≤ k ∧ Budget loc F (after ∅ P) v (lo:ℝ) 0) ∨
    EnlargedOutput loc F v eta (lo:ℝ) (8*(Fintype.card D:ℝ)*(M:ℝ)) (M:ℝ) (20*N*(M:ℝ)) k := by
  have hloR : (0:ℝ) < (lo:ℝ) := by exact_mod_cast hlo
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hZ : 0 < (M:ℝ)+8*(Fintype.card D:ℝ)*(M:ℝ) := by positivity
  have hlR : (lo:ℝ) ≤ 8*(Fintype.card D:ℝ)*(M:ℝ) := by exact_mod_cast hlohi
  rcases PhaseGeometricMerge.produce loc F v eta lo M k N
      (limit v ((M:ℝ)+8*(Fintype.card D:ℝ)*(M:ℝ))+1)
      hv hvsmall heta hprec hlo hM hN hnN hk hlohi hF hfar hdiam with
    ⟨c,hck,P,hplen,hp,hr,hc⟩ | hs
  · left
    have hstart := PhaseInitialBracket.empty_prefix loc F ∅ v (lo:ℝ) 0 hloR.le hfar
    have hfull := hstart.append_exact hv hvsmall hloR le_rfl P hp hr
    simp only [Nat.zero_add,List.nil_append,hplen] at hfull
    have hsub : after ∅ P ⊆ F := by simpa only [Finset.union_empty] using hfull.after_subset
    refine ⟨P,hfull,terminal_prefix hF hv hvsmall hdiam hZ (by linarith only [hlR]) hfull,?_,?_⟩
    · rw [Finset.inter_eq_left.mpr hsub] at hc
      exact hc ▸ hck
    · exact certify hF (Finset.disjoint_empty_right F) hv hvsmall hloR hfar hdiam hZ hlR hfull
  · exact Or.inr (solved_output hF hv hvsmall hloR hfar hdiam hZ hs)

end MetricKMedianRecovery.PhaseMergeCertificate

end OAI
