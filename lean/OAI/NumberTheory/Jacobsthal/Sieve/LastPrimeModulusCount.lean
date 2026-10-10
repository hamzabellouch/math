import OAI.NumberTheory.Jacobsthal.Paths.ActualSampleWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StoppedModulusCount

open _root_.Finset
open FinitePathGeometry PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedTraceSets
open StoppedTraceAdmission StoppedCountAdapters ReferencePruning ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem trace_product_eq_finset (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    {ps : List ℕ} (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) :
    (∏ p ∈ ps.toFinset,p) = ps.prod := by
  simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) (trace_nodup w stop n v hp)

theorem trace_primeFactors (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hP : ∀ p ∈ v.available,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : ps.prod.primeFactors = ps.toFinset := by
  have hprime : ∀ p ∈ ps.toFinset,Nat.Prime p :=
    fun p hp' => trace_primes w stop n v hP hp p (List.mem_toFinset.mp hp')
  have h := ErdosInverseCounts.primeFactors_product ps.toFinset hprime
  rwa [trace_product_eq_finset w stop n v hp] at h

theorem trace_product_squarefree (w : ℝ) (stop : List ℕ → Prop) (n : ℕ) (v : Vertex)
    (hP : ∀ p ∈ v.available,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n v ∨ ps ∈ stopped w stop n v) : Squarefree ps.prod := by
  have hprime : ∀ p ∈ ps.toFinset,Nat.Prime p :=
    fun p hp' => trace_primes w stop n v hP hp p (List.mem_toFinset.mp hp')
  rw [← trace_product_eq_finset w stop n v hp]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (hprime p hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)

theorem trace_mass_eq_modulusCount (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (stop : List ℕ → Prop) (n : ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n (rootVertex z ∅ P mu) ∨ ps ∈ stopped w stop n (rootVertex z ∅ P mu)) :
    countMass Y small a (after w (rootVertex z ∅ P mu) ps) = (modulusCount Y small a ps.prod : ℝ) := by
  rw [root_after_mass,Finset.empty_union,modulusCount_eq_mass Y small a _ (suffixPrimes P ps),
    trace_primeFactors w stop n (rootVertex z ∅ P mu) hP hp]

theorem trace_survivors_eq_product_node (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu : ℝ) (stop : List ℕ → Prop) (n : ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n (rootVertex z ∅ P mu) ∨ ps ∈ stopped w stop n (rootVertex z ∅ P mu)) :
    countSurvivors Y small a (after w (rootVertex z ∅ P mu) ps) =
      (ResidueSieveTree.survivorCount Y small a (ps.prod.primeFactors,suffixPrimes P ps) : ℝ) := by
  rw [root_after_survivors,Finset.empty_union,trace_primeFactors w stop n (rootVertex z ∅ P mu) hP hp]

theorem trace_bad_edge_iff (w : ℝ) (Y : ℕ) (small P : Finset ℕ) (a : ℕ → ℕ)
    (z : Node) (mu delta V0 : ℝ) (stop : List ℕ → Prop) (n : ℕ)
    (hP : ∀ p ∈ P,Nat.Prime p) {ps : List ℕ}
    (hp : ps ∈ expanded w stop n (rootVertex z ∅ P mu) ∨ ps ∈ stopped w stop n (rootVertex z ∅ P mu))
    {u : ℕ} (hu : u ∈ (after w (rootVertex z ∅ P mu) ps).available) :
    NodeBadEdge Y small a delta V0 ps.prod u ↔
      |countMass Y small a (child w (after w (rootVertex z ∅ P mu) ps) u)-
        countMass Y small a (after w (rootVertex z ∅ P mu) ps)/(u:ℝ)| >
          delta*(Y:ℝ)*V0/((ps.prod:ℝ)*(u:ℝ)) := by
  have hpf := trace_primeFactors w stop n (rootVertex z ∅ P mu) hP hp
  have hm : ps.prod ≠ 0 := (trace_product_squarefree w stop n (rootVertex z ∅ P mu) hP hp).ne_zero
  have hup : u ∈ P := by
    rw [after_available] at hu
    exact (Finset.mem_filter.mp hu).1
  rw [nodeBadEdge_iff_tree_mass Y small a delta V0 ps.prod u (suffixPrimes P ps) hm (hP u hup)]
  simp only [countMass_eq_tree_mass,child,after_required,after_available,rootVertex,
    Finset.empty_union,ResidueSieveTree.child,hpf]

end NumberTheoryLean.StoppedModulusCount

end

section

namespace NumberTheoryLean.LastPrimeModulusCount
open PrimeHistories StoppedCountVertex StoppedVertexHistory StoppedCountAdapters
open ReferencePruning SievePartition LargePrimeDeletion LogarithmicBinPartition ErdosInverseCounts
attribute [local instance] Classical.propDecidable

theorem survivor_required_union (Y : ℕ) (H small P : Finset ℕ) (a : ℕ → ℕ) :
    survivors (residueCandidates Y H small a) P (residueBad a)=residueCandidates Y H (small∪P) a := by
  ext n
  simp only [mem_survivors,mem_residueCandidates,Finset.mem_union,or_imp,forall_and]
  tauto

theorem below_all_last (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·)) (q : ℕ) :
    (∀ p∈ps,q<p) ↔ q<ps.getLastD 0 := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  constructor
  · intro h
    exact h _ (List.getLast_mem hne)
  · intro h p hp
    have hd' : (ps.dropLast++[ps.getLast hne]).Pairwise (· > ·) := by rwa [List.dropLast_append_getLast]
    rw [← List.dropLast_append_getLast hne] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.trans ((List.pairwise_append.mp hd').2.2 p hp _ (by simp))
    · simpa only [List.mem_singleton.mp hp] using h

theorem small_suffix_strict_cutoff {w top : ℝ} (hw : 0 < w) (htop : w < top)
    (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·))
    (hsource : ∀ p∈ps,p∈sourcePrimeSet w top) :
    cutoffPrimes ⌊w⌋₊∪suffixPrimes (sourcePrimeSet w top) ps=cutoffPrimes (ps.getLastD 0-1) := by
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  have hlast : ps.getLastD 0∈ps := by rw [he]; exact List.getLast_mem hne
  have hP := (mem_sourcePrimeSet hw htop _).mp (hsource _ hlast)
  ext q
  constructor
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨hqprime,hqw⟩ := mem_cutoffPrimes.mp hq
      have hqr : (q:ℝ) < (ps.getLastD 0:ℝ) := ((Nat.le_floor_iff hw.le).mp hqw).trans_lt hP.2.1
      have hqn : q < ps.getLastD 0 := by exact_mod_cast hqr
      exact mem_cutoffPrimes.mpr ⟨hqprime,by omega⟩
    · obtain ⟨hqS,hall⟩ := Finset.mem_filter.mp hq
      have hqprime := ((mem_sourcePrimeSet hw htop q).mp hqS).1
      have hlastq := (below_all_last ps hne hd q).mp hall
      exact mem_cutoffPrimes.mpr ⟨hqprime,by omega⟩
  · intro hq
    obtain ⟨hqprime,hql⟩ := mem_cutoffPrimes.mp hq
    have hPlast : 0 < ps.getLastD 0 := hP.1.pos
    have hqP : q < ps.getLastD 0 := by omega
    by_cases hqw : q ≤ ⌊w⌋₊
    · exact Finset.mem_union_left _ (mem_cutoffPrimes.mpr ⟨hqprime,hqw⟩)
    · have hwq : w < (q:ℝ) := lt_of_not_ge (fun h => hqw ((Nat.le_floor_iff hw.le).mpr h))
      have hqt : (q:ℝ) ≤ top := (show (q:ℝ) ≤ (ps.getLastD 0:ℝ) by exact_mod_cast hqP.le).trans hP.2.2
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨(mem_sourcePrimeSet hw htop q).mpr ⟨hqprime,hwq,hqt⟩,(below_all_last ps hne hd q).mpr hqP⟩)

theorem after_survivors_eq_last_modulusCount (Y : ℕ) {w top : ℝ}
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : Node) (mu : ℝ)
    (ps : List ℕ) (hne : ps≠[]) (hd : ps.Pairwise (· > ·))
    (hsource : ∀ p∈ps,p∈sourcePrimeSet w top) :
    countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) ps)=
      (modulusCount Y (cutoffPrimes (ps.getLastD 0-1)) a ps.prod:ℝ) := by
  have hprime : ∀ p∈ps.toFinset,p.Prime := fun p hp =>
    ((mem_sourcePrimeSet hw htop p).mp (hsource p (List.mem_toFinset.mp hp))).1
  have hprod : (∏ p∈ps.toFinset,p)=ps.prod := by
    simpa only [List.map_id'] using List.prod_toFinset (fun p : ℕ => p) (hd.imp (fun h => ne_of_gt h))
  have hfac : ps.prod.primeFactors=ps.toFinset := by
    rw [← hprod]
    exact primeFactors_product ps.toFinset hprime
  unfold countSurvivors
  rw [after_required,after_available]
  change ((survivors (residueCandidates Y (∅∪ps.toFinset) (cutoffPrimes ⌊w⌋₊) a)
    (suffixPrimes (sourcePrimeSet w top) ps) (residueBad a)).card:ℝ)=_
  rw [Finset.empty_union,survivor_required_union,small_suffix_strict_cutoff hw htop ps hne hd hsource]
  simp only [modulusCount,modulusCandidates,Int.cast_natCast,hfac]

theorem frozen_survivors_eq_modulusCount (Y : ℕ) {w top : ℝ}
    (hw : 0 < w) (htop : w < top) (a : ℕ → ℕ) (z : Node) (mu : ℝ)
    (pre tail : List ℕ) (p : ℕ) (htail : tail≠[])
    (hd : (pre++p::tail).Pairwise (· > ·))
    (hsource : ∀ q∈pre++p::tail,q∈sourcePrimeSet w top) :
    countSurvivors Y (cutoffPrimes ⌊w⌋₊) a (after w (rootVertex z ∅ (sourcePrimeSet w top) mu) (pre++p::tail))=
      (modulusCount Y (cutoffPrimes (tail.getLastD 0-1)) a (p*(pre.prod*tail.prod)):ℝ) := by
  have hlast : (pre++p::tail).getLastD 0=tail.getLastD 0 := by
    rw [← List.dropLast_append_getLast htail]
    rw [← List.cons_append,← List.append_assoc]
    simp only [List.getLastD_concat]
  rw [after_survivors_eq_last_modulusCount Y hw htop a z mu _ (by simp) hd hsource,hlast]
  congr 2
  simp only [List.prod_append,List.prod_cons]
  ring
end NumberTheoryLean.LastPrimeModulusCount

end

end Erdos970

end OAI
