import OAI.Dynamics.StandardMap.PatternCount

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma ordered_subpattern (T : Finset ℕ) (f : ℕ → ℕ) (N r : ℕ) (P : ℕ → ℕ → Prop)
    (hr : r ≤ T.card) (hb : ∀ j ∈ T, j < N ∧ f j < N ∧ P j (f j))
    (hord : ∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) :
    ∃ (e₁ e₂ : Fin r ↪o Fin N), ∀ i, P (e₁ i) (e₂ i) := by
  classical
  let g : Fin r → ℕ := fun i => T.orderEmbOfFin rfl (Fin.castLE hr i)
  have hgmem (i : Fin r) : g i ∈ T := T.orderEmbOfFin_mem rfl _
  have hgmono : StrictMono g := fun i j hij => (T.orderEmbOfFin rfl).strictMono hij
  let e₁ : Fin r → Fin N := fun i => ⟨g i,(hb _ (hgmem i)).1⟩
  let e₂ : Fin r → Fin N := fun i => ⟨f (g i),(hb _ (hgmem i)).2.1⟩
  have hm₁ : StrictMono e₁ := fun i j hij => hgmono hij
  have hm₂ : StrictMono e₂ := fun i j hij => hord _ (hgmem i) _ (hgmem j) (hgmono hij)
  exact ⟨OrderEmbedding.ofStrictMono e₁ hm₁,OrderEmbedding.ofStrictMono e₂ hm₂,
    fun i => (hb _ (hgmem i)).2.2⟩

lemma small_endpoints_pattern (k q a : ℝ) (n Np Nm : ℕ)
    (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1) (hNm : n ≤ Nm ∧ Nm ≤ n+1)
    (hk : 0 ≤ k) (hM : 6 ≤ growthBase k)
    (hb : ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    ∃ (fm fp : Fin (n/100) ↪o Fin (n+2)), ∀ i,
      CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i) := by
  obtain ⟨b,hm,hp⟩:=hb
  obtain ⟨T,f,hcard,hT,hord⟩:=matching_small_endpoints (growthBase k)
    (orbitCoefficient k q a) (orbitCoefficient k q (phi k q-a)) b (potential k q-b)
    n Nm Np hn hNm hNp hM
    (fun j _ _ => potential_bound k _ hk)
    (fun j _ _ => potential_bound k _ hk) hm hp
  apply ordered_subpattern T f (n+2) (n/100)
    (fun jm jp => CommonGood k q a jm jp ∧ MatchedLogs k q a jm jp) hcard ?_ hord
  intro j hj
  have hh:=hT j hj
  refine ⟨by omega,by omega,⟨⟨b,hh.2.2.1,hh.2.2.2.2.2.1⟩,?_⟩⟩
  dsimp [MatchedLogs]
  linarith [hh.2.2.2.2.2.2]

lemma small_endpoints_slice_bound (k q η η' : ℝ) (n Np Nm : ℕ)
    (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1) (hNm : n ≤ Nm ∧ Nm ≤ n+1)
    (hk : 0 ≤ k) (hM : 6 ≤ growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hscarce : ∀ jm jp b, CommonGood k q b jm jp → MatchedLogs k q b jm jp →
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤
      (4^(n+2):ℝ≥0∞)*(ENNReal.ofReal (5*η)^(n/100-1)*3) := by
  apply (measure_mono (show _ ⊆ {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin (n/100) ↪o Fin (n+2)),
      ∀ i, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} from ?_)).trans
  · exact increasing_pattern_union_decay k q η η' (n+2) (n/100) (by omega) (by linarith) hη hsmall hscarce
  · rintro a ⟨ha,hb⟩
    exact ⟨ha,small_endpoints_pattern k q a n Np Nm hn hNp hNm hk hM hb⟩
end StandardMapEntropy

end OAI
