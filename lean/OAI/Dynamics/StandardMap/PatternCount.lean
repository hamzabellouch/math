import OAI.Dynamics.StandardMap.PatternDecay

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma card_increasing_maps_le (N r : ℕ) : Fintype.card (Fin r ↪o Fin N) ≤ 2^N := by
  classical
  let image : (Fin r ↪o Fin N) → Finset (Fin N) := fun f => Finset.univ.image f
  have hi : Function.Injective image := by
    intro f g hfg
    apply DFunLike.ext
    intro i
    have hh : Set.range f=Set.range g := by
      have hc:=congrArg (fun S : Finset (Fin N) => (S:Set (Fin N))) hfg
      simpa [image] using hc
    exact congrFun ((f.strictMono.range_inj_of_wellFoundedLT g.strictMono).mp hh) i
  have hh:=Fintype.card_le_of_injective image hi
  simpa using hh

lemma card_pair_patterns_le (N r : ℕ) :
    Fintype.card ((Fin r ↪o Fin N) × (Fin r ↪o Fin N)) ≤ 4^N := by
  have hh:=Nat.mul_le_mul (card_increasing_maps_le N r) (card_increasing_maps_le N r)
  rw [Fintype.card_prod]
  convert hh using 1
  rw [← mul_pow]
  norm_num
lemma finite_pattern_union_bound {ι : Type*} [Fintype ι]
    (F : ι → Set ℝ) (A : ℝ≥0∞) (N : ℕ)
    (hcard : Fintype.card ι ≤ N) (hF : ∀ i, volume (F i) ≤ A) :
    volume (⋃ i, F i) ≤ N*A := by
  classical
  calc
    _ ≤ ∑ i, volume (F i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : ι, A := Finset.sum_le_sum fun i hi => hF i
    _ = (Fintype.card ι : ℝ≥0∞)*A := by simp [nsmul_eq_mul]
    _ ≤ _ := by gcongr

lemma increasing_pattern_union_decay (k q η η' : ℝ) (N r : ℕ)
    (hr : 1 ≤ r) (hM : 1 < growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hscarce : ∀ jm jp b, CommonGood k q b jm jp → MatchedLogs k q b jm jp →
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin r ↪o Fin N),
      ∀ i : Fin r, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} ≤
      (4^N:ℝ≥0∞)*(ENNReal.ofReal (5*η)^(r-1)*3) := by
  classical
  let F := fun P : (Fin r ↪o Fin N) × (Fin r ↪o Fin N) =>
    {a : ℝ | a ∈ Icc 0 1 ∧ ∀ i : Fin r, CommonGood k q a (P.1 i) (P.2 i) ∧ MatchedLogs k q a (P.1 i) (P.2 i)}
  have hsub : {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin r ↪o Fin N),
      ∀ i : Fin r, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} ⊆ ⋃ P, F P := by
    rintro a ⟨ha,fm,fp,hp⟩
    exact mem_iUnion.mpr ⟨⟨fm,fp⟩,ha,hp⟩
  apply (measure_mono hsub).trans
  have hh:=finite_pattern_union_bound F (ENNReal.ofReal (5*η)^(r-1)*3) (4^N)
    (card_pair_patterns_le N r) ?_
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  intro P
  let fm : ℕ → ℕ := fun i => if h : i < r then (P.1 ⟨i,h⟩ : ℕ) else 0
  let fp : ℕ → ℕ := fun i => if h : i < r then (P.2 ⟨i,h⟩ : ℕ) else 0
  apply pattern_decay k q η η' fm fp r (F P) hr hM hη hsmall (fun a ha => ha.1)
  · intro a ha i hi
    simpa only [fm,fp,dite_eq_left hi] using (ha.2 ⟨i,hi⟩).1
  · intro i hi
    have hi' : i < r := by omega
    simp only [fm,fp,dite_eq_left hi,dite_eq_left hi']
    change ((P.1 ⟨i,hi'⟩ : ℕ) < (P.1 ⟨i+1,hi⟩ : ℕ)) ∧
      ((P.2 ⟨i,hi'⟩ : ℕ) < (P.2 ⟨i+1,hi⟩ : ℕ))
    exact
      And.intro (P.1.strictMono (show (⟨i,hi'⟩:Fin r) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self i))
        (P.2.strictMono (show (⟨i,hi'⟩:Fin r) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self i))
  · intro i hi b hb
    simpa only [fm,fp,dite_eq_left hi] using hscarce (P.1 ⟨i,hi⟩) (P.2 ⟨i,hi⟩) b
      (hb.2 ⟨i,hi⟩).1 (hb.2 ⟨i,hi⟩).2
end StandardMapEntropy

end OAI
