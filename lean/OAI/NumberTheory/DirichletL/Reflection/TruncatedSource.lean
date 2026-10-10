import OAI.NumberTheory.DirichletL.Reflection.DyadicBox
import OAI.NumberTheory.DirichletL.Reflection.HeightTail

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def retainedDyads (scale B : ℝ) : Finset (ℕ×ℕ×ℕ) :=
  (retainedDyadicBox scale B).filter (fun i => rawDyadicCenter scale i≤B)

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma retainedDyads_card_le (scale B : ℝ) :
    (retainedDyads scale B).card≤(retainedDyadicBox scale B).card := Finset.card_filter_le _ _

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm

theorem actual_truncated_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
      ‖(∑' i,literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)-
        (∑ i∈retainedDyads (literalRawScale G s X) (16*T),
          literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i)‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := literal_dyadic_tail_uniform_height (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro G D s hc hN hbase hchar j hj S u θ X T hX hT
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hs := literalDyadicBlock_summable G D s hc hN hbase hchar j hj S
    (CompletedHeight.normTwistedSource W θ) lo hi hlo
    ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  rw [tsum_sub_finset_eq_tail _ hs]
  have hb := hbound G D s hc hN hbase hchar j hj S u θ X T hX hT
    (fun i => i∉retainedDyads (literalRawScale G s X) (16*T))
    (fun i hi => (lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ (literalRawScale_pos G s hc X hX) i).mpr h))).le)
  apply le_trans ?_ hb
  apply le_of_eq
  congr 1
  apply tsum_congr
  intro i
  by_cases hi : i∈retainedDyads (literalRawScale G s X) (16*T) <;> simp [hi]
end
end SevenEighths.InverseReflectedPhase

end OAI
