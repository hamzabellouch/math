import OAI.Probability.SignedSweeps.TypeTrace
import OAI.Probability.SignedSweeps.LocalTraceBudget

namespace OAI

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators Classical

lemma size_eq {p : ℕ} (t : PairType p) : t.1.1+(p-t.1.1)=p :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ t.1.2)

lemma extended_size_eq {p n : ℕ} (t : PairType p) (hpn : p ≤ n) :
    t.1.1+(p-t.1.1)+(n-p)=n := by rw [t.size_eq, Nat.add_sub_of_le hpn]

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p t q B : ℕ} {k : J → ℕ}

lemma blockCarrierCost_le_exp (a : ∀ j, PairType (k j))
    (hk : ∀ j, k j ≤ t) (hB : t+1 ≤ B) :
    (∏ j, pairCarrierCost (Fin q) (a j).2.1 (a j).2.2) ≤
      Real.exp (blockEntropy a+(Fintype.card J : ℝ)*(2*(q:ℝ)^2*Real.log B)) := by
  calc
    _ ≤ ∏ j, Real.exp ((a j).entropy+2*(q:ℝ)^2*Real.log B) := by
      apply Finset.prod_le_prod₀ (fun j _ => (pairCarrierCost_pos _ _ _).le)
      intro j _
      exact pairCarrierCost_le_exp _ _ (by rw [(a j).size_eq]; exact hk j) hB
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, blockEntropy]

lemma blockTypeCount_le_exp (hk : ∀ j, k j ≤ t) (hB : t+1 ≤ B) :
    (Fintype.card (∀ j, PairType (k j)) : ℝ) ≤
      Real.exp ((Fintype.card J : ℝ)*((4*(Nat.sqrt t : ℝ)+1)*Real.log B)) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : J, Real.exp ((4*(Nat.sqrt t:ℝ)+1)*Real.log B) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => pairTypeCount_le_exp (hk j) hB)
    _ = _ := by rw [← Real.exp_sum]; simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma block_stabilizer_trace_exp (e : (Σ j, Fin (k j)) ≃ Fin p)
    (a : ∀ j, PairType (k j)) (hk : ∀ j, k j ≤ t)
    (ha : ∀ j, (a j).height ≤ q)
    (i : ∀ j, Fin (k j) ↪ Fin t) (f : J → SymmetricGroup t → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (η : ℝ) (G : J → ℝ)
    (hamb : ∀ j (lam : Partition t) (c : Partition (t-k j)),
      SignedOccurrence ((a j).extended_size_eq (hk j)) (a j).2.1 (a j).2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*(a j).entropy+G j))
    (hB : 2*t+2*q+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (blockTypeProjection e a * coefficientAction (signedWordRepresentation p (Fin q))
        (coefficientPush (blockPermutation e)
          (productCoefficient (fun j g => f j (g.viaEmbedding (i j))))))).re ≤
      (∏ j, ((k j).factorial : ℝ)/t.factorial) *
        Real.exp ((η-1)*blockEntropy a+(∑ j, G j)+
          (Fintype.card J : ℝ)*localTraceError t q B) := by
  have hp (j : J) : (coefficientAction (signedWordRepresentation (k j) (Fin q))
      (fun g => f j (g.viaEmbedding (i j)))).IsPositive := by
    exact unitary_injective_coefficient_positive _ (fun g x => signedWordRepresentation_norm g x)
      (Equiv.Perm.viaEmbeddingHom (i j)) (viaEmbeddingHom_injective _) _ (hf j)
  rw [blockTypeProjection_trace_real e a _ hp]
  have hnonneg (j : J) : 0 ≤ (LinearMap.trace ℂ (WordSpace (k j) (Fin q ⊕ Fin q))
      ((a j).projector (Fin q) * coefficientAction (signedWordRepresentation (k j) (Fin q))
        (fun g => f j (g.viaEmbedding (i j))))).re := by
    have hh := positive_commuting_projection _ ((a j).projector (Fin q)) (hp j)
      (pairTypeProjection_positive _ _ _ _).isSymmetric
      (pairTypeProjection_idempotent _ _ _ _) (pairTypeProjection_coefficient_commute _ _ _ _)
    exact Complex.re_le_re hh.trace_nonneg
  calc
    _ ≤ ∏ j, (((k j).factorial : ℝ)/t.factorial) *
         Real.exp ((η-1)*(a j).entropy+G j+localTraceError t q B) := by
      apply Finset.prod_le_prod₀ (fun j _ => hnonneg j)
      intro j _
      exact signed_local_stabilizer_trace_exp (a j).size_eq ((a j).extended_size_eq (hk j))
        (a j).2.1 (a j).2.2
        ((le_max_left _ _).trans (ha j)) ((le_max_right _ _).trans (ha j))
        (i j) (f j) (hf j) η (G j) (hamb j) B hB
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, blockEntropy]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma angle_trace_exp_tradeoff {η F w E U V a x y : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hE : 0 ≤ E)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (han : a ≤ min 1 (Real.exp (w-F+E)))
    (hxy : x*y ≤ U*V*Real.exp (-(1-η)*w)) :
    a*x*y ≤ U*V*Real.exp (-(1-η)*F+E) := by
  have hb : min 1 (Real.exp (w-F+E)) ≤
      Real.exp E * Real.exp (min 0 (w-F)) := by
    by_cases hw : 0 ≤ w-F
    · rw [min_eq_left hw, Real.exp_zero, mul_one]
      exact (min_le_left _ _).trans (Real.one_le_exp_iff.mpr hE)
    · rw [min_eq_right (le_of_not_ge hw), ← Real.exp_add]
      apply (min_le_right _ _).trans_eq
      congr 1
      ring
  have hc : a * (x*y) ≤ (Real.exp E * Real.exp (min 0 (w-F))) *
      (U*V*Real.exp (-(1-η)*w)) :=
    mul_le_mul (han.trans hb) hxy (mul_nonneg hx hy) (ha.trans (han.trans hb))
  calc
    a*x*y = a*(x*y) := mul_assoc _ _ _
    _ ≤ (Real.exp E * Real.exp (min 0 (w-F))) *
      (U*V*Real.exp (-(1-η)*w)) := hc
    _ = U*V*Real.exp (-(1-η)*w+min 0 (w-F)+E) := by
      simp only [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hU hV)
      apply Real.exp_le_exp.mpr
      linarith [entropy_angle_tradeoff hη hη' (F:=F) (w:=w)]

end SignedSweeps
end

end OAI
