import OAI.Probability.SignedSweeps.BlockAngle

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma block_stabilizer_trace_exp_all {J : Type*} [Fintype J]
    {p t q R : ℕ} {k : J → ℕ}
    (e : (Σ j, Fin (k j)) ≃ Fin p) (a : ∀ j, PairType (k j))
    (hk : ∀ j, k j ≤ t) (i : ∀ j, Fin (k j) ↪ Fin t)
    (f : J → SymmetricGroup t → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (η : ℝ) (G : J → ℝ)
    (hamb : ∀ j, (a j).height ≤ q → ∀ (lam : Partition t) (c : Partition (t-k j)),
      SignedOccurrence ((a j).extended_size_eq (hk j)) (a j).2.1 (a j).2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*(a j).entropy+G j))
    (hR : 2*t+2*q+1 ≤ R) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (blockTypeProjection e a * coefficientAction (signedWordRepresentation p (Fin q))
        (coefficientPush (blockPermutation e)
          (productCoefficient (fun j g => f j (g.viaEmbedding (i j))))))).re ≤
      (∏ j, ((k j).factorial : ℝ)/t.factorial) *
        Real.exp ((η-1)*blockEntropy a+(∑ j, G j)+
          (Fintype.card J : ℝ)*localTraceError t q R) := by
  by_cases ha : ∀ j, (a j).height ≤ q
  · exact block_stabilizer_trace_exp e a hk ha i f hf η G
      (fun j => hamb j (ha j)) hR
  · push Not at ha
    obtain ⟨j,hj⟩ := ha
    rw [blockTypeProjection_zero_of_height e a j (by simpa only [Fintype.card_fin] using hj)]
    simp only [zero_mul, map_zero, Complex.zero_re]
    positivity

def typedLineError (t q R : ℕ) : ℝ :=
  localTraceError t q R + (4*(Nat.sqrt t : ℝ)+1)*Real.log R + 2*(q:ℝ)^2*Real.log R

lemma occupied_positive_block_trace_exp {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q p l n s m R : ℕ} (hq : 0 < q)
    (hn : p+l=n) (e : Fin n ≃ A × B) (z : MarkedAssignment l n)
    {kH : B → ℕ} {kK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin p)
    (hHroute : ∀ x, (eH.symm x).1 = (e (markedInjection hn z x)).2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin p)
    (hKroute : ∀ x, (eK.symm x).1 = (e (markedInjection hn z x)).1)
    (hkH : ∀ j, kH j ≤ s) (hkK : ∀ i, kK i ≤ m)
    (iH : ∀ j, Fin (kH j) ↪ Fin s) (iK : ∀ i, Fin (kK i) ↪ Fin m)
    (f : B → SymmetricGroup s → ℂ) (g : A → SymmetricGroup m → ℂ)
    (hf : ∀ j, (coefficientAction finiteRegularRepresentation (f j)).IsPositive)
    (hg : ∀ i, (coefficientAction finiteRegularRepresentation (g i)).IsPositive)
    (X Y : WordSpace p (Fin q ⊕ Fin q) →ₗ[ℂ] WordSpace p (Fin q ⊕ Fin q))
    (hX : X = coefficientAction (signedWordRepresentation p (Fin q))
      (coefficientPush (blockPermutation eH)
        (productCoefficient (fun j a => f j (a.viaEmbedding (iH j))))))
    (hY : Y = coefficientAction (signedWordRepresentation p (Fin q))
      (coefficientPush (blockPermutation eK)
        (productCoefficient (fun i a => g i (a.viaEmbedding (iK i))))))
    (hXp : X.IsPositive) (hYp : Y.IsPositive)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (GH : B → ℝ) (GK : A → ℝ)
    (hambH : ∀ j (a : PairType (kH j)), a.height ≤ q →
      ∀ (lam : Partition s) (c : Partition (s-kH j)),
      SignedOccurrence (a.extended_size_eq (hkH j)) a.2.1 a.2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (f j))).re ≤
          Real.exp (η*a.entropy+GH j))
    (hambK : ∀ i (a : PairType (kK i)), a.height ≤ q →
      ∀ (lam : Partition m) (c : Partition (m-kK i)),
      SignedOccurrence (a.extended_size_eq (hkK i)) a.2.1 a.2.2 c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) (g i))).re ≤
          Real.exp (η*a.entropy+GK i))
    (hR : 2*max s m+2*q+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h a b (Fin q) * X * Y)).re ≤
      (∏ j, ((kH j).factorial : ℝ)/s.factorial) *
      (∏ i, ((kK i).factorial : ℝ)/m.factorial) *
      Real.exp ((η-1)*signedEntropy a b+(∑ j, GH j)+(∑ i, GK i)+l+
        (Fintype.card B : ℝ)*typedLineError s q R+
        (Fintype.card A : ℝ)*typedLineError m q R) := by
  let PH : ℝ := ∏ j, ((kH j).factorial : ℝ)/s.factorial
  let PK : ℝ := ∏ i, ((kK i).factorial : ℝ)/m.factorial
  let U := PH * Real.exp ((∑ j, GH j)+(Fintype.card B : ℝ)*localTraceError s q R)
  let V := PK * Real.exp ((∑ i, GK i)+(Fintype.card A : ℝ)*localTraceError m q R)
  let E := (l:ℝ)+((Fintype.card A : ℝ)+Fintype.card B)*(2*(q:ℝ)^2*Real.log R)
  have hU : 0 ≤ U := by dsimp [U, PH]; positivity
  have hV : 0 ≤ V := by dsimp [V, PK]; positivity
  have hlog : 0 ≤ Real.log (R:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAX (H : ∀ j, PairType (kH j)) : blockTypeProjection (C:=Fin q) eH H * X =
      X * blockTypeProjection eH H := by rw [hX]; exact blockTypeProjection_coefficient_commute _ _ _
  have hBY (K : ∀ i, PairType (kK i)) : blockTypeProjection (C:=Fin q) eK K * Y =
      Y * blockTypeProjection eK K := by rw [hY]; exact blockTypeProjection_coefficient_commute _ _ _
  have hPX : pairTypeProjection h a b (Fin q)*X = X*pairTypeProjection h a b (Fin q) := by
    rw [hX]; exact pairTypeProjection_coefficient_commute _ _ _ _
  have hPY : pairTypeProjection h a b (Fin q)*Y = Y*pairTypeProjection h a b (Fin q) := by
    rw [hY]; exact pairTypeProjection_coefficient_commute _ _ _ _
  have ht := positive_trace_type_resolution_bound (pairTypeProjection h a b (Fin q)) X Y
    (blockTypeProjection eH) (blockTypeProjection eK)
    (blockTypeProjection_sum eH) (blockTypeProjection_sum eK) hXp hYp
    (pairTypeProjection_positive _ _ _ _) (pairTypeProjection_idempotent _ _ _ _)
    (blockTypeProjection_positive eH) (blockTypeProjection_positive eK)
    (blockTypeProjection_idempotent eH) (blockTypeProjection_idempotent eK)
    (fun H => (blockTypeProjection_global_commute eH H h a b).symm)
    (fun K => (blockTypeProjection_global_commute eK K h a b).symm) hPX hPY hAX hBY
  apply ht.trans
  have hterm (H : ∀ j, PairType (kH j)) (K : ∀ i, PairType (kK i)) :
      ‖(blockTypeProjection (C:=Fin q) eH H * blockTypeProjection eK K *
        pairTypeProjection h a b (Fin q)).toContinuousLinearMap‖^2 *
      (LinearMap.trace ℂ _ (blockTypeProjection eH H * X)).re *
      (LinearMap.trace ℂ _ (blockTypeProjection eK K * Y)).re ≤
        U*V*Real.exp (-(1-η)*signedEntropy a b+E) := by
    have hx := positive_commuting_projection X (blockTypeProjection eH H) hXp
      (blockTypeProjection_positive _ _).isSymmetric (blockTypeProjection_idempotent _ _) (hAX H)
    have hy := positive_commuting_projection Y (blockTypeProjection eK K) hYp
      (blockTypeProjection_positive _ _).isSymmetric (blockTypeProjection_idempotent _ _) (hBY K)
    have hx0 := Complex.re_le_re hx.trace_nonneg
    have hy0 := Complex.re_le_re hy.trace_nonneg
    have htx : (LinearMap.trace ℂ _ (blockTypeProjection eH H * X)).re ≤
        PH*Real.exp ((η-1)*blockEntropy H+(∑ j, GH j)+(Fintype.card B:ℝ)*localTraceError s q R) := by
      rw [hX]
      exact block_stabilizer_trace_exp_all eH H hkH iH f hf η GH (fun j => hambH j (H j)) (by omega)
    have hty : (LinearMap.trace ℂ _ (blockTypeProjection eK K * Y)).re ≤
        PK*Real.exp ((η-1)*blockEntropy K+(∑ i, GK i)+(Fintype.card A:ℝ)*localTraceError m q R) := by
      rw [hY]
      exact block_stabilizer_trace_exp_all eK K hkK iK g hg η GK (fun i => hambK i (K i)) (by omega)
    apply angle_trace_exp_tradeoff (w:=blockEntropy H+blockEntropy K) hη hη' hE hU hV (sq_nonneg _) hx0 hy0
      (by simpa only [E, add_assoc] using
        (occupied_block_type_angle_exp_all (s:=s) (m:=m) (R:=R) hq hn e z eH hHroute eK hKroute H K hkH hkK
        (by omega) h a b ha hb))
    calc
      _ ≤ (PH*Real.exp ((η-1)*blockEntropy H+(∑ j, GH j)+(Fintype.card B:ℝ)*localTraceError s q R)) *
          (PK*Real.exp ((η-1)*blockEntropy K+(∑ i, GK i)+(Fintype.card A:ℝ)*localTraceError m q R)) :=
        mul_le_mul htx hty hy0 (by dsimp [PH]; positivity)
      _ = _ := by
        dsimp [U,V]
        rw [show -(1-η)*(blockEntropy H+blockEntropy K) =
          (η-1)*blockEntropy H+(η-1)*blockEntropy K by ring]
        simp only [Real.exp_add]
        ring
  calc
    _ ≤ ∑ _H : ∀ j, PairType (kH j), ∑ _K : ∀ i, PairType (kK i),
        U*V*Real.exp (-(1-η)*signedEntropy a b+E) :=
      Finset.sum_le_sum (fun H _ => Finset.sum_le_sum (fun K _ => hterm H K))
    _ = ((Fintype.card (∀ j, PairType (kH j)) : ℝ) * (Fintype.card (∀ i, PairType (kK i)) : ℝ)) *
        (U*V*Real.exp (-(1-η)*signedEntropy a b+E)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Real.exp ((Fintype.card B : ℝ)*((4*(Nat.sqrt s:ℝ)+1)*Real.log R)) *
        Real.exp ((Fintype.card A : ℝ)*((4*(Nat.sqrt m:ℝ)+1)*Real.log R))) *
        (U*V*Real.exp (-(1-η)*signedEntropy a b+E)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (blockTypeCount_le_exp hkH (by omega)) (blockTypeCount_le_exp hkK (by omega))
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      dsimp [U,V,E,PH,PK,typedLineError]
      rw [show -(1-η)*signedEntropy a b = (η-1)*signedEntropy a b by ring]
      simp only [add_mul, mul_add, Real.exp_add]
      ring

end SignedSweeps
end

end OAI
