import OAI.NumberTheory.DirichletL.Reflection.CanonicalPool
import OAI.NumberTheory.DirichletL.Descent.ActiveReflection

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem markedCompletedT_twist_congr_primary (Ψ Φ : Eis→*ℂ)
    (h : ∀ n : Eis, λ₀^2∣n-1 → Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT Ψ W X d=markedCompletedT Φ W X d := by
  unfold markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem actual_marked_row_fixed_factor {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ m f z) W X d=
      markedCompletedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X d :=
by
  apply markedCompletedT_twist_congr_primary
  intro n hn
  exact D.row_primary Ψ Q hmLam hm2 n hn

def freePrimeFamily (I Q : Ideal Eis) (hI : Supported I) : PrimeFamily (FreePrimeIndex I Q) where
  ideal P := P.val.val
  maximal _P := inferInstance
  good P := (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

def markedSumSlots {ι σ : Type*} [Fintype ι] [Fintype σ] : Finset (ι⊕σ) :=
  Finset.univ.filter (fun x => x.isRight)

lemma actual_sextic_power_congr (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP : λ₀∉P) (hQ : λ₀∉Q) (hPQ : P=Q) (j : ℕ) (n : Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic Q hQ^j) (Ideal.Quotient.mk Q n) := by
  subst Q
  rfl

lemma unmarked_sum_twist {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) (n : Eis) :
    unmarkedSexticTwist (G.sum S).generator (G.sum S).generator_good
      (Sum.elim j (fun _ => 0)) markedSumSlots n =
    ∏ i, (actualSextic (G.ideal i) (G.good i)^j i) (Ideal.Quotient.mk _ n) := by
  let : DecidableEq (ι⊕σ) := Classical.decEq _
  have hset : (Finset.univ : Finset (ι⊕σ))\markedSumSlots = Finset.univ.filter (fun x => x.isLeft) := by
    ext x
    cases x <;> simp [markedSumSlots]
  unfold unmarkedSexticTwist
  change (∏ i∈Finset.univ\markedSumSlots, _) = _
  rw [hset,Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isLeft_inl,Sum.isLeft_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,mul_one,Sum.elim_inl]
  apply Finset.prod_congr rfl
  intro i hi
  exact actual_sextic_power_congr _ _ ((G.sum S).generator_good (Sum.inl i)) (G.good i)
    ((G.sum S).generator_span (Sum.inl i)) (j i) n

theorem free_row_eq_joined_unmarked {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ) :
    freePrimeRow I hI Q =
      unmarkedSexticTwist ((freePrimeFamily I Q hI).sum S).generator
        ((freePrimeFamily I Q hI).sum S).generator_good
        (Sum.elim (fun P : FreePrimeIndex I Q => (UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
          (fun _ => 0)) markedSumSlots := by
  ext n
  rw [unmarked_sum_twist]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
