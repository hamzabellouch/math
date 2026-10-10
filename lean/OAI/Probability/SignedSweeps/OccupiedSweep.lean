import OAI.Probability.SignedSweeps.HoleCount
import OAI.Probability.SignedSweeps.OccupiedTrace
import OAI.Probability.SignedSweeps.SweepCoefficients

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

@[simp] lemma columnEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((columnEnumeration a b).symm x).1 = (sweepBoard a b x).2 := rfl

@[simp] lemma rowEnumeration_symm_fst (a b : ℕ) (x : Fin (2^(a+b))) :
    ((rowEnumeration a b).symm x).1 = (sweepBoard a b x).1 := rfl

lemma factorial_ratio_eq_descFactorial_inv {k h t : ℕ} (hh : k+h=t) :
    (k.factorial : ℝ) / t.factorial = (t.descFactorial h : ℝ)⁻¹ := by
  have he : (k.factorial : ℝ) * (t.descFactorial h : ℝ) = t.factorial := by
    exact_mod_cast (by simpa only [show t-h=k by omega] using
      Nat.factorial_mul_descFactorial (show h ≤ t by omega))
  rw [← he, div_mul_cancel_left₀ (by positivity : (k.factorial : ℝ) ≠ 0)]

lemma sweepPowerCoefficient_positive_fintype (d r : ℕ) (left : Bool)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (sweepPowerCoefficient d r left)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact sweepPowerCoefficient_positive d r left

lemma columnPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (columnPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact columnPowerCoefficient_positive a b r

lemma rowPowerCoefficient_positive_fintype (a b r : ℕ)
    (I : Fintype (SymmetricGroup (2^(a+b)))) :
    letI := I
    (coefficientAction finiteRegularRepresentation (rowPowerCoefficient a b r)).IsPositive := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^(a+b))) (Fin (2^(a+b)))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact rowPowerCoefficient_positive a b r

lemma sweepPowerCoefficient_trace_fintype {d : ℕ} (lam : Partition (2^d)) (r : ℕ) (left : Bool)
    (I : Fintype (SymmetricGroup (2^d))) :
    letI := I
    LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam)
      (sweepPowerCoefficient d r left)) = LinearMap.trace ℂ (Specht lam) (sweepSquare lam^r) := by
  cases Subsingleton.elim I (@Equiv.instFintype (Fin (2^d)) (Fin (2^d))
    (Classical.decEq _) (Classical.decEq _) (Fin.fintype _) (Fin.fintype _))
  exact sweepPowerCoefficient_trace lam r left

lemma columnPowerCoefficient_eq_push (a b r : ℕ)
    (I : Fintype (Fin (2^b) → SymmetricGroup (2^a))) :
    columnPowerCoefficient a b r =
      @coefficientPush _ _ _ I _ (blockPermutation (columnEnumeration a b))
        (productCoefficient (fun _ => sweepPowerCoefficient a r true)) := by
  unfold columnPowerCoefficient
  apply congrArg (fun (T : Fintype (Fin (2^b) → SymmetricGroup (2^a))) =>
    @coefficientPush _ _ _ T _ (blockPermutation (columnEnumeration a b))
      (productCoefficient (fun _ => sweepPowerCoefficient a r true)))
  exact Subsingleton.elim _ _

lemma rowPowerCoefficient_eq_push (a b r : ℕ)
    (I : Fintype (Fin (2^a) → SymmetricGroup (2^b))) :
    rowPowerCoefficient a b r =
      @coefficientPush _ _ _ I _ (blockPermutation (rowEnumeration a b))
        (productCoefficient (fun _ => sweepPowerCoefficient b r false)) := by
  unfold rowPowerCoefficient
  apply congrArg (fun (T : Fintype (Fin (2^a) → SymmetricGroup (2^b))) =>
    @coefficientPush _ _ _ T _ (blockPermutation (rowEnumeration a b))
      (productCoefficient (fun _ => sweepPowerCoefficient b r false)))
  exact Subsingleton.elim _ _

lemma occupied_sweep_trace_bound {a b j q R p l : ℕ} (hq : 0 < q)
    (hn : p+l=2^(a+b)) (z : MarkedAssignment l (2^(a+b)))
    {η τ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    {u v : ℕ} (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h α β (Fin q) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => columnPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))) *
        coefficientAction (signedWordRepresentation p (Fin q))
          (fun g => rowPowerCoefficient a b (2^j) (g.viaEmbedding (markedInjection hn z))))).re ≤
      holePrefactor (markedBoardPlacement (sweepBoard a b) z) *
      Real.exp (holeBudget τ (markedBoardPlacement (sweepBoard a b) z).1+
        (η-1)*signedEntropy α β+l+(2^b : ℕ)*typedLineError (2^a) q R+
        (2^a : ℕ)*typedLineError (2^b) q R) := by

  let I := markedInjection hn z
  let EH := columnEnumeration a b
  let EK := rowEnumeration a b
  let kH := routeSize (freeRoute EH I)
  let kK := routeSize (freeRoute EK I)
  let eH := routeEnumeration (freeRoute EH I)
  let eK := routeEnumeration (freeRoute EK I)
  let Z := markedBoardPlacement (sweepBoard a b) z

  have hH (c : Fin (2^b)) : kH c+(occupancy (fun i => (Z.1 i).2) c).val=2^a := by
    simpa only [kH, I, EH, markedRoutes, columnEnumeration_symm_fst,
      routeSize_occupancy, Function.comp_def, Z, markedBoardPlacement_apply] using
      freeLineSize_add_marks hn z EH c

  have hK (c : Fin (2^a)) : kK c+(occupancy (fun i => (Z.1 i).1) c).val=2^b := by
    simpa only [kK, I, EK, markedRoutes, rowEnumeration_symm_fst,
      routeSize_occupancy, Function.comp_def, Z, markedBoardPlacement_apply] using
      freeLineSize_add_marks hn z EK c
  let X := coefficientAction (signedWordRepresentation p (Fin q))
      (fun g => columnPowerCoefficient a b (2^j) (g.viaEmbedding I))
  let Y := coefficientAction (signedWordRepresentation p (Fin q))
      (fun g => rowPowerCoefficient a b (2^j) (g.viaEmbedding I))

  have hb₀ := occupied_positive_block_trace_exp (s:=2^a) (m:=2^b) (R:=R) hq hn (sweepBoard a b) z
    eH (by
      intro x
      rw [routeEnumeration_symm_fst]
      rfl) eK (by
      intro x
      rw [routeEnumeration_symm_fst]
      rfl)
    (by exact freeLineSize_le EH I)
    (by exact freeLineSize_le EK I)
    (freeLineInjection EH I) (freeLineInjection EK I)

  have hb₁ := hb₀
    (fun _ => sweepPowerCoefficient a (2^j) true) (fun _ => sweepPowerCoefficient b (2^j) false)
    (by intro c; exact sweepPowerCoefficient_positive_fintype a (2^j) true _)
    (by intro c; exact sweepPowerCoefficient_positive_fintype b (2^j) false _)

  have hb₂ := hb₁ (η:=η) X Y
    (by
      dsimp only [X]
      rw [columnPowerCoefficient_eq_push a b (2^j)
        (@Pi.instFintype (Fin (2^b)) (fun _ => SymmetricGroup (2^a))
          (Classical.decEq _) (Fin.fintype _) (fun _ => inferInstance))]
      exact congrArg (coefficientAction (signedWordRepresentation p (Fin q)))
        (funext (block_coefficient_restriction eH EH I (freeLineInjection EH I)
          (freeLine_square EH I) (fun _ => sweepPowerCoefficient a (2^j) true))))
    (by
      dsimp only [Y]
      rw [rowPowerCoefficient_eq_push a b (2^j)
        (@Pi.instFintype (Fin (2^a)) (fun _ => SymmetricGroup (2^b))
          (Classical.decEq _) (Fin.fintype _) (fun _ => inferInstance))]
      exact congrArg (coefficientAction (signedWordRepresentation p (Fin q)))
        (funext (block_coefficient_restriction eK EK I (freeLineInjection EK I)
          (freeLine_square EK I) (fun _ => sweepPowerCoefficient b (2^j) false))))
    (by exact marked_coefficient_compression_positive hn _ (columnPowerCoefficient_positive_fintype a b (2^j) _) z)
    (by exact marked_coefficient_compression_positive hn _ (rowPowerCoefficient_positive_fintype a b (2^j) _) z)

  have hb₃ := hb₂ hη hη'
    (fun c => clippedBudget τ (2^a) (occupancy (fun i => (Z.1 i).2) c).val)
    (fun c => clippedBudget τ (2^b) (occupancy (fun i => (Z.1 i).1) c).val)
    (by
      intro c T _ lam γ ho
      rw [sweepPowerCoefficient_trace_fintype]
      change weightedMoment lam (2^j) ≤ _
      have hh : 2^a-routeSize (freeRoute EH I) c=(occupancy (fun i => (Z.1 i).2) c).val := by have := hH c; dsimp only [kH] at this; omega
      simpa only [hh, PairType.entropy] using HA lam _ _ _ _ T.2.1 T.2.2 γ ho)
    (by
      intro c T _ lam γ ho
      rw [sweepPowerCoefficient_trace_fintype]
      change weightedMoment lam (2^j) ≤ _
      have hh : 2^b-routeSize (freeRoute EK I) c=(occupancy (fun i => (Z.1 i).1) c).val := by have := hK c; dsimp only [kK] at this; omega
      simpa only [hh, PairType.entropy] using HB lam _ _ _ _ T.2.1 T.2.2 γ ho)

  have hb := hb₃ hR h α β hα hβ

  simp only [Fintype.card_fin] at hb
  convert hb using 1
  have hp : ((∏ c, ((kH c).factorial : ℝ)/((2^a).factorial : ℝ)) *
    ∏ c, ((kK c).factorial : ℝ)/((2^b).factorial : ℝ)) = holePrefactor Z := by
      unfold holePrefactor
      congr 1 <;> apply Finset.prod_congr rfl
      · intro c _; exact factorial_ratio_eq_descFactorial_inv (hH c)
      · intro c _; exact factorial_ratio_eq_descFactorial_inv (hK c)
  dsimp only [kH, kK] at hp
  rw [hp]
  congr 2
  unfold holeBudget
  ring

end SignedSweeps
end

end OAI
