import OAI.NumberTheory.Ostmann.Construction.InitialEtaStateIndex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta
open InitialCoordinatesTemplate

abbrev RawSample (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) :=
  ((Bool × Fin s) → spectator.Sample) ×
    (giant.Sample × giant.Sample ×
      ((q : SmallShape b k) → (tupleSource giant bulk spectator aux b s (smallPosition q)).Sample))

def rawEquiv (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) :
    JointSample giant bulk spectator aux b s ≃ RawSample (b:=b) (s:=s) giant bulk spectator aux where
  toFun x := (fun i => (halfAt x i.1).2.2.1 i.2,x.1.1,x.2.1,
    fun q => tupleSample x (smallPosition q))
  invFun x :=
    ((x.2.1,(fun i => x.2.2.2 (.inl (false,i))),
      (fun i => x.1 (false,i)),
      (fun i => match i with
        | .inl j => x.2.2.2 (.inr (.inl (false,j)))
        | .inr (j,l) => x.2.2.2 (.inr (.inr (j,(false,l)))))),
     (x.2.2.1,(fun i => x.2.2.2 (.inl (true,i))),
      (fun i => x.1 (true,i)),
      (fun i => match i with
        | .inl j => x.2.2.2 (.inr (.inl (true,j)))
        | .inr (j,l) => x.2.2.2 (.inr (.inr (j,(true,l)))))))
  left_inv x := by
    apply Prod.ext
    all_goals
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      funext i
      rcases i with j | ⟨j,l⟩ <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      rcases i with ⟨h,i⟩
      cases h <;> rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    funext q
    rcases q with ⟨h,i⟩ | (⟨h,i⟩ | ⟨j,h,i⟩) <;> cases h <;> rfl

abbrev SourceSample (giant bulk spectator : PrimeSource) {k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource)
    (b s : ℕ) :=
  (Fin (2*s) → spectator.Sample) ×
    OuterSample (initialSources bulk aux b) (Template.initial (2*b) k) giant

def sourceEquiv (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) :
    JointSample giant bulk spectator aux b s ≃ SourceSample giant bulk spectator aux b s :=
  (rawEquiv giant bulk spectator aux).trans
    (Equiv.prodCongr (Equiv.piCongrLeft (fun _ => spectator.Sample) (halfEquiv s))
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr (Equiv.refl _) (smallAssignmentEquiv giant bulk spectator aux))))

@[simp] theorem sourceEquiv_spectator (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) (x : JointSample giant bulk spectator aux b s)
    (h : Bool) (i : Fin s) :
    (sourceEquiv giant bulk spectator aux x).1 (halfEquiv s (h,i)) = (halfAt x h).2.2.1 i := by
  change (Equiv.piCongrLeft (fun _ => spectator.Sample) (halfEquiv s)
    (fun i => (halfAt x i.1).2.2.1 i.2)) (halfEquiv s (h,i)) = _
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp] theorem sourceEquiv_small (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) (x : JointSample giant bulk spectator aux b s)
    (q : SmallShape b k) :
    ((sourceEquiv giant bulk spectator aux x).2.2.2 (smallIndex b k q) : ℕ) =
      tupleValues x (smallPosition q) := by
  change (smallAssignmentEquiv giant bulk spectator aux
    (fun q => tupleSample x (smallPosition q)) (smallIndex b k q) : ℕ) = _
  exact smallAssignmentEquiv_apply giant bulk spectator aux _ q

theorem sourceEquiv_mass (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) (x : JointSample giant bulk spectator aux b s) :
    ((spectatorPrior spectator (2*s)).pair
      (outerPrior (initialSources bulk aux b) (Template.initial (2*b) k) giant)).mass
      (sourceEquiv giant bulk spectator aux x) =
        (jointPrior giant bulk spectator aux b s).mass x := by
  have hspec : (spectatorPrior spectator (2*s)).mass
      (sourceEquiv giant bulk spectator aux x).1 =
      ∏h,∏i,spectator.law.mass ((halfAt x h).2.2.1 i) := by
    unfold spectatorPrior dependentProductPrior
    dsimp only
    rw [←(halfEquiv s).prod_comp]
    simp only [sourceEquiv_spectator,Fintype.prod_prod_type]
  change (spectatorPrior spectator (2*s)).mass _ *
    (giant.law.mass x.1.1 * (giant.law.mass x.2.1 *
      (assignmentPrior (initialSources bulk aux b) (Template.initial (2*b) k)).mass
        (smallAssignmentEquiv giant bulk spectator aux (fun q => tupleSample x (smallPosition q))))) = _
  rw [hspec,smallAssignmentEquiv_mass]
  simp only [jointPrior,halfListPrior,FinitePrior.pair,primeGroupPrior,dependentProductPrior,
    Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_bool,
    tupleSource,halfSource,smallPosition,tupleSample,halfSample,halfAt,Bool.false_eq_true,
    ite_false,ite_true]
  simp only [Finset.prod_mul_distrib]
  ring

theorem sourceEquiv_cmean (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) (f : SourceSample giant bulk spectator aux b s → ℂ) :
    (jointPrior giant bulk spectator aux b s).cmean (fun x => f (sourceEquiv giant bulk spectator aux x)) =
      (spectatorPrior spectator (2*s)).cmean (fun ds =>
        (outerPrior (initialSources bulk aux b) (Template.initial (2*b) k) giant).cmean
          (fun a => f (ds,a))) := by
  rw [←FinitePrior.pair_cmean]
  unfold FinitePrior.cmean
  simp_rw [←sourceEquiv_mass giant bulk spectator aux]
  exact (sourceEquiv giant bulk spectator aux).sum_comp (fun y =>
    (((spectatorPrior spectator (2*s)).pair
      (outerPrior (initialSources bulk aux b) (Template.initial (2*b) k) giant)).mass y:ℂ)*f y)

end Ostmann.Construction.InitialEta

end

end OAI
