import OAI.Combinatorics.Ryser.Construction.AmbientDeletionProcess
import OAI.Combinatorics.Ryser.Construction.PoolThinProbability
import OAI.Combinatorics.Ryser.Selection.PoolLaw

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [instFintypeK : Fintype k] [Fintype F]
  [instDecidableEqK : DecidableEq k] [DecidableEq F]

abbrev AmbientPool (σ : k →+* F) (K : ℕ) := ConfigurationGroup σ → Fin K → Point F

def ambientPoolTrialEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ (Fin (ambientTrialCount σ K) → Point F) where
  toFun b t := b (ambientPosition σ K t).1 (ambientPosition σ K t).2
  invFun b i j := b ((Fintype.equivFin (AmbientPosition σ K)) (i, j))
  left_inv b := by
    funext i j
    simp only [ambientPosition, Equiv.symm_apply_apply]
  right_inv b := by
    funext t
    change b ((Fintype.equivFin (AmbientPosition σ K))
      ((Fintype.equivFin (AmbientPosition σ K)).symm t)) = b t
    exact congrArg b ((Fintype.equivFin (AmbientPosition σ K)).apply_symm_apply t)

def ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    AmbientPool σ K ≃ Selection.Pool F (Fintype.card (ConfigurationGroup σ)) K where
  toFun b p := b ((Fintype.equivFin (ConfigurationGroup σ)).symm p.1) p.2
  invFun b i j := b ((Fintype.equivFin (ConfigurationGroup σ)) i, j)
  left_inv b := by
    funext i j
    simp only [Equiv.symm_apply_apply]
  right_inv b := by
    funext p
    simp only [Equiv.apply_symm_apply, Prod.mk.eta]

theorem poolThinLaw_map_ambientFlatPoolEquiv (σ : k →+* F) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map (ambientFlatPoolEquiv σ K) =
      Selection.poolLaw F (Fintype.card (ConfigurationGroup σ)) K :=
  let _ := instFintypeK; let _ := instDecidableEqK; by
  rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
    Selection.poolLaw_eq_uniform]

def ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K) :
    Fin (ambientTrialCount σ K) →
      LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K) :=
  fun t => ambientTrialOutcome σ
    (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K
    (b (ambientPosition σ K t).1 (ambientPosition σ K t).2)

@[simp] theorem ambientPoolConfig_at (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) (b : AmbientPool σ K)
    (i : ConfigurationGroup σ) (j : Fin K) :
    ambientPoolConfig σ u v huv a ha K b
        ((Fintype.equivFin (AmbientPosition σ K)) (i, j)) =
      ambientTrialOutcome σ (groupPlacement σ u v huv i) a ha K (b i j) := by
  simp only [ambientPoolConfig, ambientPosition, Equiv.symm_apply_apply]

theorem poolThinLaw_map_ambientPoolConfig (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ) :
    (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
        (ambientPoolConfig σ u v huv a ha K) =
      FiniteLaw.pi (ambientTrials σ u v huv a ha K) := by
  let f : (Fin (ambientTrialCount σ K) → Point F) →
      (Fin (ambientTrialCount σ K) →
        LineCover.Outcome (ambientShapes F) (ambientDeletionConstant (Fintype.card k) K)) :=
    fun b t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K (b t)
  have hconfig : ambientPoolConfig σ u v huv a ha K = f ∘ ambientPoolTrialEquiv σ K := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (poolThinLaw (F := F) (ConfigurationGroup σ) K).map
      (ambientPoolTrialEquiv σ K) =
      FiniteLaw.pi (fun _ : Fin (ambientTrialCount σ K) => FiniteLaw.uniform (Point F)) := by
    rw [poolThinLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv, FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform (Point F))
    (fun t => ambientTrialOutcome σ
      (groupPlacement σ u v huv (ambientPosition σ K t).1) a ha K)

end RyserCoveringCounterexample.Construction

end

end OAI
