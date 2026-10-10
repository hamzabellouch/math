import OAI.Combinatorics.Ryser.Construction.GadgetShapes
import OAI.Combinatorics.Ryser.LineCover.Process
import OAI.Combinatorics.Ryser.LineCover.SurvivalNumerics
import OAI.Combinatorics.Ryser.Probability.ProductMap
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem nonzeroSlope_card (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    Fintype.card (NonzeroSlope k) = Fintype.card k - 1 := by
  change Fintype.card {d : k // ¬d = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

def cubicTrialLaw (d : NonzeroSlope k) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  (FiniteLaw.uniform k).map (cubicTrialOutcome d)

theorem cubicTrialLaw_point_probability
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) =
      1 / (Fintype.card k : ℝ) := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  simp only [deleted_empty_cubicTrialOutcome]
  rw [FiniteLaw.uniform_prob]
  have hfilter : @Finset.filter _ (fun z => x ∈ cubicShape d.val z)
      (fun z => Classical.propDecidable (x ∈ cubicShape d.val z)) Finset.univ =
      Finset.univ.filter (fun z => x ∈ cubicShape d.val z) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter, cubicShape_intercept_card hcop]
  simp

theorem cubicTrialLaw_point_probability_le
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (d : NonzeroSlope k) (x : Point k) :
    (cubicTrialLaw d).prob (fun a => x ∈ LineCover.deleted ∅ a) ≤
      (3 : ℝ) / Fintype.card k := by
  rw [cubicTrialLaw_point_probability hcop]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem cubicTrialLaw_line_probability_zero
    (hcard : 3 < Fintype.card k) (d : NonzeroSlope k) (l : AffineLine k) :
    (cubicTrialLaw d).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 := by
  rw [cubicTrialLaw, FiniteLaw.prob_map]
  have hevent : (fun z : k => ∃ S ∈ (cubicTrialOutcome d z).val,
      S.val = linePoints l) = (fun _ : k => False) := by
    funext z
    exact propext (iff_false_intro (cubicTrialOutcome_no_line d z hcard l))
  rw [hevent, FiniteLaw.prob_false]

def gadgetSlope (i : Fin (Fintype.card (NonzeroSlope k))) : NonzeroSlope k :=
  (Fintype.equivFin (NonzeroSlope k)).symm i

def gadgetTrials (i : Fin (Fintype.card (NonzeroSlope k))) :
    FiniteLaw (LineCover.Outcome (cubicShapes k) 3) :=
  cubicTrialLaw (gadgetSlope i)

def gadgetSurvival (k : Type*) [Field k] [Fintype k] : ℝ :=
  (1 - 1 / (Fintype.card k : ℝ)) ^ (Fintype.card k - 1)

theorem gadgetTrials_uniformSurvival
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (x : Point k) :
    (FiniteLaw.pi (gadgetTrials (k := k))).prob
      (fun a => x ∈ LineCover.survivors ∅ a) = gadgetSurvival k := by
  simp only [LineCover.mem_survivors]
  rw [FiniteLaw.prob_pi (gadgetTrials (k := k))
    (fun _ a => x ∉ LineCover.deleted ∅ a)]
  simp_rw [FiniteLaw.prob_compl]
  simp only [gadgetTrials, cubicTrialLaw_point_probability hcop]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nonzeroSlope_card, gadgetSurvival]

def gadgetDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) (δ : ℝ)
    (hδ : δ ≤ gadgetSurvival k) : LineCover.DeletionProcess k 3 δ where
  shapes := cubicShapes k
  shapeCount := cubicShapes_card_le k
  shapeSize := by
    intro S hS
    exact cubicShapes_member_card_le hS
  sparse := cubicShapes_sparse k
  trialsCount := Fintype.card (NonzeroSlope k)
  trials := gadgetTrials
  trialsCount_le := by rw [nonzeroSlope_card]; omega
  pointCap := fun i x => cubicTrialLaw_point_probability_le hcop (gadgetSlope i) x
  survival := gadgetSurvival k
  survivalLower := hδ
  uniformSurvival := gadgetTrials_uniformSurvival hcop
  lineCap := by
    intro l
    have hzero : ∀ i : Fin (Fintype.card (NonzeroSlope k)),
        (gadgetTrials i).prob (fun a => ∃ S ∈ a.val, S.val = linePoints l) = 0 :=
      fun i => cubicTrialLaw_line_probability_zero hcard (gadgetSlope i) l
    simp only [hzero, Finset.sum_const_zero]
    positivity

theorem gadgetDeletionProcess_trialsCount
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) (δ : ℝ) (hδ : δ ≤ gadgetSurvival k) :
    (gadgetDeletionProcess hcop hcard δ hδ).trialsCount = Fintype.card k - 1 :=
  nonzeroSlope_card k

def cubicDeletionProcess
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hcard : 3 < Fintype.card k) : LineCover.DeletionProcess k 3 (1 / 4 : ℝ) :=
  gadgetDeletionProcess hcop hcard (1 / 4)
    (LineCover.one_quarter_le_survival_pow_pred (Fintype.card k) (by omega))

def primeCubicDeletionProcess (p : ℕ) [Fact p.Prime]
    (hpmod : p % 3 = 2) (hp : 3 < p) :
    LineCover.DeletionProcess (ZMod p) 3 (1 / 4 : ℝ) :=
  cubicDeletionProcess (coprime_three_zmod_card_sub_one hpmod)
    (by simpa only [ZMod.card] using hp)

def gadgetLaw (k : Type*) [Field k] [Fintype k] [DecidableEq k] :
    FiniteLaw (GadgetOutcome k) :=
  FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)

def gadgetInterceptEquiv : GadgetOutcome k ≃
    (Fin (Fintype.card (NonzeroSlope k)) → k) where
  toFun a i := a (gadgetSlope i)
  invFun b d := b ((Fintype.equivFin (NonzeroSlope k)) d)
  left_inv a := by
    funext d
    simp only [gadgetSlope, Equiv.symm_apply_apply]
  right_inv b := by
    funext i
    simp only [gadgetSlope, Equiv.apply_symm_apply]

def gadgetConfig (a : GadgetOutcome k) :
    Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3 :=
  fun i => cubicTrialOutcome (gadgetSlope i) (a (gadgetSlope i))

theorem gadgetLaw_map_config :
    (gadgetLaw k).map gadgetConfig = FiniteLaw.pi (gadgetTrials (k := k)) := by
  let f : (Fin (Fintype.card (NonzeroSlope k)) → k) →
      (Fin (Fintype.card (NonzeroSlope k)) → LineCover.Outcome (cubicShapes k) 3) :=
    fun a i => cubicTrialOutcome (gadgetSlope i) (a i)
  have hconfig : gadgetConfig (k := k) = f ∘ gadgetInterceptEquiv := rfl
  rw [hconfig, ← FiniteLaw.map_map]
  have hreindex : (gadgetLaw k).map gadgetInterceptEquiv =
      FiniteLaw.pi (fun _ : Fin (Fintype.card (NonzeroSlope k)) =>
        FiniteLaw.uniform k) := by
    rw [gadgetLaw, FiniteLaw.pi_uniform, FiniteLaw.map_uniform_equiv,
      FiniteLaw.pi_uniform]
  rw [hreindex]
  exact FiniteLaw.map_pi (fun _ => FiniteLaw.uniform k)
    (fun i => cubicTrialOutcome (gadgetSlope i))

theorem gadgetConfig_survivors
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (a : GadgetOutcome k) :
    LineCover.survivors ∅ (gadgetConfig a) = transformedRetained a := by
  rw [transformedRetained_eq_survivors hcop]
  ext x
  have hright : x ∈ Finset.univ \ cubicDeletionUnion a ↔
      ∀ d : NonzeroSlope k, x ∉ cubicShape d.val (a d) := by
    simp [cubicDeletionUnion]
  rw [hright, LineCover.mem_survivors]
  simp only [gadgetConfig, deleted_empty_cubicTrialOutcome]
  constructor
  · intro h d
    simpa only [gadgetSlope, Equiv.symm_apply_apply] using
      h ((Fintype.equivFin (NonzeroSlope k)) d)
  · intro h i
    exact h (gadgetSlope i)

theorem gadgetLaw_transformedRetained_probability
    (hcop : Nat.Coprime 3 (Fintype.card k - 1)) (x : Point k) :
    (gadgetLaw k).prob (fun a => x ∈ transformedRetained a) = gadgetSurvival k := by
  have h := gadgetTrials_uniformSurvival hcop x
  rw [← gadgetLaw_map_config, FiniteLaw.prob_map] at h
  simpa only [gadgetConfig_survivors hcop] using h

end RyserCoveringCounterexample.Construction

end

end OAI
