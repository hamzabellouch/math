import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryDescriptor
import OAI.Probability.CriticalPercolation.Entropy.BinaryRaw
import OAI.Probability.CriticalPercolation.Entropy.MarkedEntropy

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

lemma scheduleWeight_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (n : ℕ) (b : Fin n → Bool) (i : Fin n)
    (ω : E → Prop) (m : Option E) : 0 ≤ scheduleWeight G order d x p w n b i ω m :=
  G.rawContact_nonneg order _ _ hp w h0 h1 _ ω m

lemma scheduleWeight_sum (n : ℕ) (b : Fin n → Bool) (i : Fin n) (ω : E → Prop) :
    (∑ m, scheduleWeight G order d x p w n b i ω m) =
      G.scheduledContact order
        (BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) i.val)
        (scheduledAnchor (E := E) d x n b i.val) p w
        (G.clusterObject ω (BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) i.val)) ω := by
  unfold scheduleWeight
  rw [G.rawContact_sum,scheduledTargets_anchors d x n b i.val i.isLt.le]

theorem scheduleWeight_exponential (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (n : ℕ) (b : Fin n → Bool) :
    expect w (fun ω => Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) ω)) ≤
      Real.exp (n*Real.log 4) := by
  let a := scheduledAnchor (E := E) d x n b
  let B := BondGraph.anchorSet {x 0,x d} a
  have he (ω : E → Prop) : logContactMass (scheduleWeight G order d x p w n b) ω =
      ∑ i ∈ Finset.range n, Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (B i)) ω)) := by
    unfold logContactMass
    simp only [scheduleWeight_sum]
    exact Fin.sum_univ_eq_sum_range (fun i => Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
      (G.clusterObject ω (B i)) ω))) n
  simp_rw [he]
  exact G.scheduled_contact_exponential order ho {x 0,x d} a B (fun _ => Set.Subset.refl _)
    hp w h0 h1 n (Finset.range n) (Finset.Subset.refl _)

lemma density_seed_le_rawProduct (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (n : ℕ) (h : History E n) (ω : E → Prop) :
    density G order d x p w (seed G w (x 0) (x d) s) n h ω ≤
      (prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n * rawProduct G order d x p w n h ω := by
  apply (density_le_rawProduct G order d x p w hd hp h0 h1 _
    (seed_nonneg G w _ _ s hδ) hc hc1 hconn n h ω).trans
  apply mul_le_mul_of_nonneg_right _ (rawProduct_nonneg G order d x p w hp h0 h1 n h ω)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hc.le) n)
  unfold seed
  split_ifs <;> simp only [mul_one,mul_zero,le_refl,inv_nonneg.mpr hδ.le]

noncomputable def constructionCost (c : ℝ) (s n : ℕ) (D : FixedDescriptor n) : ℝ :=
  Real.log ((prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n /
    descriptorMass G order d x p w s n D)

lemma exp_constructionCost (c : ℝ) (hc : 0<c) (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    Real.exp (constructionCost G order d x p w c s n D) =
      (prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n /
        descriptorMass G order d x p w s n D :=
  Real.exp_log (div_pos (mul_pos (inv_pos.mpr hδ) (pow_pos (inv_pos.mpr hc) n)) hD)

theorem conditionedMass_density_le (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      Real.exp (constructionCost G order d x p w c s n D) *
        FiniteProduct.density (QueryTree.bitWeight p) z.1 *
        ∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration z.1) (z.2 i) := by
  rw [exp_constructionCost G order d x p w c hc s n D hδ hD]
  have hμ : 0 ≤ FiniteProduct.density (QueryTree.bitWeight p) z.1 :=
    FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _
  unfold conditionedMass fixedMass
  dsimp only
  split_ifs
  · have hr := density_seed_le_rawProduct G order d x p w hd hp h0 h1 hc hc1 hconn s hδ n
      (fromWords n (fun j => (D j).1) z.2) (configuration z.1)
    erw [rawProduct_words] at hr
    unfold jointMass
    dsimp only
    calc
      _ ≤ (FiniteProduct.density (QueryTree.bitWeight p) z.1 *
          ((prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n *
            ∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration z.1) (z.2 i))) /
          descriptorMass G order d x p w s n D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hμ) hD.le
      _ = _ := by ring
  · rw [zero_div]
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le)
      (pow_nonneg (inv_nonneg.mpr hc.le) n)) hD.le) hμ)
      (Finset.prod_nonneg fun i _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)

lemma sum_configuration (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (f : Set E → ℝ) :
    (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω * f (configuration ω)) =
      expect w f := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  have he := expect_configuration w f
  rw [← hw] at he
  refine Eq.trans ?_ he
  unfold expect
  apply Finset.sum_congr
  · ext f; simp only [Finset.mem_univ]
  · intro f _; rfl

lemma scheduleWeight_exponential_bool (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (n : ℕ) (b : Fin n → Bool) :
    (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω *
      Real.exp (2*logContactMass (fun i ω => scheduleWeight G order d x p w n b i (configuration ω)) ω)) ≤
      Real.exp (n*Real.log 4) := by
  have he := sum_configuration p w h0 h1
    (fun ω => Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) ω))
  change (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω *
    Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) (configuration ω))) ≤ _
  rw [he]
  exact scheduleWeight_exponential G order d x p w ho hp h0 h1 n b

noncomputable section EntropyFinal
local instance classicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem conditioned_configuration_entropy (ho : LazyDFS.Exhaustive G order)
    (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let a := fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω)
    divergence (pushMass Prod.fst Q) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
        2*constructionCost G order d x p w c s n D+n*Real.log 4 ∧
      (∑ z, Q z * logContactMass a z.1) ≤ constructionCost G order d x p w c s n D+n*Real.log 4 := by
  exact contact_configuration_entropy
    (conditionedMass G order d x p w s n D)
    (conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD)
    (by
      have hz := conditionedMass_normalized G order d x p w s n D hD
      refine Eq.trans ?_ hz
      apply Finset.sum_congr
      · ext z; simp only [Finset.mem_univ]
      · intro z _; rfl)
    (FiniteProduct.density (QueryTree.bitWeight p))
    (fun ω => Finset.prod_pos (fun e _ => QueryTree.bitWeight_pos hp e (ω e)))
    (fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω))
    (fun i ω m => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m)
    (constructionCost G order d x p w c s n D) (n*Real.log 4)
    (conditionedMass_density_le G order d x p w hd hp h0 h1 hc hc1 hconn s n D hδ hD)
    (scheduleWeight_exponential_bool G order d x p w ho hp h0 h1 n _)

end EntropyFinal
end CriticalPercolation.BinaryLaw
end
end

end OAI
