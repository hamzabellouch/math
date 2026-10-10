import OAI.Combinatorics.PlanarL1.SelectedGain
import OAI.Combinatorics.PlanarL1.FamilyPersistence

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable def heightLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  (2*ρ+2*a₁/m)/a₁+(2*ρ+2*a₂/m)/a₂
lemma heightLoss_nonneg {ρ : ℝ} (hρ : 0≤ρ) (m : ℕ) : 0≤heightLoss ρ m := by
  unfold heightLoss
  apply add_nonneg
  · exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) hρ)
      (div_nonneg (mul_nonneg (by norm_num) interpolationA.2.1.le) (Nat.cast_nonneg m))) interpolationA.2.1.le
  · exact div_nonneg (add_nonneg (mul_nonneg (by norm_num) hρ)
      (div_nonneg (mul_nonneg (by norm_num) interpolationB.2.1.le) (Nat.cast_nonneg m))) interpolationB.2.1.le
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.VertexBands
open Parameters FiniteRandom
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {L U : ℝ}

def HeightPadded {m : ℕ} (c : Choices m L U M) (H ρ : ℝ) : Prop :=
  Tiling.Padded a₁ (shift m a₁ c.1.1) H ρ ∧
  Tiling.Padded a₂ (shift m a₂ c.1.2) H ρ

lemma height_padding_loss (m : ℕ) (hm : 0 < m) (H : ℝ) {ρ : ℝ} (hρ : 0≤ρ) :
    (geometricExecution m L U M).prob (fun c => ¬HeightPadded c H ρ)≤heightLoss ρ m := by
  let P := fun h : HeightChoices m => ¬Tiling.Padded a₁ (shift m a₁ h.1) H ρ
  let Q := fun h : HeightChoices m => ¬Tiling.Padded a₂ (shift m a₂ h.2) H ρ
  have hp : prob P≤(2*ρ+2*a₁/m)/a₁ := by
    apply prob_prod_bound_left
    intro j
    apply (prob_mono (Q := fun i => Tiling.NearBoundary a₁ (a₁/m*i.val) H ρ) ?_).trans
      (periodic_probability m hm interpolationA.2.1 hρ H)
    intro i hi
    by_contra hn
    exact hi (Tiling.padded_of_avoid interpolationA.2.1 hn)
  have hq : prob Q≤(2*ρ+2*a₂/m)/a₂ := by
    apply prob_prod_bound
    intro i
    apply (prob_mono (Q := fun j => Tiling.NearBoundary a₂ (a₂/m*j.val) H ρ) ?_).trans
      (periodic_probability m hm interpolationB.2.1 hρ H)
    intro j hj
    by_contra hn
    exact hj (Tiling.padded_of_avoid interpolationB.2.1 hn)
  have he : (geometricExecution m L U M).prob (fun c => ¬HeightPadded c H ρ)=
      prob (fun h : HeightChoices m => P h ∨ Q h) := by
    unfold geometricExecution
    rw [Execution.prob_bind]
    simp only [Execution.prob_bind_pure,HeightPadded,not_and_or]
    change Execution.uniform.mean (fun h : HeightChoices m =>
      Execution.uniform.prob (fun _ : RadialChoices m (shift m a₁ h.1) L U M => P h ∨ Q h))=_
    have hc (h : HeightChoices m) :
        Execution.uniform.prob (fun _ : RadialChoices m (shift m a₁ h.1) L U M => P h ∨ Q h)=
          if P h ∨ Q h then 1 else 0 := by
      by_cases hh : P h ∨ Q h <;> simp only [Execution.prob,hh,ite_true,ite_false,Execution.mean_const]
    simp_rw [hc]
    calc
      _ = Execution.uniform.prob (fun h : HeightChoices m => P h ∨ Q h) := by
        unfold Execution.prob
        congr 1
        funext h
        by_cases hh : P h ∨ Q h <;> simp [hh]
      _ = _ := Execution.prob_uniform _
  rw [he]
  exact (prob_or_le P Q).trans (add_le_add hp hq)

lemma conditional_persistence {β : Type*} (m : ℕ) (hm : 0 < m) (H : ℝ)
    {ρ b : ℝ} (hρ : 0≤ρ) (hb : 0≤b)
    (F : Choices m L U M → Execution β) (P : β → Prop)
    (hF : ∀ c, HeightPadded c H ρ → (F c).prob (fun z => ¬P z)≤b) :
    ((geometricExecution m L U M).bind F).prob (fun z => ¬P z)≤heightLoss ρ m+b :=
  (Execution.conditional_loss _ F (fun c => HeightPadded c H ρ) P hb hF).trans
    (add_le_add (height_padding_loss (M := M) (L := L) (U := U) m hm H hρ) le_rfl)
end PlanarL1.Columns.Model.VertexBands

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}

namespace SetSystem
lemma lift_separation (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    S.lift.separation i H j T=S.separation i H j T := by
  let hp := measurePreserving_fst (μ := μ) (ν := Threshold.fair)
  change (∫ z : Ω × Bool, |(S.activity z.1).indicator i H-(S.activity z.1).indicator j T| ∂μ.prod Threshold.fair)=_
  have he := integral_map_of_stronglyMeasurable (μ := μ.prod Threshold.fair) hp.measurable
    (((S.measurable_indicator i H).sub (S.measurable_indicator j T)).abs.stronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm
end SetSystem

namespace PairGeometry
variable {V : Type*} {A : Ambient M} {SA : OrdinaryState M kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b d : ℝ}
lemma Certificate.mono (h : Certificate A SA v (x := x) (y := y) b) (hdb : d≤b) :
    Certificate A SA v (x := x) (y := y) d := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  exact ⟨a,c,H,E,hH,hac,hsep,hE,hdb.trans hm,hx,hy,hn⟩
lemma Certificate.lift (h : Certificate A SA v (x := x) (y := y) b) :
    Certificate A SA.lift v (x := x) (y := y) b := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  refine ⟨a,c,H,Prod.fst ⁻¹' E,hH,hac,hsep,hE.preimage measurable_fst,?_,?_,?_,?_⟩
  · rw [(measurePreserving_fst (μ := μ) (ν := Threshold.fair)).measureReal_preimage hE.nullMeasurableSet]
    exact hm
  · intro z hz; exact hx z.1 hz
  · intro z hz; exact hy z.1 hz
  · intro z hz; exact hn z.1 hz
end PairGeometry

/-- The two literal cut/chart systems together with every B chart's recorded
increment history. The radius bound is an invariant, not a separation promise. -/
structure CoupledState (A : Ambient M) (Ω Ξ : Type*) [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (t : ℝ) where
  left : OrdinaryState M kappaA Ω μ
  right : BState M kappaB SecondaryGeometry.Group.lam Ξ ν
  histories : BState.Histories A (c := R/200) (by norm_num [R]) (by norm_num [R]) right t

namespace CoupledState
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
noncomputable def lift : CoupledState A (Ω × Bool) (Ξ × Bool)
    (μ.prod Threshold.fair) (ν.prod Threshold.fair) t where
  left := S.left.lift
  right := S.right.lift
  histories := S.histories.lift
noncomputable def weaken {s : ℝ} (h : s≤t) : CoupledState A Ω Ξ μ ν s where
  left := S.left
  right := S.right
  histories := S.histories.weaken h
noncomputable def dilate {q : ℝ} (hq : 0<q) :
    CoupledState (A.dilate hq) Ω Ξ (ENNReal.ofReal q • μ) (ENNReal.ofReal q • ν) (q*t) where
  left := S.left.dilate hq
  right := S.right.dilate hq
  histories := S.histories.dilate hq

variable {V : Type*} (v : V → M.Point Set.univ A.root)
def Successful (b : ℝ) (x y : V) : Prop :=
  b≤S.left.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
  b≤S.right.sets.separation (v x).column (v x).height (v y).column (v y).height ∨
  PairGeometry.Certificate A S.left v (x := x) (y := y) b
lemma Successful.mono {b d : ℝ} {x y : V} (h : S.Successful v b x y) (hdb : d≤b) :
    S.Successful v d x y := by
  rcases h with h|h|h
  · exact Or.inl (hdb.trans h)
  · exact Or.inr (Or.inl (hdb.trans h))
  · exact Or.inr (Or.inr (h.mono hdb))
lemma Successful.lift {b : ℝ} {x y : V} (h : S.Successful v b x y) : S.lift.Successful v b x y := by
  rcases h with h|h|h
  · exact Or.inl (by simpa only [CoupledState.lift,OrdinaryState.lift,SetSystem.lift_separation] using h)
  · exact Or.inr (Or.inl (by simpa only [CoupledState.lift,BState.lift,SetSystem.lift_separation] using h))
  · exact Or.inr (Or.inr h.lift)
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Execution
variable {α : Type*}
lemma choose_lower (n : ℕ) (E : Fin (n+1) → Execution α) (P : α → Prop) (i : Fin (n+1)) :
    (E i).prob P/(n+1) ≤ (Execution.choose n E).prob P := by
  change _ ≤ (∑ j, (E j).prob P)/(n+1)
  exact div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (E j).prob_nonneg P) (Finset.mem_univ i)) (by positivity)
lemma choose4_lower (E : Fin 4 → Execution α) (P : α → Prop) (i : Fin 4) :
    (E i).prob P/4 ≤ (Execution.choose 3 E).prob P := by
  convert choose_lower 3 E P i using 1
  norm_num
lemma prob_pure (x : α) (P : α → Prop) [Decidable (P x)] :
    (Execution.pure x).prob P=if P x then 1 else 0 := by
  classical
  by_cases h : P x <;> simp only [prob,mean,h,ite_true,ite_false]
lemma prob_pure_of (x : α) (P : α → Prop) (h : P x) : (Execution.pure x).prob P=1 := by
  classical
  simp only [prob_pure,h,ite_true]
end PlanarL1.Execution

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)
variable (ht : 1≤t) (hgap : 10≤(R/200)*t)

include hgap in
lemma cross (a : Fin (S.right.count+1)) (i : Fin ((S.histories.history a).count)) :
    10≤(R/200)*(S.histories.history a).radius i :=
  hgap.trans (mul_le_mul_of_nonneg_left (S.histories.older a i) (by norm_num [R]))

abbrev Next := CoupledState A (Ω × Bool) (Ξ × Bool)
    (μ.prod Threshold.fair) (ν.prod Threshold.fair) 1

noncomputable def unchanged : Next (A := A) (μ := μ) (ν := ν) := (S.weaken ht).lift

variable [SFinite μ] [SFinite ν]
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m)

noncomputable def main (omega : MainFamily.Sample phaseD m) : Next (A := A) (μ := μ) (ν := ν) where
  left := MainFamily.result A S.left phaseD hm omega
  right := S.right.lift
  histories := (S.histories.weaken ht).lift

variable [Fintype V] (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
noncomputable def groups := RetainedSelection.group A S.left S.right v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)

noncomputable def secondary (omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m) :
    Next (A := A) (μ := μ) (ν := ν) where
  left := S.left.lift
  right := SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega
  histories := BState.SecondaryLayer.histories A (by norm_num [R]) (by norm_num [R])
    (SecondaryGeometry.layer (S.groups v hv phaseD p phaseG) hm omega) (S.histories.weaken ht)

noncomputable def increment (sign : Fin (S.right.count+1) → Bool) : Next (A := A) (μ := μ) (ν := ν) where
  left := S.left.lift
  right := (IncrementStep.update A S.right S.histories.history (S.cross hgap) S.histories.recorded sign).lift
  histories := (S.histories.increment sign (by norm_num : (0:ℝ)<1) le_rfl ht (by simpa using S.cross hgap)
    verticalB.1 (by norm_num [kappaB,a₂]) Group.lam_bound
    (by change kappaB*lambda*10≤1/8; norm_num [kappaB,a₂,lambda,R])).lift

noncomputable def branches : Fin 4 → Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  ![.pure (S.unchanged ht),
    Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega)),
    Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega)),
    Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))]
noncomputable def modes : Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  .choose 3 (S.branches ht hgap v hv phaseD hm p phaseG)

noncomputable def step : Execution (Next (A := A) (μ := μ) (ν := ν)) :=
  (geometricExecution m L U M).bind (fun c =>
    S.modes ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2))

end PlanarL1.Columns.Model.CoupledState

end

end OAI
