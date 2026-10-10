import OAI.Combinatorics.PlanarL1.Movement

namespace OAI


section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory SecondaryGeometry FiniteRandom
open scoped NNReal
attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (x : M.Point Set.univ A.root) {ρ : ℝ} (hρ : 0 ≤ ρ)
variable (hp : Tiling.Padded a₁ q x.height ρ) (hn : Tiling.Padded a₂ p x.height ρ)
variable (a : Fin (SB.count+1)) (hold : A.Common SB.name x ρ a)
variable (hsmall : 18*ρ ≤ (199/1000:ℝ)*R) (hr : ρ ≤ secondaryRadius)
variable {m : ℕ} (hm : 0 < m)
noncomputable local instance : Fintype (Offsets (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m) := Fintype.ofFinite _
noncomputable local instance : Fintype (∀ i C, ComponentSample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) i C m) := Fintype.ofFinite _

include hρ hp hn hold hsmall hr hm

lemma persistence_fixed [SFinite ν]
    (o : Fin (SB.count+1) → Bool)
    (coins : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG) → Bool) :
    prob (fun w : Offsets (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m => ∃ z : Group.Ball x (ρ := ρ),
      (SecondaryGeometry.result (group A SA SB v hv) hm (flatSample (group A SA SB v hv) o coins w)).name z.val.column z.val.height≠
      (SecondaryGeometry.result (group A SA SB v hv) hm (flatSample (group A SA SB v hv) o coins w)).name x.column x.height) ≤
      (1+SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  have hBand (z : Group.Ball x (ρ := ρ)) : z.val.height∈(SB.chart a).band :=
    SB.height_named _ _ _ (hold z.val z.property)
  apply prob_bound_of_instances
  apply persistence_flat G o coins a x hBand hρ hm hsmall hr _
    (fun z => hold z.val z.property) _ (wholeBallSlots_card A SA SB v hv x o coins a hρ hp hn)
  · intro z
    have hb : ∀ H, |H-x.height|≤ρ → H∈(SB.chart a).band := by
      intro H hH
      exact SB.ball_band A hold (J := {T | |T-x.height|≤ρ})
        (fun T hT => by simpa only [Set.mem_ofPred_eq,abs_sub_comm] using hT) hH
    obtain ⟨hX,hZ,he⟩ := ((SB.chart a).comparison Group.lam Group.lam_bound (o a)).ball_variation x z.val hρ hb z.property
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hρ
    exact_mod_cast (le_max_left (5 : ℝ≥0) ⟨3/(9*a₂/100),by norm_num [a₂]⟩)
  · intro j ⟨z,hz⟩ H hH
    exact group_touched_envelope A SA SB v hv x hρ hn
      (coord G o coins (m := m) a j).1 (o a) (coord G o coins (m := m) a j).2
      z.property hz H hH

lemma persistence_probability [SFinite ν] :
    prob (fun omega : Sample (group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)) m =>
      ∃ z : Group.Ball x (ρ := ρ),
      (SecondaryGeometry.result (group A SA SB v hv) hm omega).name z.val.column z.val.height≠
      (SecondaryGeometry.result (group A SA SB v hv) hm omega).name x.column x.height) ≤
      (1+SurvivingGroups.packBound*secondaryN : ℕ)^2*secondaryTestLoss ρ m := by
  classical
  let G := group A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)
  apply prob_prod_bound_any
  intro o
  apply prob_prod_bound_any
  intro coins
  rw [←prob_equiv (Equiv.piCurry (fun i C => ComponentSample G i C m))]
  apply prob_bound_of_instances
  exact persistence_fixed A SA SB v hv x hρ hp hn a hold hsmall hr hm o coins
end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.Execution
variable {α : Type*}
lemma choose_upper (n : ℕ) (E : Fin (n+1) → Execution α) (P : α → Prop) {b : ℝ}
    (h : ∀ i, (E i).prob P ≤ b) : (Execution.choose n E).prob P ≤ b := by
  change (∑ i, (E i).prob P)/(n+1) ≤ b
  have hp : (0:ℝ)<n+1 := by positivity
  apply (div_le_iff₀ hp).mpr
  calc
    _  ≤  ∑ _ : Fin (n+1), b := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp; ring
end PlanarL1.Execution

namespace PlanarL1.Parameters
lemma mainLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ mainLoss ρ m := by
  unfold mainLoss mainTestLoss
  positivity [mainQ_pos,interpolationA.1]
lemma secondaryLoss_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) : 0 ≤ secondaryLoss ρ m :=
  mul_nonneg (sq_nonneg _) (secondaryTestLoss_nonneg hρ m)
noncomputable def persistenceLoss (ρ : ℝ) (m : ℕ) : ℝ :=
  heightLoss ρ m+(mainLoss ρ m+secondaryLoss ρ m)
end PlanarL1.Parameters

namespace PlanarL1.Columns.Model.CoupledState
open MeasureTheory Parameters SecondaryGeometry VertexBands VertexTests
open scoped NNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] FiniteRandom.prob
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {t : ℝ} (S : CoupledState A Ω Ξ μ ν t)

def Coherent (x : M.Point Set.univ A.root) (ρ : ℝ) : Prop :=
  ∀ z : M.Point Set.univ A.root, dist x z ≤ ρ →
    S.left.name z.column z.height=S.left.name x.column x.height ∧
    S.right.name z.column z.height=S.right.name x.column x.height

lemma Coherent.lift {x : M.Point Set.univ A.root} {ρ : ℝ} (h : S.Coherent x ρ) :
    S.lift.Coherent x ρ := h

variable (ht : 1 ≤ t) (hgap : 10 ≤ (R/200)*t)
variable [SFinite μ] [SFinite ν] [Fintype V]
variable (v : V → M.Point Set.univ A.root) {L U : ℝ}
variable (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q : ℝ} (phaseD : MainFamily.BandComponent (M := M) q L U → ℝ)
variable {m : ℕ} (hm : 0 < m) (p : ℝ) (phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)
variable (x : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ persistenceRadius) (hold : S.Coherent (v x) ρ)

omit [SFinite ν] [Fintype V] in
include hv hρ hr hold in
lemma main_persistence (hp : Tiling.Padded a₁ q (v x).height ρ) :
    FiniteRandom.prob (fun omega : MainFamily.Sample phaseD m =>
      ¬(S.main ht phaseD hm omega).Coherent (v x) ρ) ≤ mainLoss ρ m := by
  let c := mainCell A v hv phaseD x
  have hh := MainFamily.persistence_probability A S.left phaseD (v x) c
    (mainCell_mem A v hv phaseD x) hρ hp (persistence_main_small hr)
    (persistence_main_radius hr) (fun z hz => (hold z hz).1) m hm
  apply (FiniteRandom.prob_mono (Q := fun omega : MainFamily.Sample phaseD m =>
    ∃ z : M.Point Set.univ A.root, dist (v x) z ≤ ρ ∧
      (MainFamily.result A S.left phaseD hm omega).name z.column z.height≠
      (MainFamily.result A S.left phaseD hm omega).name (v x).column (v x).height) ?_).trans hh
  intro omega hb
  by_contra hn
  apply hb
  intro z hz
  exact ⟨not_ne_iff.mp (fun he => hn ⟨z,hz,he⟩),(hold z hz).2⟩

omit [SFinite μ] in
include hv hρ hr hold in
lemma secondary_persistence (hp : Tiling.Padded a₁ q (v x).height ρ)
    (hn : Tiling.Padded a₂ p (v x).height ρ) :
    FiniteRandom.prob (fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      ¬(S.secondary ht v hv phaseD hm p phaseG omega).Coherent (v x) ρ) ≤ secondaryLoss ρ m := by
  have hh := RetainedSelection.persistence_probability A S.left S.right v hv (phaseD := phaseD) (phaseG := phaseG) (v x) hρ hp hn
    (S.right.name (v x).column (v x).height) (fun z hz => (hold z hz).2)
    (persistence_secondary_small hr) (persistence_secondary_radius hr) hm
  apply (FiniteRandom.prob_mono (Q := fun omega : SecondaryGeometry.Sample (S.groups v hv phaseD p phaseG) m =>
      ∃ z : Group.Ball (v x) (ρ := ρ),
      (SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega).name z.val.column z.val.height≠
      (SecondaryGeometry.result (S.groups v hv phaseD p phaseG) hm omega).name (v x).column (v x).height) ?_).trans hh
  intro omega hb
  by_contra hn
  apply hb
  intro z hz
  exact ⟨(hold z hz).1,not_ne_iff.mp (fun he => hn ⟨⟨z,hz⟩,he⟩)⟩

include hv hρ hr hold in
lemma modes_persistence (hp : Tiling.Padded a₁ q (v x).height ρ)
    (hn : Tiling.Padded a₂ p (v x).height ρ) :
    (S.modes ht hgap v hv phaseD hm p phaseG).prob (fun z => ¬z.Coherent (v x) ρ) ≤ 
      mainLoss ρ m+secondaryLoss ρ m := by
  have hA := mainLoss_nonneg hρ m
  have hB := secondaryLoss_nonneg hρ m
  apply Execution.choose_upper
  intro i
  fin_cases i
  · change (Execution.pure (S.unchanged ht)).prob (fun z => ¬z.Coherent (v x) ρ) ≤ _
    have hg : (S.unchanged ht).Coherent (v x) ρ := hold
    simp only [Execution.prob_pure,hg,not_true_eq_false,ite_false]
    exact add_nonneg hA hB
  · change (Execution.uniform.bind (fun omega => .pure (S.main ht phaseD hm omega))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    exact (S.main_persistence ht v hv phaseD hm x hρ hr hold hp).trans (le_add_of_nonneg_right hB)
  · change (Execution.uniform.bind (fun omega => .pure (S.secondary ht v hv phaseD hm p phaseG omega))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    exact (S.secondary_persistence ht v hv phaseD hm p phaseG x hρ hr hold hp hn).trans (le_add_of_nonneg_left hA)
  · change (Execution.uniform.bind (fun sign => .pure (S.increment ht hgap sign))).prob
      (fun z => ¬z.Coherent (v x) ρ) ≤ _
    rw [Execution.prob_bind_pure,Execution.prob_uniform]
    have hh : ∀ sign, (S.increment ht hgap sign).Coherent (v x) ρ := fun _ => hold
    have he : (fun sign => ¬(S.increment ht hgap sign).Coherent (v x) ρ)=(fun _ => False) :=
      funext (fun sign => propext (iff_false_intro (not_not.mpr (hh sign))))
    rw [he,FiniteRandom.prob_false]
    exact add_nonneg hA hB

include hv hρ hr hold in
lemma step_persistence : (S.step ht hgap v hv hm).prob (fun z => ¬z.Coherent (v x) ρ) ≤ persistenceLoss ρ m := by
  apply VertexBands.conditional_persistence m hm (v x).height hρ
    (add_nonneg (mainLoss_nonneg hρ m) (secondaryLoss_nonneg hρ m))
  intro c hc
  exact S.modes_persistence ht hgap v hv (phase D c.2.1) hm (shift m a₂ c.1.2) (phase g c.2.2) x hρ hr hold hc.1 hc.2
end PlanarL1.Columns.Model.CoupledState

end



section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M} {q : ℝ} (hq : 0 < q)
namespace SetSystem
lemma dilate_separation (S : SetSystem M Ω μ) (i j : Fin (k+1)) (H T : ℝ) :
    (S.dilate hq).separation i (q*H) j (q*T)=q*S.separation i H j T := by
  simp only [separation,dilate,Activity.dilate_indicator,integral_smul_measure,
    smul_eq_mul,ENNReal.toReal_ofReal hq.le,mul_div_cancel_left₀ _ hq.ne']
end SetSystem
namespace PairGeometry
variable {SA : OrdinaryState M kappaA Ω μ} {v : V → M.Point Set.univ A.root}
variable {x y : V} {b : ℝ}
lemma Certificate.dilate (h : Certificate A SA v (x := x) (y := y) b) :
    Certificate (A.dilate hq) (SA.dilate hq) (fun x => A.scaleEquiv hq (v x))
      (x := x) (y := y) (q*b) := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  refine ⟨a,c,q*H,E,⟨H,hH,rfl⟩,hac,hsep,hE,?_,?_,?_,?_⟩
  · simpa only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq.le] using mul_le_mul_of_nonneg_left hm hq.le
  · intro w hw
    change (SA.sets.activity w).active (v x).column (q*(v x).height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hx w hw
  · intro w hw
    change (SA.sets.activity w).active (v y).column (q*(v y).height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hy w hw
  · intro w hw
    change ¬(SA.sets.activity w).active a (q*H/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hn w hw
end PairGeometry
namespace CoupledState
variable {t : ℝ} (S : CoupledState A Ω Ξ μ ν t) (v : V → M.Point Set.univ A.root)
lemma Successful.dilate {x y : V} {b : ℝ} (h : S.Successful v b x y) :
    (S.dilate hq).Successful (fun x => A.scaleEquiv hq (v x)) (q*b) x y := by
  rcases h with h|h|h
  · apply Or.inl
    change q*b ≤ (S.left.sets.dilate hq).separation _ (q*_) _ (q*_)
    rw [SetSystem.dilate_separation]
    exact mul_le_mul_of_nonneg_left h hq.le
  · apply Or.inr ∘ Or.inl
    change q*b ≤ (S.right.sets.dilate hq).separation _ (q*_) _ (q*_)
    rw [SetSystem.dilate_separation]
    exact mul_le_mul_of_nonneg_left h hq.le
  · exact Or.inr (Or.inr (h.dilate hq))
lemma coherent_dilate (x : M.Point Set.univ A.root) (ρ : ℝ) :
    (S.dilate hq).Coherent (A.scaleEquiv hq x) (q*ρ) ↔ S.Coherent x ρ := by
  constructor
  · intro h z hz
    have hh := h (A.scaleEquiv hq z) (by rw [A.scaleEquiv_dist]; exact mul_le_mul_of_nonneg_left hz hq.le)
    change S.left.name z.column (q*z.height/q)=S.left.name x.column (q*x.height/q) ∧
      S.right.name z.column (q*z.height/q)=S.right.name x.column (q*x.height/q) at hh
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hh
  · intro h z hz
    obtain ⟨z,rfl⟩ := (A.scaleEquiv hq).surjective z
    rw [A.scaleEquiv_dist] at hz
    have hh := h z (by nlinarith only [hz,hq])
    change S.left.name z.column (q*z.height/q)=S.left.name x.column (q*x.height/q) ∧
      S.right.name z.column (q*z.height/q)=S.right.name x.column (q*x.height/q)
    simpa only [mul_div_cancel_left₀ _ hq.ne'] using hh
end CoupledState
end PlanarL1.Columns.Model

end

end OAI
