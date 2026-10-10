import OAI.Combinatorics.PlanarL1.StepSuccess

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {Ω Ξ V : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
variable {A : Ambient M}
namespace SetSystem
local instance : MeasurableSpace (Set (Fin (k+1))) := ⊤
variable [Fintype V] (S : SetSystem M Ω μ) (v : V → M.Point Set.univ A.root)
noncomputable def refinedBinary : FiniteL1.BinarySystem (V := V)
    (μ.prod (Measure.count : Measure (Set (Fin (k+1))))) where
  active w x := (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column
  measurable x := by
    have hm : Measurable (fun w : Ω × Set (Fin (k+1)) => (S.activity w.1).vector (v x).column (v x).height w.2) :=
      measurable_from_prod_countable_left (fun c => S.measurable_vector (v x).column (v x).height c)
    convert measurableSet_eq_fun hm (measurable_const : Measurable (fun _ : Ω × Set (Fin (k+1)) => (1:ℝ))) using 1
    ext w
    simp [Activity.vector]
  integrable x y := by
    convert (S.integrable_coordinateDifference (Classical.choice ((v x).paths_nonempty (v y))) (v x).height (v y).height).abs using 1
    funext w
    by_cases hx : (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column <;>
      by_cases hy : (S.activity w.1).active (v y).column (v y).height ∧ w.2=(S.activity w.1).component (v y).column <;>
      simp [SetSystem.coordinateDifference,Activity.vector,hx,hy]
noncomputable def cuts : FiniteL1.CutFamily V := FiniteL1.CutFamily.ofBinary (S.refinedBinary v)
variable [SFinite μ]
lemma cuts_distance (x y : V) :
    (S.cuts v).distance x y=∫ w, (S.activity w).cost (v x).column (v y).column (v x).height (v y).height ∂μ := by
  rw [cuts,FiniteL1.CutFamily.distance_ofBinary]
  rw [← S.integral_norm_coordinates (Classical.choice ((v x).paths_nonempty (v y))) (v x).height (v y).height]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  by_cases hx : (S.activity w.1).active (v x).column (v x).height ∧ w.2=(S.activity w.1).component (v x).column <;>
    by_cases hy : (S.activity w.1).active (v y).column (v y).height ∧ w.2=(S.activity w.1).component (v y).column <;>
    simp [Real.norm_eq_abs,SetSystem.coordinateDifference,Activity.vector,FiniteL1.BinarySystem.indicator,refinedBinary,hx,hy]
lemma cuts_upper (x y : V) : (S.cuts v).distance x y ≤ dist (v x) (v y) := by
  rw [S.cuts_distance]
  exact S.integral_cost_le_dist isClosed_univ _ _
lemma cuts_dominates (x y : V) : S.separation (v x).column (v x).height (v y).column (v y).height ≤ (S.cuts v).distance x y := by
  rw [S.cuts_distance,← S.norm_refinedMap_sub (v x)]
  exact S.refinedMap_dominates _ _ _
end SetSystem
namespace PairGeometry
variable [SFinite μ] [Fintype V] {SA : OrdinaryState M kappaA Ω μ}
variable {v : V → M.Point Set.univ A.root} {x y : V} {b : ℝ}
lemma Certificate.cuts (h : Certificate A SA v (x := x) (y := y) b) :
    b ≤ (SA.sets.cuts v).distance x y := by
  obtain ⟨a,c,H,E,hH,hac,hsep,hE,hm,hx,hy,hn⟩ := h
  rw [SA.sets.cuts_distance,← SA.sets.norm_refinedMap_sub (v x)]
  have bound {a c : Fin (k+1)} (hH : H ∈ M.heights a c) (hac : ¬Consecutive a c)
      (hsep : Field.TipSeparates a c (v x).column (v y).column)
      (hn : ∀ w ∈ E, ¬(SA.sets.activity w).active a H) :
      2*μ.real E ≤ ‖SA.sets.refinedMap (v x) (v x)-SA.sets.refinedMap (v x) (v y)‖ := by
    rcases hsep with ⟨h1,h2,hout⟩|⟨h1,h2,hout⟩
    · exact (SA.sets.refinedMap_terminal_certificate (v x) (v x) (v y) hH hac ⟨h1,h2⟩ hout E hE hn hx hy).2
    · simpa only [norm_sub_rev] using (SA.sets.refinedMap_terminal_certificate (v x) (v y) (v x) hH hac ⟨h1,h2⟩ hout E hE hn hy hx).2
  have hh : 2*μ.real E ≤ ‖SA.sets.refinedMap (v x) (v x)-SA.sets.refinedMap (v x) (v y)‖ := by
    rcases hsep with hsep|hsep
    · exact bound hH hac hsep hn
    · apply bound (M.symm a c ▸ hH) (fun h => hac (by simpa only [Consecutive,or_comm,or_left_comm,or_assoc] using h)) hsep
      intro w hw hwa
      exact hn w hw ((SA.sets.activity w).switch a c H hH |>.mpr hwa)
  linarith [measureReal_nonneg (μ := μ) (s := E)]
end PairGeometry
namespace CoupledState
variable [SFinite μ] [SFinite ν] [Fintype V]
variable {t : ℝ} (S : CoupledState A Ω Ξ μ ν t) (v : V → M.Point Set.univ A.root)
noncomputable def cuts : FiniteL1.CutFamily V := (S.left.sets.cuts v).add (S.right.sets.cuts v)
lemma cuts_upper (x y : V) : (S.cuts v).distance x y ≤ 2*dist (v x) (v y) := by
  rw [CoupledState.cuts,FiniteL1.CutFamily.distance_add]
  linarith [S.left.sets.cuts_upper v x y,S.right.sets.cuts_upper v x y]
lemma Successful.cuts {x y : V} {b : ℝ} (h : S.Successful v b x y) : b ≤ (S.cuts v).distance x y := by
  rw [CoupledState.cuts,FiniteL1.CutFamily.distance_add]
  rcases h with h|h|h
  · exact (h.trans (S.left.sets.cuts_dominates v x y)).trans (le_add_of_nonneg_right (FiniteL1.CutFamily.distance_nonneg _ _ _))
  · exact (h.trans (S.right.sets.cuts_dominates v x y)).trans (le_add_of_nonneg_left (FiniteL1.CutFamily.distance_nonneg _ _ _))
  · exact h.cuts.trans (le_add_of_nonneg_right (FiniteL1.CutFamily.distance_nonneg _ _ _))
end CoupledState
end PlanarL1.Columns.Model

end



section

namespace PlanarL1.Threshold
open MeasureTheory
instance labelMeasure_sfinite : SFinite labelMeasure := by
  rw [labelMeasure_eq]
  infer_instance
end PlanarL1.Threshold

namespace PlanarL1.Columns.Model
open MeasureTheory Parameters

/-- A state of the actual construction in its current physical units. Both
label spaces are enlarged at every step, even in the no-change mode. -/
structure World (k : ℕ) (V : Type*) (Q : ℝ) where
  model : Model (k+1)
  ambient : Ambient model
  vertex : V → model.Point Set.univ ambient.root
  sample : Type
  [measurable : MeasurableSpace sample]
  measure : Measure sample
  [sfinite : SFinite measure]
  state : CoupledState ambient sample sample measure measure Q

namespace World
attribute [instance] measurable sfinite
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (hQ : 0 < Q) (h1 : 1 ≤ Q) (hgap : 10 ≤ (R/200)*Q)
variable (W : World k V Q)
noncomputable def heightBound : ℝ := ∑ x, |(W.vertex x).height|
lemma height_bounds (x : V) : (W.vertex x).height ∈ Set.Icc (-W.heightBound) W.heightBound := by
  have hh : |(W.vertex x).height| ≤ W.heightBound :=
    Finset.single_le_sum (f := fun y => |(W.vertex y).height|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  exact abs_le.mp hh

noncomputable def after (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) : World k V Q where
  model := W.model.dilate Q hQ
  ambient := W.ambient.dilate hQ
  vertex x := W.ambient.scaleEquiv hQ (W.vertex x)
  sample := W.sample × Bool
  measure := ENNReal.ofReal Q • (W.measure.prod Threshold.fair)
  state := (T.dilate hQ).weaken (by simp)

noncomputable def step {m : ℕ} (hm : 0 < m) : Execution (World k V Q) :=
  (W.state.step h1 hgap W.vertex W.height_bounds hm).bind (fun T => .pure (W.after hQ T))

def Coherent (x : V) (ρ : ℝ) : Prop := W.state.Coherent (W.vertex x) ρ
def Successful (b : ℝ) (x y : V) : Prop := W.state.Successful W.vertex b x y
noncomputable def distance (x y : V) : ℝ := dist (W.vertex x) (W.vertex y)
noncomputable def cuts : FiniteL1.CutFamily V := W.state.cuts W.vertex
lemma cuts_upper (x y : V) : W.cuts.distance x y ≤ 2*W.distance x y := W.state.cuts_upper W.vertex x y
lemma Successful.cuts {b : ℝ} {x y : V} (h : W.Successful b x y) : b ≤ W.cuts.distance x y := CoupledState.Successful.cuts W.state W.vertex h
omit [Fintype V] in
lemma Successful.mono {b c : ℝ} {x y : V} (h : W.Successful b x y) (hc : c ≤ b) : W.Successful c x y := CoupledState.Successful.mono W.state W.vertex h hc

omit [Fintype V] in
lemma after_distance (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) (x y : V) :
    (W.after hQ T).distance x y=Q*W.distance x y := W.ambient.scaleEquiv_dist hQ _ _
omit [Fintype V] in
lemma after_coherent (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure)) (x : V) (ρ : ℝ) :
    (W.after hQ T).Coherent x (Q*ρ) ↔ T.Coherent (W.vertex x) ρ :=
  T.coherent_dilate hQ _ _
omit [Fintype V] in
lemma after_successful (T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure))
    {x y : V} {b : ℝ} (h : T.Successful W.vertex b x y) : (W.after hQ T).Successful (Q*b) x y := h.dilate hQ T W.vertex

lemma step_distances {m : ℕ} (hm : 0 < m) : (W.step hQ h1 hgap hm).Holds
    (fun Z => ∀ x y, Z.distance x y=Q*W.distance x y) := by
  apply Execution.holds_bind_of_forall
  intro T x y
  exact W.after_distance hQ T x y

lemma step_survives {m : ℕ} (hm : 0 < m) {x y : V} {b : ℝ} (h : W.Successful b x y) :
    (W.step hQ h1 hgap hm).Holds (fun Z => Z.Successful (Q*(b-3)) x y) := by
  apply (W.state.step_moves h1 hgap W.vertex W.height_bounds hm).bind
  intro T hT
  exact W.after_successful hQ T (by simpa only [mul_one] using hT.successful W.state (by norm_num) W.vertex h)

lemma step_persistence {m : ℕ} (hm : 0 < m) {x : V} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hr : ρ ≤ persistenceRadius) (hold : W.Coherent x ρ) :
    (W.step hQ h1 hgap hm).prob (fun Z => ¬Z.Coherent x (Q*ρ)) ≤ persistenceLoss ρ m := by
  rw [step,Execution.prob_bind_pure]
  have he : (fun T : CoupledState.Next (A := W.ambient) (μ := W.measure) (ν := W.measure) =>
      ¬(W.after hQ T).Coherent x (Q*ρ))=(fun T => ¬T.Coherent (W.vertex x) ρ) := by
    funext T
    exact propext (not_congr (W.after_coherent hQ T x ρ))
  rw [he]
  exact W.state.step_persistence h1 hgap W.vertex W.height_bounds hm x hρ hr hold

omit [Fintype V] in
lemma coherent_eligible {x y : V} (h : W.Coherent x 20) (hd : W.distance x y < 2) :
    VertexTests.Eligible W.ambient W.state.left W.state.right W.vertex x y := by
  refine ⟨?_,?_,?_,?_⟩
  · intro z hz
    exact (h z (hz.trans (by norm_num))).1
  · intro z hz
    have hxz : dist (W.vertex x) z ≤ 20 := by
      have ht := dist_triangle (W.vertex x) (W.vertex y) z
      change dist (W.vertex x) (W.vertex y)<2 at hd
      linarith
    exact (h z hxz).1
  · intro z hz
    exact (h z (hz.trans (by norm_num))).2
  · intro z hz
    have hxz : dist (W.vertex x) z ≤ 20 := by
      have ht := dist_triangle (W.vertex x) (W.vertex y) z
      change dist (W.vertex x) (W.vertex y)<2 at hd
      linarith
    exact (h z hxz).2

lemma step_success {m : ℕ} (hm : 0 < m) (hmany : 10000 ≤ m) {x y : V}
    (hc : W.Coherent x 20) (hlo : 1 ≤ W.distance x y) (hhi : W.distance x y < 2) :
    successChance ≤ (W.step hQ h1 hgap hm).prob (fun Z => Z.Successful (Q*successGain) x y) := by
  rw [step,Execution.prob_bind_pure]
  apply le_trans (W.state.step_success h1 hgap W.vertex W.height_bounds hm (W.coherent_eligible hc hhi) hlo hhi hmany)
  apply Execution.prob_mono
  intro T hT
  exact W.after_successful hQ T hT

noncomputable def initial {M : Model (k+1)} (A : Ambient M) (v : V → M.Point Set.univ A.root) : World k V Q where
  model := M
  ambient := A
  vertex := v
  sample := Bool × ℝ
  measure := Threshold.labelMeasure
  state := {
    left := OrdinaryState.initial M kappaA
    right := BState.initial M kappaB SecondaryGeometry.Group.lam
    histories := BState.Histories.ofOrdinary (A := A) (hc := by norm_num [R]) (hcr := by norm_num [R]) (OrdinaryState.initial M kappaB) }
omit [Fintype V] in
lemma initial_coherent {M : Model (k+1)} (A : Ambient M) (v : V → M.Point Set.univ A.root) (x : V) (ρ : ℝ) :
    (initial (Q := Q) A v).Coherent x ρ := by
  intro z hz
  exact ⟨rfl,rfl⟩
end World
end PlanarL1.Columns.Model

end

end OAI
