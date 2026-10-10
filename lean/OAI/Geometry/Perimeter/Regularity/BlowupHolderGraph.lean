import OAI.Geometry.Perimeter.Regularity.SlabContraction
import OAI.Geometry.Perimeter.Regularity.InitialSlab
import OAI.Geometry.Perimeter.Regularity.HolderGraph

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem HasHalfspaceBlowup.exists_holder_graphs (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hp : p∈perimeterSupport E) (hbl : HasHalfspaceBlowup E p v) :
    ∃ η : ℝ, 0<η ∧ η≤1/2 ∧ ∀ ε : ℝ, 0<ε →
    ∃ r : ℝ, 0<r ∧ ∃ f : normalPlane v → ℝ,
      f 0=0 ∧ ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)) ∧
      (∀ y, ‖y‖<1/4 → |f y|<1/4 ∧
        (y:Euc n)+f y•v∈perimeterSupport (blownUpSet E p r) ∩ Metric.ball 0 1) ∧
      (∀ y z, ‖y‖<1/4 → ‖z‖<1/4 → |f y-f z|≤‖y-z‖) ∧
      (∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
        ((y:Euc n)+t•v∈perimeterSupport (blownUpSet E p r) ↔ t=f y)) ∧
      (∃ a : ℝ, 0<a ∧ a<1/4 ∧ FullSlab (blownUpSet E p r) v 8 a) ∧
      (∀ x∈Metric.ball (0:normalPlane v) (1/4), GeometricHolderAt η (fderiv ℝ f) x) ∧
      (∀ x∈Metric.ball (0:normalPlane v) (1/4), ‖fderiv ℝ f x‖<ε) := by
  let s : ℕ → ℝ := fun i ↦ 1/((i:ℝ)+1)
  have hs : ∀ i, 0<s i := fun i ↦ by dsimp [s]; positivity
  have hst : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hHmeas : MeasurableSet {x : Euc n | inner ℝ x v<0} :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hH := locally_minimizing_of_local_L1_limit (by omega : 0<n)
    (fun i ↦ locally_minimizing_blownUpSet hmin p (hs i)) hHmeas (hbl.local_L1 hmin.1 s hs hst)
  obtain ⟨q,M,δ,hq,hq64,hM,hδ,_,hstep⟩ := exists_slab_contraction hn hbl.1 hH
  refine ⟨q/2,by positivity,by linarith,?_⟩
  intro ε hε
  let b := min (δ/8) (min (1/8) (min (1/(64*(M+1))) (1/(4*(16*M+1/q+1)))))
  have hb : 0<b := lt_min (by positivity) (lt_min (by norm_num)
    (lt_min (by positivity) (by positivity)))
  let a := min b (ε/(32*(M+1)))
  have ha : 0<a := lt_min hb (by positivity)
  have hab : a≤b := min_le_left _ _
  have haε : 16*M*a<ε := by
    have hh : a≤ε/(32*(M+1)) := min_le_right _ _
    have hb' := (le_div_iff₀ (by positivity : 0<32*(M+1))).mp hh
    nlinarith
  have haδ : 4*a<δ := by
    have hh : a≤δ/8 := hab.trans (min_le_left _ _)
    linarith
  have ha4 : a<1/4 := by
    have hh : a≤1/8 := hab.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have haM : 8*M*a≤1/2 := by
    have haB : a≤1/(64*(M+1)) :=
      hab.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hh := (le_div_iff₀ (by positivity : 0<64*(M+1))).mp haB
    nlinarith
  have hachord : a*(16*M+1/q)≤1/2 := by
    have haB : a≤1/(4*(16*M+1/q+1)) :=
      hab.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (by positivity : 0<4*(16*M+1/q+1))).mp haB
    nlinarith
  obtain ⟨i,hi⟩ := (hbl.eventually_fullSlab hn hmin s hs hst ha (by linarith : a<1)).exists
  have hm := locally_minimizing_blownUpSet hmin p (hs i)
  obtain ⟨f,hf,hfs,hlip,hiff,hhold,hslope⟩ := holder_graph_from_contraction hn hq (by linarith : q<1)
    hM hstep hm hbl.1 ha haδ ha4 haM hachord hi
  have hzero : (0:Euc n)∈perimeterSupport (blownUpSet E p (s i)) := by
    rw [perimeterSupport_blownUpSet hmin.1 p (hs i)]
    simpa using hp
  have hf0 : f 0=0 := by
    have hh := (hiff 0 0 (by simp) (by simp)).mp (by simpa using hzero)
    exact hh.symm
  exact ⟨s i,hs i,f,hf0,hf,fun y hy ↦ ⟨((hfs y hy).1.trans_lt ha4),(hfs y hy).2⟩,hlip,hiff,⟨a,ha,ha4,hi⟩,hhold,fun x hx ↦ (hslope x hx).trans_lt haε⟩

end RPISingularHarnack

end

end OAI
