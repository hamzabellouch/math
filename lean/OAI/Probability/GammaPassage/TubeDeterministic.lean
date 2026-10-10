import OAI.Probability.GammaPassage.Waypoints
import OAI.Probability.GammaPassage.FiniteWaypoints

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

def LocalTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) (w : Edge → ℝ) : Prop :=
  ∃ ds, p+displacement ds=q ∧ pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s ∧
    PathIn p ds (SegmentTube p q (δ*s))

theorem localTravel_of_waypoint_tests (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (α D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n)
    (hgood : ∀ j < B, GoodOrigin μ α C κ δ n
      (fun e => w (shiftEdge (waypoint p q B j) e))) :
    LocalTravel μ η δ n p q w := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    have ht := (hgood 0 hB).1 (e.1-p,e.2)
    simpa [waypoint_zero,shiftEdge] using ht
  have hμzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have hwhole : μ (latticeEmbed (q-p)) ≤ β*(D*n) := by
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q-p)) 0)
    simp only [hμzero,sub_zero] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hdist hβ)
  let a := μ (latticeEmbed (q-p))/(B : ℝ)+4*β+κ*n+1
  have hpiece (j : ℕ) (hj : j < B) : ∃ ds,
      waypoint p q B j+displacement ds=waypoint p q B (j+1) ∧
      pathCost w (waypoint p q B j) ds ≤ a ∧
      PathIn (waypoint p q B j) ds (SegmentTube p q (δ*n)) := by
    let x := waypoint p q B j
    let y := waypoint p q B (j+1)
    have hg := hgood j hj
    have hlength : ‖latticeEmbed (y-x)‖ ≤ (C : ℝ)*n := by
      have ht := waypoint_displacement_norm p q B j hB
      exact (ht.trans (add_le_add ((div_le_div_iff_of_pos_right hb).mpr hdist) le_rfl)).trans hshortdist
    have herror := (abs_le.mp (hg.2.1 (y-x) hlength)).2
    have hpassage : passageTime w x y ≤ μ (latticeEmbed (y-x))+κ*n := by
      have hxy : waypoint p q B j+(y-x)=y := by dsimp [x]; abel
      simp only [passageTime_translate,add_zero,hxy] at herror
      linarith
    have hstepμ := waypoint_cost_bound μ hμ β hβ hlip p q B j hB
    have hshort : passageTime w x y+1 ≤ α*δ*n/6 := by
      have hd := (div_le_div_iff_of_pos_right hb).mpr hwhole
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    have hescape (z : Vertex) (hz : δ*n/3 ≤ ‖latticeEmbed (z-x)‖) :
        α*δ*n/6 ≤ passageTime w x z := by
      have hxz : waypoint p q B j+(z-x)=z := by dsimp [x]; abel
      simpa only [passageTime_translate,add_zero,hxz] using hg.2.2 (z-x) hz
    obtain ⟨ds,hend,hcost,hlocal⟩ := exists_confined_near_optimal w hw x y
      (δ*n/3) (α*δ*n/6) 1 (by norm_num) hescape hshort
    refine ⟨ds,hend,?_,?_⟩
    · change pathCost w x ds ≤ a
      dsimp [a]
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    · intro i hi
      obtain ⟨t,ht0,ht1,hbound⟩ := waypoint_ball_in_tube p q B j hB hj.le
        (δ*n/3) (x+displacement (ds.take i)) (hlocal i hi).le
      exact ⟨t,ht0,ht1,hbound.trans htube⟩
  have hp : waypoint p q B 0 ∈ SegmentTube p q (δ*n) := by
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hn : 0 ≤ δ*n := by linarith
    simpa [segmentPoint] using hn
  obtain ⟨ds,hend,hcost,hlocal⟩ := exists_path_chain w (waypoint p q B)
    (SegmentTube p q (δ*n)) (fun _ => a) B hp hpiece
  refine ⟨ds,by simpa [waypoint_end p q B hB] using hend,?_,by simpa using hlocal⟩
  have hid : (B : ℝ)*a=μ (latticeEmbed (q-p))+(B : ℝ)*(4*β+κ*n+1) := by
    dsimp [a]
    field_simp; ring
  simp only [sum_const,card_range,nsmul_eq_mul] at hcost
  rw [hid] at hcost
  simpa only [waypoint_zero] using hcost.trans (add_le_add le_rfl htotal)

theorem localTravel_parameters (α β D η δ : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B C : ℕ, ∃ κ : ℝ, 0 < B ∧ 0 < C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop,
        D*n/(B : ℝ)+4 ≤ (C : ℝ)*n ∧
        β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6 ∧
        (B : ℝ)*(4*β+κ*n+1) ≤ η*n ∧ δ*n/3+2 ≤ δ*n := by
  have had : 0 < α*δ := mul_pos hα hδ
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (24*β*D/(α*δ)))
  have hb1 : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hb : 0 < B := by exact_mod_cast hbpos
  have hbchoose := (div_lt_iff₀ had).mp ((le_max_right _ _).trans_lt hB)
  have hbase : β*D/(B : ℝ) ≤ α*δ/24 :=
    (div_le_iff₀ hbpos).mpr (by nlinarith)
  obtain ⟨C,hC⟩ := exists_nat_gt (D+4)
  have hc : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  let κ := min (η/(4*(B : ℝ))) (α*δ/24)
  have hk : 0 < κ := lt_min (div_pos hη (by linarith)) (div_pos had (by norm_num))
  have hkcost : κ ≤ α*δ/24 := min_le_right _ _
  have hktotal : (B : ℝ)*κ ≤ η/4 := by
    have ht := (le_div_iff₀ (by linarith : 0 < 4*(B : ℝ))).mp (min_le_left _ _ : κ ≤ η/(4*(B : ℝ)))
    nlinarith
  refine ⟨B,C,κ,hb,hc,hk,?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (12*(4*β+1)/(α*δ))),
    hlim.eventually (eventually_ge_atTop (2*(B : ℝ)*(4*β+1)/η)),
    hlim.eventually (eventually_ge_atTop (3/δ))] with n hn hn1 hn2 hn3
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' := (div_le_iff₀ had).mp hn1
  have hn2' := (div_le_iff₀ hη).mp hn2
  have hn3' := (div_le_iff₀ hδ).mp hn3
  have hbase' := mul_le_mul_of_nonneg_right hbase hn0
  have hkcost' := mul_le_mul_of_nonneg_right hkcost hn0
  have hktotal' := mul_le_mul_of_nonneg_right hktotal hn0
  have hdiv : D*(n : ℝ)/(B : ℝ) ≤ D*n := by
    apply (div_le_iff₀ hbpos).mpr
    have ht := mul_le_mul_of_nonneg_left hb1.le (mul_nonneg hD.le hn0)
    simpa using ht
  have hc' := mul_le_mul_of_nonneg_right hC.le hn0
  have hid : β*(D*n)/(B : ℝ) = (β*D/(B : ℝ))*n := by ring
  rw [hid]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end GammaFPP.IntervalTravelBridge

end OAI
